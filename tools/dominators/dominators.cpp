//===-- dominators.cpp - Incremental dominators playground  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SparseSet.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/raw_ostream.h"

#include <cctype>
#include <fstream>
#include <map>
#include <memory>
#include <queue>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

using namespace llvm;

static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input file>"),
                                      cl::init("-"));
static cl::opt<bool> ViewCFG("view-cfg", cl::desc("View CFG"));

using Node = BasicBlock *;
using Index = unsigned;
static constexpr Index UndefIndex = static_cast<Index>(-1);

struct NodeByName {
  bool operator()(const Node first, const Node second) const {
    const auto Cmp = first->getName().compare_numeric(second->getName());
    if (Cmp == 0)
      return less{}(first, second);

    return Cmp < 0;
  }
};

class NewDomTree {
public:
  NewDomTree(Node Root) : root(Root) { computeReachableDominators(root, 0); }

  bool contains(Node N) const;
  Node getIDom(Node N) const;
  Index getLevel(Node N) const;
  Node findNCA(Node First, Node Second) const;

  void insertArc(Node From, Node To);
  void deleteArc(Node From, Node To);

  bool verifyAll() const;
  bool verifyWithOldDT() const;
  bool verifyNCA() const;
  bool verifyLevels() const;

  void print(raw_ostream &OS) const;
  void dump() const { print(dbgs()); }
  void dumpLevels(raw_ostream &OS = dbgs()) const;
  void addDebugInfoToIR();
  void viewCFG() const { root->getParent()->viewCFG(); }
  void dumpLegacyDomTree(raw_ostream &OS = dbgs()) const {
    DominatorTree DT(*root->getParent());
    DT.print(OS);
  }

private:
  Node root;
  DenseMap<Node, Node> idoms;
  DenseMap<Node, Node> sdoms;
  DenseMap<Node, Index> levels;
  DenseMap<Node, Node> preorderParents;
  DenseMap<Node, Node> sdomPathPredecessors;
  DenseMap<Node, Index> descendantsNum; // FIXME: Compute it.

  void computeReachableDominators(Node Root, Index MinLevel);
  void computeUnreachableDominators(
      Node Root, Node Incoming,
      SmallVectorImpl<std::pair<Node, Node>> &DiscoveredConnectingArcs);

  struct DFSResult {
    Index nextDFSNum = 0;
    DenseMap<Node, Index> nodeToNum;
    DenseMap<Index, Node> numToNode;
    DenseMap<Node, Node> parent;

    void dumpDFSNumbering(raw_ostream &OS = dbgs()) const;
  };

  template <typename DescendCondition>
  static DFSResult runDFS(Node Start, DescendCondition Condition);

  void semiNCA(DFSResult &DFS, Node Root, Index MinLevel, Index RootLevel = 0);

  struct InsertionInfo {
    using BucketElementTy = std::pair<Index, Node>;
    struct DecreasingLevel {
      bool operator()(const BucketElementTy &First,
                      const BucketElementTy &Second) const {
        return First.first > Second.first;
      }
    };

    std::priority_queue<BucketElementTy, SmallVector<BucketElementTy, 8>,
                        DecreasingLevel>
        bucket;
    DenseSet<Node> affected;
    DenseSet<Node> visited;
    SmallVector<Node, 8> affectedQueue;
    SmallVector<Node, 8> visitedNotAffectedQueue;
  };

  Node getSDomCandidate(Node Start, Node Pred, DFSResult &DFS,
                        DenseMap<Node, Node> &Labels);

  void insertUnreachable(Node From, Node To);
  void insertReachable(Node From, Node To);
  void visitInsertion(Node N, Index RootLevel, Node NCA, InsertionInfo &II);
  void updateInsertion(Node NCA, InsertionInfo &II);
  void updateLevels(InsertionInfo &II);

  bool isReachableFromIDom(Node N);
  void deleteReachable(Node From, Node To);
  void deleteUnreachable(Node From, Node To);

  using ChildrenTy = DenseMap<Node, SmallVector<Node, 8>>;
  void printImpl(raw_ostream &OS, Node N, const ChildrenTy &Children,
                 std::set<Node, NodeByName> &ToPrint) const;
};

template <typename DescendCondition>
NewDomTree::DFSResult NewDomTree::runDFS(Node Start,
                                         DescendCondition Condition) {
  DFSResult Res;
  Res.nextDFSNum = 0;
  DenseSet<Node> Visited;
  std::vector<Node> WorkList;

  Res.parent[Start] = nullptr;
  WorkList.push_back(Start);

  // Compute preorder numbers nad parents.
  while (!WorkList.empty()) {
    BasicBlock *BB = WorkList.back();
    WorkList.pop_back();
    if (Visited.count(BB) != 0)
      continue;

    Res.nodeToNum[BB] = Res.nextDFSNum;
    Res.numToNode[Res.nextDFSNum] = BB;
    ++Res.nextDFSNum;
    Visited.insert(BB);

    for (auto *Succ : reverse(successors(BB)))
      if (Visited.count(Succ) == 0)
        if (Condition(BB, Succ)) {
          WorkList.push_back(Succ);
          Res.parent[Succ] = BB;
        }
  }

  return Res;
}

void NewDomTree::semiNCA(DFSResult &DFS, Node Root, const Index MinLevel,
                         const Index RootLevel /* = 0 */) {
  // assert(DFS.nodeToNum.count(Root) != 0);
  assert(DFS.nextDFSNum > 0 && "DFS not run?");
  DenseMap<Node, Node> Label;
  const Index LastNum = DFS.nextDFSNum - 1;
  dbgs() << "StartNum: " << 0 << ": " << Root->getName() << "\n";
  dbgs() << "LastNum: " << LastNum << ": " << DFS.numToNode[LastNum]->getName()
         << "\n";

  // Step 0: initialize data structures.
  for (Index i = 0; i <= LastNum; ++i) {
    auto N = DFS.numToNode[i];
    idoms[N] = DFS.parent[N];
    sdoms[N] = N;
    Label[N] = N;
  }

  idoms[Root] = Root;
  levels[Root] = RootLevel;

  // Step 1: compute semidominators.
  for (Index i = LastNum; i > 0; --i) {
    auto CurrentNode = DFS.numToNode[i];
    for (auto PredNode : predecessors(CurrentNode)) {
      // Incoming arc from an unreachable node.
      if (DFS.nodeToNum.count(PredNode) == 0)
        continue;

      if (levels[PredNode] < MinLevel)
        continue;

      Node SDomCandidate = getSDomCandidate(CurrentNode, PredNode, DFS, Label);
      if (DFS.nodeToNum[sdoms[CurrentNode]] >
          DFS.nodeToNum[sdoms[SDomCandidate]]) {
        sdoms[CurrentNode] = sdoms[SDomCandidate];
        sdomPathPredecessors[CurrentNode] = SDomCandidate;
      }
    }
    // Update Label for the current Node.
    Label[CurrentNode] = sdoms[CurrentNode];
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i <= LastNum; ++i) {
    const auto CurrentNode = DFS.numToNode[i];
    const auto SDom = sdoms[CurrentNode];
    auto IDomCandidate = idoms[CurrentNode];
    while (DFS.nodeToNum[IDomCandidate] > DFS.nodeToNum[SDom])
      IDomCandidate = idoms[IDomCandidate];

    idoms[CurrentNode] = IDomCandidate;
    levels[CurrentNode] = levels[IDomCandidate] + 1;
  }
}

// Non-recursive union-find-based semidominator path walker.
Node NewDomTree::getSDomCandidate(const Node Start, const Node Pred,
                                  DFSResult &DFS, DenseMap<Node, Node> &Label) {
  assert(Pred != Start && "Not a predecessor");
  const Index StartNum = DFS.nodeToNum[Start];
  const Index PredNum = DFS.nodeToNum[Pred];

  if (PredNum < StartNum)
    return Pred;

  Node Next = Pred;
  SmallVector<Node, 8> SDomPath;
  // Walk the SDom path up the spanning tree.
  do {
    SDomPath.push_back(Next);
    Next = DFS.parent[Next];
  } while (DFS.nodeToNum[Next] > StartNum);

  // Compress path.
  for (auto i = SDomPath.size() - 2; i < SDomPath.size(); --i) {
    const auto Current = SDomPath[i];
    const auto Parent = SDomPath[i + 1];

    if (DFS.nodeToNum[Label[Current]] > DFS.nodeToNum[Label[Parent]])
      Label[Current] = Label[Parent];
    DFS.parent[Current] = DFS.parent[Parent];
  }

  return Label[Pred];
}

void NewDomTree::computeReachableDominators(Node Root, Index MinLevel) {
  auto &Lvls = levels; // Don't capture `this`.
  auto LevelDescender = [MinLevel, &Lvls](Node, Node To) -> bool { // CLion...
    auto LIt = Lvls.find(To);
    return LIt == Lvls.end() || LIt->second > MinLevel;
  };

  auto DFSRes = runDFS(root, LevelDescender);
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());
  DFSRes.dumpDFSNumbering();

  semiNCA(DFSRes, Root, MinLevel);
}

void NewDomTree::computeUnreachableDominators(
    Node Root, Node Incoming,
    SmallVectorImpl<std::pair<Node, Node>> &DiscoveredConnectingArcs) {
  assert(contains(Incoming));
  assert(!contains(Root));
  auto UnreachableDescender = [&DiscoveredConnectingArcs, this](Node From,
                                                                Node To) {
    // Arc unreachable -> reachable
    if (contains(To)) {
      DiscoveredConnectingArcs.push_back({From, To});
      return false;
    }

    return true;
  };

  auto DFSRes = runDFS(Root, UnreachableDescender);
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());
  DFSRes.dumpDFSNumbering();

  semiNCA(DFSRes, Root, /* MinLevel = */ 0, levels[Incoming] + 1);
  // Attach Root to existing tree.
  idoms[Root] = Incoming;
  sdoms[Root] = Incoming;
}

bool NewDomTree::contains(Node N) const { return idoms.count(N) != 0; }

Node NewDomTree::getIDom(Node N) const {
  assert(contains(N));
  const auto it = idoms.find(N);
  assert(it != idoms.end());
  return it->second;
}

Index NewDomTree::getLevel(Node N) const {
  assert(contains(N));
  const auto it = levels.find(N);
  assert(it != levels.end());
  return it->second;
}

Node NewDomTree::findNCA(Node First, Node Second) const {
  if (First == root || Second == root)
    return root;

  while (First != Second) {
    const auto LFIt = levels.find(First);
    assert(LFIt != levels.end());
    const Index LFirst = LFIt->second;

    const auto LSIt = levels.find(Second);
    assert(LSIt != levels.end());
    const Index LSecond = LSIt->second;

    if (LFirst < LSecond)
      std::swap(First, Second);

    const auto it = idoms.find(First);
    assert(it != idoms.end());
    First = it->second;
  }

  return First;
}

void NewDomTree::insertArc(Node From, Node To) {
  // Source unreachable. We don't want to maintain a forest, so we ignore
  // unreachable nodes.
  if (!contains(From))
    return;

  // Connecting previously unreachable node.
  if (!contains(To))
    insertUnreachable(From, To);
  else // Both were reachable.
    insertReachable(From, To);

  if (!verifyAll())
    dbgs() << "Verification after insertion failed!\n";
}

void NewDomTree::insertUnreachable(Node From, Node To) {
  assert(!contains(To));
  dbgs() << "Inserting " << From->getName() << " -> (unreachable) "
         << To->getName() << "\n";

  SmallVector<std::pair<Node, Node>, 8> DiscoveredArcsToReachable;
  computeUnreachableDominators(To, From, DiscoveredArcsToReachable);

  dbgs() << "Inserted " << From->getName() << " -> (prev unreachable) "
         << To->getName() << "\n";
  dumpLevels();

  for (const auto &A : DiscoveredArcsToReachable)
    insertReachable(A.first, A.second);
}

void NewDomTree::insertReachable(Node From, Node To) {
  InsertionInfo II;
  const Node NCA = findNCA(From, To);
  const Node ToIDom = getIDom(To);

  dbgs() << "Inserting a reachable arc: " << From->getName() << " -> "
         << To->getName() << "\n";

  // Nothing affected.
  if (NCA == To || NCA == ToIDom)
    return;

  dbgs() << "Marking " << To->getName() << " affected\n";
  II.affected.insert(To);
  const Index ToLevel = getLevel(To);
  dbgs() << "Putting " << To->getName() << " into bucket\n";
  II.bucket.push({ToLevel, To});

  while (!II.bucket.empty()) {
    const Node CurrentNode = II.bucket.top().second;
    II.bucket.pop();
    dbgs() << "\tAdding to visited and AQ: " << CurrentNode->getName() << "\n";
    II.visited.insert(CurrentNode);
    II.affectedQueue.push_back(CurrentNode);

    visitInsertion(CurrentNode, getLevel(CurrentNode), NCA, II);
  }

  dbgs() << "IR: Almost end, entering update with NCA " << NCA->getName()
         << "\n";
  updateInsertion(NCA, II);

  dbgs() << "Clearing stuff\n";
}

void NewDomTree::visitInsertion(Node N, Index RootLevel, Node NCA,
                                InsertionInfo &II) {
  const Index NCALevel = getLevel(NCA);
  dbgs() << "Visiting " << N->getName() << "\n";

  for (const auto Succ : successors(N)) {
    const Index SuccLevel = getLevel(Succ);
    dbgs() << "\tSuccessor " << Succ->getName() << ", level = " << SuccLevel
           << "\n";
    // Succ dominated by subtree root -- not affected.
    if (SuccLevel > RootLevel) {
      dbgs() << "\t\tdominated by subtree root\n";
      if (II.visited.count(Succ) != 0)
        continue;

      dbgs() << "\t\tMarking visited not affected " << Succ->getName() << "\n";
      II.visited.insert(Succ);
      II.visitedNotAffectedQueue.push_back(Succ);
      visitInsertion(Succ, RootLevel, NCA, II);
    } else if ((SuccLevel > NCALevel + 1) && II.affected.count(Succ) == 0) {
      dbgs() << "\t\tMarking affected and adding to bucket " << Succ->getName()
             << "\n";
      II.affected.insert(Succ);
      II.bucket.push({SuccLevel, Succ});
    }
  }
}

void NewDomTree::updateInsertion(Node NCA, InsertionInfo &II) {
  dbgs() << "Updating NCA = " << NCA->getName() << "\n";
  // Update idoms and start updating levels.
  for (const Node N : II.affectedQueue) {
    dbgs() << "\tidoms[" << N->getName() << "] = " << NCA->getName() << "\n";
    idoms[N] = NCA;
    dbgs() << "\tlevels[" << N->getName() << "] = " << levels[NCA] << " + 1\n";
    levels[N] = levels[NCA] + 1;

    assert(preorderParents.count(N) != 0);
    preorderParents.erase(N);
  }

  dbgs() << "Before updating levels\n";
  updateLevels(II);
}

void NewDomTree::updateLevels(InsertionInfo &II) {
  dbgs() << "Updating levels\n";
  // Update levels of visited but not affected nodes;
  for (const Node N : II.visitedNotAffectedQueue) {
    dbgs() << "\tlevels[" << N->getName() << "] = levels["
           << idoms[N]->getName() << "] + 1\n";
    levels[N] = levels[idoms[N]] + 1;
  }
}

void NewDomTree::deleteArc(Node From, Node To) {
  dbgs() << "Deleting arc " << From->getName() << " -> " << To->getName()
         << "\n";
  // Deletion in unreachable subtree -- nothing to do.
  if (!contains(From))
    return;

  const auto NCA = findNCA(From, To);

  // To dominates From -- nothing to do.
  if (To == NCA)
    return;

  const Node IDomTo = getIDom(To);

  // To stays reachable.
  if (From != IDomTo || isReachableFromIDom(To))
    deleteReachable(From, To);
  else
    deleteUnreachable(From, To);

  if (!verifyAll())
    dbgs() << "Verification after deletion failed!\n";
}

bool NewDomTree::isReachableFromIDom(Node N) {
  for (auto *Succ : predecessors(N)) {
    // Incoming arc from an unreachable Node.
    if (!contains(Succ))
      continue;

    const Node Support = findNCA(N, Succ);
    if (Support != N) {
      dbgs() << "\tIsReachable " << N->getName() << " from support = "
             << Succ->getName() << "\n";
      return true;
    }
  }

  return false;
}

void NewDomTree::deleteReachable(Node From, Node To) {
  auto parentIt = preorderParents.find(To);
  if (parentIt != preorderParents.end() && From != parentIt->second) {
    // What happens when why try to delete an arc that first connected
    // unreachable region? SNCA doesn't assign an spath to it.
    assert(sdomPathPredecessors.count(To) != 0);
    if (sdomPathPredecessors[To] != From)
      return;
  }

  dbgs() << "Subtree needs to be rebuilt\n";
  const Node IDomTo = getIDom(To);
  const Node PrevIDomSubTree = getIDom(IDomTo);
  const Index Level = getLevel(IDomTo);
  auto DescendBelow = [Level, this](Node, Node To) {
    return getLevel(To) > Level;
  };

  dbgs() << "Top of subtree: " << IDomTo->getName() << " [" << Level << "]\n";

  auto DFSRes = runDFS(IDomTo, DescendBelow);
  DFSRes.dumpDFSNumbering();
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());

  dbgs() << "Running SNCA\n";
  semiNCA(DFSRes, IDomTo, Level, Level);
  // Reattach.
  idoms[IDomTo] = PrevIDomSubTree;
  sdoms[IDomTo] = PrevIDomSubTree;
  dbgs() << "Reattaching:\n" << "idoms[" << IDomTo->getName() << "] = "
         << PrevIDomSubTree->getName() << "\nDeleted\n";
}

void NewDomTree::deleteUnreachable(Node From, Node To) {
  dbgs() << "Deleting unreachable " << To->getName() << "\n";

  SmallVector<Node, 8> affectedQueue;
  SmallDenseSet<Node, 8> affected;

  const Index Level = getLevel(To);
  auto DescendCollect = [Level, &affectedQueue, &affected, this](Node, Node To) {
    if (getLevel(To) > Level)
      return true;
    if (affected.count(To) == 0) {
      affected.insert(To);
      affectedQueue.push_back(To);
    }
    return false;
  };

  auto DFSRes = runDFS(To, DescendCollect);
  DFSRes.dumpDFSNumbering();
  Node MinNode = To;

  for (const Node N : affectedQueue) {
    const Node NCA = findNCA(N, To);
    if (NCA != N && getLevel(NCA) < getLevel(MinNode))
      MinNode = NCA;
  }

  for (Index i = 0; i < DFSRes.nextDFSNum; ++i) {
    const Node N = DFSRes.numToNode[i];
    idoms.erase(N);
    sdoms.erase(N);
    levels.erase(N);
    preorderParents.erase(N);
    sdomPathPredecessors.erase(N);
  }

  if (MinNode == To)
    return;

  DFSRes = 

  dbgs() << "DeleteUnreachable: running SNCA(MinNode = "
         << MinNode->getName() << ")\n";
  const Index MinLevel = getLevel(MinNode);
  const Node PrevIDomMin = getIDom(MinNode);
  MinNode->getParent()->viewCFG();
  dbgs() << "Previous idoms[MinNode] = " << PrevIDomMin->getName() << "\n";
  semiNCA(DFSRes, MinNode, MinLevel, MinLevel);
  // Reattach.
  idoms[MinNode] = PrevIDomMin;
  sdoms[MinNode] = PrevIDomMin;
  dbgs() << "Reattaching:\n" << "idoms[" << MinNode->getName() << "] = "
         << PrevIDomMin->getName() << "\nDeleted unreachable\n";
}

bool NewDomTree::verifyAll() const {
  bool IsCorrect = true;

  if (!verifyWithOldDT()) {
    IsCorrect = false;
    errs() << "\nIncorrect domtree!\n";
    dumpLegacyDomTree();
  }

  if (!verifyNCA()) {
    IsCorrect = false;
    errs() << "\nIncorrect NCA!\n";
  }

  if (!verifyLevels()) {
    IsCorrect = false;
    errs() << "\nIncorrect levels!\n";
  }

  return IsCorrect;
}

bool NewDomTree::verifyWithOldDT() const {
  assert(root);
  assert(!idoms.empty());

  DominatorTree DT(*root->getParent());
  bool Correct = true;

  for (const auto &NodeToIDom : idoms) {
    if (NodeToIDom.first == root)
      continue;

    auto Node = NodeToIDom.first;
    auto IDom = NodeToIDom.second;
    errs() << "Veryfing arc:\t" << Node->getName() << " -> "
           << IDom->getName() << "\n";
    auto DTN = DT.getNode(Node);
    auto *CorrectIDom = DTN->getIDom()->getBlock();
    if (CorrectIDom != IDom) {
      errs() << "!! NewDT:\t" << Node->getName() << " -> " << IDom->getName()
             << "\n   OldDT:\t" << Node->getName() << " -> "
             << CorrectIDom->getName() << "\n";
      Correct = false;
    }
  }

  return Correct;
}

bool NewDomTree::verifyNCA() const {
  Function *F = root->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB))
      continue;

    // For every arc U -> V in the graph, NCA(U, V) = idoms[V] or V.
    for (auto *Succ : successors(&BB)) {
      // dbgs() << "Checking NCA(" << BB.getName() << ", " << Succ->getName() <<
      //          ")\n";

      auto NCA = findNCA(&BB, Succ);
      if (NCA != Succ && NCA != getIDom(Succ)) {
        Correct = false;
        dbgs() << "Error:\tNCA(" << BB.getName() << ", " << Succ->getName()
               << ") = " << NCA->getName();
      }
    }
  }

  return Correct;
}

bool NewDomTree::verifyLevels() const {
  Function *F = root->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB) || &BB == root)
      continue;

    const Index BBL = getLevel(&BB);
    const auto IDom = getIDom(&BB);
    const Index IDomL = getLevel(IDom);
    if (BBL != (IDomL + 1)) {
      Correct = false;
      dbgs() << "Error:\tLevel(" << BB.getName() << ") = " << BBL << ", "
             << "Level(" << IDom << ") = " << IDomL << "\n";
    }
  }

  return Correct;
}

void NewDomTree::print(raw_ostream &OS) const {
  assert(!idoms.empty());
  std::set<Node, NodeByName> ToPrint;
  ChildrenTy Children;

  for (const auto &NodeToIDom : idoms) {
    Children[NodeToIDom.second].push_back(NodeToIDom.first);
    ToPrint.insert(NodeToIDom.first);
  }

  dbgs() << "\nPreorder New Dominator Tree:\n";
  while (!ToPrint.empty())
    printImpl(OS, *ToPrint.begin(), Children, ToPrint);
  dbgs() << "\n";
}

void NewDomTree::printImpl(raw_ostream &OS, Node N, const ChildrenTy &Children,
                           std::set<Node, NodeByName> &ToPrint) const {
  ToPrint.erase(N);
  const auto LevelIt = levels.find(N);
  assert(LevelIt != levels.end());
  const auto Level = LevelIt->second;
  for (Index i = 0; i <= Level; ++i)
    OS << "  ";

  OS << '[' << (Level + 1) << "] %" << N->getName() << " {}\n";

  const auto ChildrenIt = Children.find(N);
  if (ChildrenIt == Children.end())
    return;

  std::vector<Node> SortedChildren(ChildrenIt->second.begin(),
                                   ChildrenIt->second.end());
  std::sort(SortedChildren.begin(), SortedChildren.end());
  for (const auto &C : SortedChildren)
    if (ToPrint.count(C) != 0)
      printImpl(OS, C, Children, ToPrint);
}

void NewDomTree::DFSResult::dumpDFSNumbering(raw_ostream &OS) const {
  OS << "\nDFSNumbering:\n";
  OS << "\tnodeToNum size:\t" << nodeToNum.size() << "\n";
  OS << "\tparents size:\t" << parent.size() << "\n";

  using KeyValue = std::pair<Node, Index>;
  std::vector<KeyValue> Sorted(nodeToNum.begin(), nodeToNum.end());

  sort(Sorted.begin(), Sorted.end(), [](KeyValue first, KeyValue second) {
    return first.first->getName().compare(second.first->getName()) < 0;
  });

  for (const auto &NodeToNum : Sorted)
    OS << NodeToNum.first->getName() << " {" << NodeToNum.second << "}\n";
}

void NewDomTree::dumpLevels(raw_ostream &OS) const {
  OS << "\nLevels:\n";
  for (const auto &NodeToLevel : levels)
    OS << "  " << NodeToLevel.first->getName() << ": " << NodeToLevel.second
       << "\n";
}

void NewDomTree::addDebugInfoToIR() {
  auto M = root->getParent()->getParent();
  auto *IntTy = IntegerType::get(M->getContext(), 1);

  for (const auto &NodeToIDom : idoms) {
    auto BB = NodeToIDom.first;
    auto SD = sdoms[BB];
    auto ID = NodeToIDom.second;

    std::string Buffer;
    raw_string_ostream RSO(Buffer);
    IRBuilder<> Builder(BB, BB->begin());

    RSO << "idom___" << ID->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
    Buffer.clear();

    RSO << "sdom___" << SD->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
  }
}

struct GraphCFG {
  LLVMContext context;
  Module module;
  Function *function;
  DenseMap<unsigned, BasicBlock *> numToBB;

  GraphCFG(StringRef moduleName = "GraphCFG") : module(moduleName, context) {
    FunctionType *FTy = TypeBuilder<void(), false>::get(context);
    function = cast<Function>(module.getOrInsertFunction("dummy_f", FTy));
  }

  std::pair<BasicBlock *, BasicBlock *>
  getArc(std::pair<unsigned, unsigned> arc) {
    return {numToBB[arc.first], numToBB[arc.second]};
  };
};

struct InputGraph {
  unsigned nodesNum = 0;
  unsigned entry = 0;
  unsigned updateIdx = 0;

  using Arc = std::pair<unsigned, unsigned>;
  std::vector<Arc> arcs;

  enum class Op : char { Insert, Delete };
  struct Update {
    Op action;
    Arc arc;
  };
  std::vector<Update> updates;

  std::unique_ptr<GraphCFG> cfg;

  void dump(raw_ostream &OS = dbgs()) {
    OS << "Nodes:\t" << nodesNum << ", entry:\t" << entry << "\nArcs:\n";
    for (const auto &A : arcs)
      OS << A.first << "\t->\t" << A.second << "\n";

    OS << "Updates:\n";
    for (const auto &U : updates)
      OS << ((U.action == Op::Insert) ? "Ins " : "Del ") << U.arc.first
         << "\t->\t" << U.arc.second << "\n";
  }

  // Returns entry/root;
  BasicBlock *toCFG();

  using CFGArc = std::pair<BasicBlock *, BasicBlock *>;
  struct CFGUpdate {
    Op action;
    CFGArc arc;
  };
  Optional<CFGUpdate> applyUpdate();
};

InputGraph readInputGraph(std::string path) {
  dbgs() << "Reading input graph: " << path << "\n";
  std::ifstream IFS(path);
  dbgs() << IFS.good() << "\n";
  InputGraph Graph;

  for (std::string Line; std::getline(IFS, Line) && !Line.empty();) {
    std::istringstream ISS(Line);
    char Action;
    ISS >> Action;
    switch (Action) {
    default:
      llvm_unreachable("Unknown action");
    case 'p': {
      assert(Graph.nodesNum == 0 && "Double init?");
      unsigned nodesNum, arcsNum, entry, dummy;
      if (!(ISS >> nodesNum >> arcsNum >> entry >> dummy))
        llvm_unreachable("Parse error");
      Graph.nodesNum = nodesNum;
      Graph.arcs.reserve(arcsNum);
      Graph.entry = entry;
    } break;
    case 'a': {
      unsigned x, y;
      if (!(ISS >> x >> y))
        llvm_unreachable("Parse error");
      Graph.arcs.push_back({x, y});
    } break;
    case 'e':
      break;
    case 'i': {
      unsigned x, y;
      if (!(ISS >> x >> y))
        llvm_unreachable("Parse error");
      assert(x <= Graph.nodesNum);
      assert(y <= Graph.nodesNum);
      Graph.updates.push_back({InputGraph::Op::Insert, {x, y}});
    } break;
    case 'd': {
      unsigned x, y;
      if (!(ISS >> x >> y))
        llvm_unreachable("Parse error");
      assert(x <= Graph.nodesNum);
      assert(y <= Graph.nodesNum);
      Graph.updates.push_back({InputGraph::Op::Delete, {x, y}});
    } break;
    }
  }

  return Graph;
}

static void connect(BasicBlock *From, BasicBlock *To) {
  auto *IntTy =
      IntegerType::get(From->getParent()->getParent()->getContext(), 32);
  if (!From->getTerminator()) {
    IRBuilder<> IRB(From);
    IRB.CreateSwitch(ConstantInt::get(IntTy, 0), To);
    return;
  }

  SwitchInst *SI = cast<SwitchInst>(From->getTerminator());
  const auto Last = SI->getNumCases();

  auto *IntVal = ConstantInt::get(IntTy, Last);
  SI->addCase(IntVal, To);
}

static void disconnect(BasicBlock *From, BasicBlock *To) {
  dbgs() << "Deleting BB arc " << From->getName() << " -> "
         << To->getName() << "\n";
  dbgs().flush();
  if (!From->getTerminator()) {
    From->getParent()->viewCFG();
  }
  SwitchInst *SI = cast<SwitchInst>(From->getTerminator());

  if (SI->getNumCases() == 0) {
    SI->removeFromParent();
    return;
  }

  for (auto CIt = SI->case_begin(); CIt != SI->case_end(); ++CIt)
    if (CIt->getCaseSuccessor() == To) {
      SI->removeCase(CIt);
      return;
    }
}

BasicBlock *InputGraph::toCFG() {
  cfg = make_unique<GraphCFG>();
  GraphCFG &CFG = *cfg;
  BasicBlock *EntryBB = nullptr;
  std::vector<BasicBlock *> Blocks(nodesNum);

  auto MakeBB = [&](StringRef name) -> BasicBlock * {
    return BasicBlock::Create(CFG.context, name, CFG.function);
  };

  auto MakeName = [](StringRef prefix, unsigned num) {
    std::string buffer;
    raw_string_ostream OS(buffer);
    OS << prefix << num;
    OS.flush();
    return OS.str();
  };

  EntryBB = Blocks[entry - 1] = MakeBB(MakeName("entry_n_", entry));
  CFG.numToBB[entry] = EntryBB;

  for (unsigned i = 1; i <= nodesNum; ++i)
    if (i != entry) {
      Blocks[i - 1] = MakeBB(MakeName("n_", i));
      CFG.numToBB[i] = Blocks[i - 1];
    }

  for (const auto &A : arcs)
    connect(Blocks[A.first - 1], Blocks[A.second - 1]);

  return EntryBB;
}

Optional<InputGraph::CFGUpdate> InputGraph::applyUpdate() {
  if (updateIdx == updates.size())
    return None;

  auto Next = updates[updateIdx++];
  auto A = cfg->getArc(Next.arc);
  if (Next.action == InputGraph::Op::Insert)
    connect(A.first, A.second);
  else
    disconnect(A.first, A.second);

  return CFGUpdate{Next.action, A};
}

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "dominators");

  if (InputFile.empty()) {
    errs() << "No input file\n";
    return 1;
  }

  auto Graph = readInputGraph(InputFile);
  Graph.dump();
  auto *RootBB = Graph.toCFG();

  dbgs() << "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n";

  NewDomTree DT(RootBB);

  if (!DT.verifyAll())
    errs() << "NewDomTree verification failed.\n";

  DT.dump();
  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }

  Optional<InputGraph::CFGUpdate> Update;
  while ((Update = Graph.applyUpdate())) {
    if (Update->action == InputGraph::Op::Insert)
      DT.insertArc(Update->arc.first, Update->arc.second);
    else
      DT.deleteArc(Update->arc.first, Update->arc.second);

    DT.dump();
  }

  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }
}
