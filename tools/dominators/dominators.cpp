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
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Signals.h"

#include <cctype>
#include <fstream>
#include <map>
#include <memory>
#include <queue>
#include <string>
#include <sstream>
#include <queue>
#include <utility>
#include <vector>

using namespace llvm;

static cl::opt<std::string>
    InputFile(cl::Positional, cl::desc("<input file>"), cl::init("-"));
static cl::opt<bool>
    ViewCFG("view-cfg", cl::desc("View CFG"));


using Node = BasicBlock *;
using Index = unsigned;

struct NodeByName {
  bool operator() (const Node first, const Node second) const {
    const auto Cmp = first->getName().compare(second->getName());
    if (Cmp == 0)
      return less{}(first, second);

    return Cmp < 0;
  }
};

class NewDomTree {
public:
  NewDomTree(Node root) : root(root) {}

  void computeDFSNumbering();
  void computeDominators();

  bool contains(Node N) const;
  Node getIDom(Node N) const;
  Index getLevel(Node N) const;
  Node findNCA(Node First, Node Second) const;

  void insertArc(Node From, Node To);

  bool verifyAll() const;
  bool verifyWithOldDT() const;
  bool verifyNCA() const;
  bool verifyLevels() const;
  void print(raw_ostream& OS) const;
  void dump() const { print(dbgs()); }

// private: // Public for testing purposes.
  Node root;
  Index currentDFSNum = 0;
  DenseMap<Node, Index> nodeToNum;
  DenseMap<Index, Node> numToNode;
  DenseMap<Node, Node> parents;
  DenseMap<Node, Index> descendantsNum; // FIXME: Compute it.
  DenseMap<Node, Node> idoms;
  DenseMap<Node, Node> sdoms;
  DenseMap<Node, Index> levels;

  struct InsertionInfo {
    using BucketElementTy = std::pair<Index, Node>;
    struct DecreasingLevel {
      bool operator()(const BucketElementTy &First,
                      const BucketElementTy &Second) const {
        return First.first > Second.first;
      }
    };

    std::priority_queue<BucketElementTy, SmallVector<BucketElementTy, 8>,
                        DecreasingLevel> bucket;
    DenseSet<Node> affected;
    DenseSet<Node> visited;
    SmallVector<Node, 8> affectedQueue;
    SmallVector<Node, 8> visitedNotAffectedQueue;
  };

  Node getSDomCandidate(Node Start, Node Pred, DenseMap<Node, Node> &Labels);

  void insertReachable(Node From, Node To);
  void insertUnreachable(Node From, Node To);
  void visit(Node N, Index RootLevel, Node NCA, InsertionInfo &II);
  void update(Node NCA, InsertionInfo &II);
  void updateLevels(InsertionInfo &II);

  using ChildrenTy = DenseMap<Node, SmallVector<Node, 8>>;
  void printImpl(raw_ostream& OS, Node N, const ChildrenTy &Children,
                 std::set<Node, NodeByName> &ToPrint) const;

public:
  void dumpDFSNumbering(raw_ostream& OS = dbgs()) const;
  void addDebugInfoToIR();
  void viewCFG() const { root->getParent()->viewCFG(); }
  void dumpLegacyDomTree(raw_ostream &OS = dbgs()) const {
    DominatorTree DT(*root->getParent());
    DT.print(OS);
  }
};

void NewDomTree::computeDFSNumbering() {
  currentDFSNum = 0;
  parents[root] = root;

  DenseSet<Node> Visited;
  std::vector<Node> WorkList;
  WorkList.push_back(root);

  // Compute preorder numbers nad parents.
  while (!WorkList.empty()) {
    BasicBlock *BB = WorkList.back();
    WorkList.pop_back();
    if (Visited.count(BB) != 0)
      continue;


    nodeToNum[BB] = currentDFSNum;
    numToNode[currentDFSNum] = BB;
    ++currentDFSNum;

    Visited.insert(BB);
    for (const auto& Succ : reverse(successors(BB)))
      if (Visited.count(Succ) == 0) {
        WorkList.push_back(Succ);
        parents[Succ] = BB;
      }
  }
}

void NewDomTree::computeDominators() {
  DenseMap<Node, Node> Label;

  // Step 0: initialize data structures.
  for (const auto &NodeToNum : nodeToNum) {
    Node N = NodeToNum.first;
    idoms[N] = parents[N];
    sdoms[N] = N;
    Label[N] = N;
  }

  levels[root] = 0;

  // Step 1: compute semidominators.
  assert(currentDFSNum > 0 && "DFS not run?");
  for (Index i = currentDFSNum - 1; i >= 1; --i) {
    auto CurrentNode = numToNode[i];
    for (auto PredNode : predecessors(CurrentNode)) {
      assert(nodeToNum.count(PredNode) != 0);
      Node SDomCandidate = getSDomCandidate(CurrentNode, PredNode, Label);
      if (nodeToNum[sdoms[CurrentNode]] > nodeToNum[sdoms[SDomCandidate]])
        sdoms[CurrentNode] = sdoms[SDomCandidate];
    }
    // Update Label for the current Node.
    Label[CurrentNode] = sdoms[CurrentNode];
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i < currentDFSNum; ++i) {
    const auto CurrentNode = numToNode[i];
    const auto SDom = sdoms[CurrentNode];
    auto IDomCandidate = idoms[CurrentNode];
    while (nodeToNum[IDomCandidate] > nodeToNum[SDom])
      IDomCandidate = idoms[IDomCandidate];

    idoms[CurrentNode] = IDomCandidate;
    levels[CurrentNode] = levels[IDomCandidate] + 1;
  }
}

// Non-recursive union-find-based semidominator path walker.
Node NewDomTree::getSDomCandidate(const Node Start, const Node Pred,
                                  DenseMap<Node, Node> &Label) {
  assert(Pred != Start && "Not a predecessor");
  const Index StartNum = nodeToNum[Start];
  const Index PredNum = nodeToNum[Pred];

  if (PredNum < StartNum)
    return Pred;

  Node Next = Pred;
  SmallVector<Node, 8> SDomPath;
  // Walk the SDom path up the spanning tree.
  do {
    SDomPath.push_back(Next);
    Next = parents[Next];
  } while (nodeToNum[Next] > StartNum);

  // Compress path.
  for (auto i = SDomPath.size() - 2; i < SDomPath.size(); --i) {
    const auto Current = SDomPath[i];
    const auto Parent = SDomPath[i + 1];

    if (nodeToNum[Label[Current]] > nodeToNum[Label[Parent]])
      Label[Current] = Label[Parent];
    parents[Current] = parents[Parent];
  }

  return Label[Pred];
}

bool NewDomTree::contains(Node N) const {
  return nodeToNum.find(N) != nodeToNum.end();
}

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

}

void NewDomTree::insertReachable(Node From, Node To) {
  InsertionInfo II;
  const Node NCA = findNCA(From, To);
  const Node ToIDom = getIDom(To);

  dbgs() << "Inserting a reachable arc: " << From->getName() << " -> " <<
            To->getName() << "\n";

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

    visit(CurrentNode, getLevel(CurrentNode), NCA, II);
  }

  dbgs() << "IR: Almost end, entering update with NCA " << NCA->getName() << "\n";
  update(NCA, II);

  dbgs() << "Clearing stuff\n";
}

void NewDomTree::visit(Node N, Index RootLevel, Node NCA, InsertionInfo &II) {
  const Index NCALevel = getLevel(NCA);
  dbgs() << "Visiting " << N->getName() << "\n";

  for (const auto Succ : successors(N)) {
    const Index SuccLevel = getLevel(Succ);
    dbgs() << "\tSuccessor " << Succ->getName() << ", level = " << SuccLevel << "\n";
    // Succ dominated by subtree root -- not affected.
    if (SuccLevel > RootLevel) {
      dbgs() << "\t\tdominated by subtree root\n";
      if (II.visited.count(Succ) != 0)
        continue;

      dbgs() << "\t\tMarking visited not affected " << Succ->getName() << "\n";
      II.visited.insert(Succ);
      II.visitedNotAffectedQueue.push_back(Succ);
      visit(Succ, RootLevel, NCA, II);
    } else if ((SuccLevel > NCALevel + 1) && II.affected.count(Succ) == 0) {
      dbgs() << "\t\tMarking affected and adding to bucket " << Succ->getName() <<
                "\n";
      II.affected.insert(Succ);
      II.bucket.push({SuccLevel, Succ});
    }
  }
}

void NewDomTree::update(Node NCA, InsertionInfo &II) {
  dbgs() << "Updating NCA = " << NCA->getName() << "\n";
  // Update idoms and start updating levels.
  for (const Node N : II.affectedQueue) {
    dbgs() << "\tidoms[" << N->getName() << "] = " << NCA->getName() << "\n";
    idoms[N] = NCA;
    dbgs() << "\tlevels[" << N->getName() << "] = " << levels[NCA] << " + 1\n";
    levels[N] = levels[NCA] + 1;
  }

  dbgs() << "Before updating levels\n";
  updateLevels(II);
}

void NewDomTree::updateLevels(InsertionInfo &II) {
  dbgs() << "Updating levels\n";
  // Update levels of visited but not affected nodes;
  for (const Node N : II.visitedNotAffectedQueue) {
    dbgs() << "\tlevels[" << N->getName() << "] = levels[" << idoms[N]->getName() <<
              "] + 1\n";
    levels[N] = levels[idoms[N]] + 1;
  }
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
  assert(!nodeToNum.empty());

  DominatorTree DT(*root->getParent());
  bool Correct = true;

  for (const auto& NodeToIDom : idoms) {
    if (NodeToIDom.first == root)
      continue;

    auto Node = NodeToIDom.first;
    auto IDom = NodeToIDom.second;
    auto DTN = DT.getNode(Node);
    auto *CorrectIDom = DTN->getIDom()->getBlock();
    if (CorrectIDom != IDom) {
      errs() << "!! NewDT:\t" << Node->getName() << " -> " <<
                IDom->getName() << "\n   OldDT:\t" << Node->getName() <<
                " -> " << CorrectIDom->getName() << "\n";
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
        dbgs() << "Error:\tNCA(" << BB.getName() << ", " << Succ->getName() <<
                  ") = " << NCA->getName();
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
      dbgs() << "Error:\tLevel(" << BB.getName() << ") = " << BBL << ", " <<
             "Level(" << IDom << ") = " << IDomL << "\n";
    }
  }

  return Correct;
}

void NewDomTree::print(raw_ostream& OS) const {
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

  const auto NodeNumIt = nodeToNum.find(N);
  assert(NodeNumIt != nodeToNum.end());
  OS << '[' << (Level + 1) << "] %" << N->getName() << " {" <<
        NodeNumIt->second << "}\n";

  const auto ChildrenIt = Children.find(N);
  if (ChildrenIt == Children.end())
    return;

  std::vector<Node> SortedChildren(ChildrenIt->second.begin(),
                                   ChildrenIt->second.end());
  std::sort(SortedChildren.begin(), SortedChildren.end());
  for (const auto& C : SortedChildren)
    if (ToPrint.count(C) != 0)
      printImpl(OS, C, Children, ToPrint);
}

void NewDomTree::dumpDFSNumbering(raw_ostream &OS) const {
  OS << "\nDFSNumbering:\n";
  OS << "\tnodeToNum size:\t" << nodeToNum.size() << "\n";
  OS << "\tparents size:\t" << parents.size() << "\n";

  using KeyValue = std::pair<Node, Index>;
  std::vector<KeyValue> Sorted(nodeToNum.begin(),
                                             nodeToNum.end());

  sort(Sorted.begin(), Sorted.end(), [](KeyValue first, KeyValue second) {
    return first.first->getName().compare(second.first->getName()) < 0;
  });

  for (const auto &NodeToNum : Sorted)
    OS << NodeToNum.first->getName() << " {" << NodeToNum.second << "}\n";
}

void NewDomTree::addDebugInfoToIR() {
  auto M = root->getParent()->getParent();
  auto *IntTy = IntegerType::get(M->getContext(), 1);

  for (const auto& NodeToIDom : idoms) {
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

  GraphCFG(StringRef moduleName = "GraphCFG")
      : module(moduleName, context) {
    FunctionType *FTy = TypeBuilder<void(), false>::get(context);
    function = cast<Function>(module.getOrInsertFunction("dummy_f", FTy));
  }

  std::pair<BasicBlock *, BasicBlock*>
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
  struct Update { Op action; Arc arc; };
  std::vector<Update> updates;

  std::unique_ptr<GraphCFG> cfg;

  void dump(raw_ostream &OS = dbgs()) {
    OS << "Nodes:\t" << nodesNum << ", entry:\t" << entry << "\nArcs:\n";
    for (const auto &A : arcs)
      OS << A.first << "\t->\t" << A.second << "\n";

    OS << "Updates:\n";
    for (const auto &U : updates)
      OS << ((U.action == Op::Insert) ? "Ins " : "Del ") << U.arc.first <<
            "\t->\t" << U.arc.second << "\n";
  }

  // Returns entry/root;
  BasicBlock * toCFG();

  using CFGArc = std::pair<BasicBlock *, BasicBlock *>;
  struct CFGUpdate { Op action; CFGArc arc; };
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
      default: llvm_unreachable("Unknown action");
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
      case 'e': break;
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
  auto *IntTy = IntegerType::get(From->getParent()->getParent()->getContext(),
                                 32);
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

BasicBlock *InputGraph::toCFG() {
  cfg = make_unique<GraphCFG>();
  GraphCFG &CFG = *cfg;
  BasicBlock* EntryBB = nullptr;
  std::vector<BasicBlock *> Blocks(nodesNum);

  auto MakeBB = [&] (StringRef name) -> BasicBlock * {
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
  if (Next.action == InputGraph::Op::Insert) {
    auto A = cfg->getArc(Next.arc);
    connect(A.first, A.second);

    return CFGUpdate{Next.action, A};
  }

  llvm_unreachable("Not implemented");
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
  DT.computeDFSNumbering();
  DT.dumpDFSNumbering();
  DT.computeDominators();

  if (!DT.verifyAll())
    errs() << "NewDomTree verification failed.\n";

  DT.dump();

  Optional<InputGraph::CFGUpdate> Update;
  while ((Update = Graph.applyUpdate())) {
    if (Update->action == InputGraph::Op::Insert)
      DT.insertArc(Update->arc.first, Update->arc.second);
    else
      llvm_unreachable("Not implemented");

    DT.dump();
  }

  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }
}
