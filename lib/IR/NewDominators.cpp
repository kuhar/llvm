//===- Dominators.cpp - Dominator Calculation -----------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements prototype dynamic dominators.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/NewDominators.h"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "new-dom-tree"

bool VerifyNewDomInfo = true;

static cl::opt<bool,true>
VerifyNewDomInfoX("verify-new-dom-info", cl::location(VerifyNewDomInfo),
               cl::desc("Verify new dominator info (time consuming)"));


void NewDomTree::semiNCA(DFSResult &DFS, Node Root, const Index MinLevel,
                         const Node AttachTo /* = nullptr */) {
  assert(DFS.nodeToNum.count(Root) != 0);
  assert(DFS.nextDFSNum > 0 && "DFS not run?");
  DenseMap<Node, Node> Label;
  DenseMap<Node, Node> SDoms;
  const Index LastNum = DFS.nextDFSNum - 1;
  DEBUG(dbgs() << "StartNum: " << 0 << ": " << Root->getName() << "\n");
  DEBUG(dbgs() << "LastNum: " << LastNum << ": "
               << DFS.numToNode[LastNum]->getName() << "\n");

  // Step 0: initialize data structures.
  for (Index i = 0; i <= LastNum; ++i) {
    auto N = DFS.numToNode[i];
    idoms[N] = DFS.parent[N];
    SDoms[N] = N;
    Label[N] = N;
  }

  idoms[Root] = Root;
  if (Root == root || !AttachTo)
    levels[Root] = 0;
  else
    levels[Root] = getLevel(AttachTo) + 1;

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
      if (DFS.nodeToNum[SDoms[CurrentNode]] >
          DFS.nodeToNum[SDoms[SDomCandidate]]) {
        SDoms[CurrentNode] = SDoms[SDomCandidate];
        rdoms[CurrentNode] = SDomCandidate;
      }
    }
    // Update Label for the current Node.
    Label[CurrentNode] = SDoms[CurrentNode];
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i <= LastNum; ++i) {
    const auto CurrentNode = DFS.numToNode[i];
    const auto SDom = SDoms[CurrentNode];
    auto IDomCandidate = idoms[CurrentNode];
    while (DFS.nodeToNum[IDomCandidate] > DFS.nodeToNum[SDom])
      IDomCandidate = idoms[IDomCandidate];

    idoms[CurrentNode] = IDomCandidate;
    levels[CurrentNode] = levels[IDomCandidate] + 1;
  }

  if (!AttachTo)
    return;

  idoms[Root] = AttachTo;
  rdoms[Root] = AttachTo;
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

  semiNCA(DFSRes, Root, /* MinLevel = */ 0, Incoming);
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

bool NewDomTree::dominates(Node Src, Node Dst) const {
  if (!isInOutValid)
    recomputeInOutNums();

  const auto SrcInOutIt = inOutNums.find(Src);
  assert(SrcInOutIt != inOutNums.end());
  const auto DstInOutIt = inOutNums.find(Src);
  assert(DstInOutIt != inOutNums.end());

  return SrcInOutIt->second.first <= DstInOutIt->second.first &&
         SrcInOutIt->second.second >= DstInOutIt->second.second;
}

void NewDomTree::insertArc(Node From, Node To) {
  // Source unreachable. We don't want to maintain a forest, so we ignore
  // unreachable nodes.
  if (!contains(From))
    return;

  isInOutValid = false;

  // Connecting previously unreachable node.
  if (!contains(To))
    insertUnreachable(From, To);
  else // Both were reachable.
    insertReachable(From, To);

  if (VerifyNewDomInfo && !verifyAll())
    DEBUG(dbgs() << "Verification after insertion failed!\n");
}

void NewDomTree::insertUnreachable(Node From, Node To) {
  assert(!contains(To));
  DEBUG(dbgs() << "Inserting " << From->getName() << " -> (unreachable) "
               << To->getName() << "\n");

  SmallVector<std::pair<Node, Node>, 8> DiscoveredArcsToReachable;
  computeUnreachableDominators(To, From, DiscoveredArcsToReachable);

  DEBUG(dbgs() << "Inserted " << From->getName() << " -> (prev unreachable) "
               << To->getName() << "\n");
  DEBUG(dumpLevels());

  for (const auto &A : DiscoveredArcsToReachable)
    insertReachable(A.first, A.second);
}

void NewDomTree::insertReachable(Node From, Node To) {
  InsertionInfo II;
  const Node NCA = findNCA(From, To);
  const Node ToIDom = getIDom(To);

  DEBUG(dbgs() << "Inserting a reachable arc: " << From->getName() << " -> "
               << To->getName() << "\n");

  // Nothing affected.
  if (NCA == To || NCA == ToIDom)
    return;

  DEBUG(dbgs() << "Marking " << To->getName() << " affected\n");
  II.affected.insert(To);
  const Index ToLevel = getLevel(To);
  DEBUG(dbgs() << "Putting " << To->getName() << " into bucket\n");
  II.bucket.push({ToLevel, To});

  while (!II.bucket.empty()) {
    const Node CurrentNode = II.bucket.top().second;
    II.bucket.pop();
    DEBUG(dbgs() << "\tAdding to visited and AQ: " << CurrentNode->getName()
                 << "\n");
    II.visited.insert(CurrentNode);
    II.affectedQueue.push_back(CurrentNode);

    visitInsertion(CurrentNode, getLevel(CurrentNode), NCA, II);
  }

  DEBUG(dbgs() << "IR: Almost end, entering update with NCA " << NCA->getName()
               << "\n");
  updateInsertion(NCA, II);

  DEBUG(dbgs() << "Clearing stuff\n");
}

void NewDomTree::visitInsertion(Node N, Index RootLevel, Node NCA,
                                InsertionInfo &II) {
  const Index NCALevel = getLevel(NCA);
  DEBUG(dbgs() << "Visiting " << N->getName() << "\n");

  for (const auto Succ : successors(N)) {
    const Index SuccLevel = getLevel(Succ);
    DEBUG(dbgs() << "\tSuccessor " << Succ->getName() << ", level = "
              << SuccLevel << "\n");
    // Succ dominated by subtree root -- not affected.
    if (SuccLevel > RootLevel) {
      DEBUG(dbgs() << "\t\tdominated by subtree root\n");
      if (II.visited.count(Succ) != 0)
        continue;

      DEBUG(dbgs() << "\t\tMarking visited not affected " << Succ->getName()
                   << "\n");
      II.visited.insert(Succ);
      II.visitedNotAffectedQueue.push_back(Succ);
      visitInsertion(Succ, RootLevel, NCA, II);
    } else if ((SuccLevel > NCALevel + 1) && II.affected.count(Succ) == 0) {
      DEBUG(dbgs() << "\t\tMarking affected and adding to bucket "
                << Succ->getName() << "\n");
      II.affected.insert(Succ);
      II.bucket.push({SuccLevel, Succ});
    }
  }
}

void NewDomTree::updateInsertion(Node NCA, InsertionInfo &II) {
  DEBUG(dbgs() << "Updating NCA = " << NCA->getName() << "\n");
  // Update idoms and start updating levels.
  for (const Node N : II.affectedQueue) {
    DEBUG(dbgs() << "\tidoms[" << N->getName() << "] = " << NCA->getName()
                 << "\n");
    idoms[N] = NCA;
    DEBUG(dbgs() << "\tlevels[" << N->getName() << "] = " << levels[NCA]
                 << " + 1\n");
    levels[N] = levels[NCA] + 1;

    assert(preorderParents.count(N) != 0);
    preorderParents.erase(N);
  }

  DEBUG(dbgs() << "Before updating levels\n");
  updateLevels(II);
}

void NewDomTree::updateLevels(InsertionInfo &II) {
  DEBUG(dbgs() << "Updating levels\n");
  // Update levels of visited but not affected nodes;
  for (const Node N : II.visitedNotAffectedQueue) {
    DEBUG(dbgs() << "\tlevels[" << N->getName() << "] = levels["
                 << idoms[N]->getName() << "] + 1\n");
    levels[N] = levels[idoms[N]] + 1;
  }
}

void NewDomTree::deleteArc(Node From, Node To) {
  DEBUG(dbgs() << "Deleting arc " << From->getName() << " -> " << To->getName()
               << "\n");
  // Deletion in unreachable subtree -- nothing to do.
  if (!contains(From))
    return;

  const auto NCA = findNCA(From, To);

  // To dominates From -- nothing to do.
  if (To == NCA)
    return;

  isInOutValid = false;

  const Node IDomTo = getIDom(To);
  DEBUG(dbgs() << "NCA " << NCA->getName() << ", IDomTo " << IDomTo->getName()
               << "\n");

  // To stays reachable.
  if (From != IDomTo || isReachableFromIDom(To))
    deleteReachable(From, To);
  else
    deleteUnreachable(To);

  if (VerifyNewDomInfo && !verifyAll())
    DEBUG(dbgs() << "Verification after deletion failed!\n");
}

bool NewDomTree::isReachableFromIDom(Node N) {
  for (auto *Succ : predecessors(N)) {
    // Incoming arc from an unreachable Node.
    if (!contains(Succ))
      continue;

    const Node Support = findNCA(N, Succ);
    if (Support != N) {
      DEBUG(dbgs() << "\tIsReachable " << N->getName() << " from support = "
                   << Succ->getName() << "\n");
      return true;
    }
  }

  return false;
}

void NewDomTree::deleteReachable(Node From, Node To) {
  auto parentIt = preorderParents.find(To);
  if (parentIt != preorderParents.end() && From != parentIt->second) {
    assert(rdoms.count(To) != 0);
    if (rdoms[To] != From)
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
  semiNCA(DFSRes, IDomTo, Level, PrevIDomSubTree);
}

void NewDomTree::deleteUnreachable(Node To) {
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
    rdoms.erase(N);
    levels.erase(N);
    preorderParents.erase(N);
  }

  if (MinNode == To)
    return;

  dbgs() << "DeleteUnreachable: running SNCA(MinNode = "
         << MinNode->getName() << ")\n";
  const Index MinLevel = getLevel(MinNode);
  const Node PrevIDomMin = getIDom(MinNode);
  DFSRes = runDFS(MinNode, [MinLevel, this] (Node, Node To) {
    return contains(To) && getLevel(To) > MinLevel;
  });
  DFSRes.dumpDFSNumbering();

  dbgs() << "Previous idoms[MinNode] = " << PrevIDomMin->getName() << "\n";
  semiNCA(DFSRes, MinNode, MinLevel, PrevIDomMin);
}

void NewDomTree::recomputeInOutNums() const {
  inOutNums.clear();

  DenseMap<Node, SmallVector<Node, 8>> Children;
  for (const auto NodeToIDom : idoms) {
    if (NodeToIDom.first == root)
      continue;

    Children[NodeToIDom.second].push_back(NodeToIDom.first);
  }

  DenseSet<Node> Visited;
  std::vector<Node> WorkList = {root};
  Index nextNum = 0;
  while (!WorkList.empty()) {
    const Node Current = WorkList.back();

    if (Visited.count(Current) != 0) {
      WorkList.pop_back();
      inOutNums[Current].second = nextNum++;
      continue;
    }

    Visited.insert(Current);
    inOutNums[Current].first = nextNum++;
    for (const Node C : Children[Current])
      WorkList.push_back(C);
  }

  isInOutValid = true;
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

  if (!isInOutValid)
    recomputeInOutNums();

  for (const auto &NodeToIDom : idoms) {
    Children[NodeToIDom.second].push_back(NodeToIDom.first);
    ToPrint.insert(NodeToIDom.first);
  }

  dbgs() << "\nNew Dominator Tree:\n";
  while (!ToPrint.empty())
    printImpl(OS, *ToPrint.begin(), Children, ToPrint);
  dbgs() << "\n";
}

void NewDomTree::printImpl(raw_ostream &OS, Node N, const ChildrenTy &Children,
                           std::set<Node, NodeByName> &ToPrint) const {
  assert(isInOutValid);
  ToPrint.erase(N);
  const auto LevelIt = levels.find(N);
  assert(LevelIt != levels.end());
  const auto Level = LevelIt->second;
  for (Index i = 0; i <= Level; ++i)
    OS << "  ";

  const auto InOutNumIt = inOutNums.find(N);
  assert(InOutNumIt != inOutNums.end());

  OS << '[' << (Level + 1) << "] %" << N->getName() << " {"
     << InOutNumIt->second.first << ", " << InOutNumIt->second.second << "}\n";

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
    auto ID = NodeToIDom.second;

    std::string Buffer;
    raw_string_ostream RSO(Buffer);
    IRBuilder<> Builder(BB, BB->begin());

    RSO << "idom___" << ID->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
    Buffer.clear();

    if (rdoms.count(BB) == 0)
      continue;

    auto RD = rdoms[BB];
    RSO << "rdom___" << RD->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
  }
}

void NewDomTree::dumpLegacyDomTree() const {
  DominatorTree DT(*root->getParent());
  DT.print(dbgs());
}
