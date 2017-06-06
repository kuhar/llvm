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

#include <llvm/IR/NewDominators.h>
#include "llvm/IR/NewDominators.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "new-dom-tree"

bool VerifyNewDomInfo = true;

static cl::opt<bool, true> VerifyNewDomInfoX(
    "verify-new-dom-info", cl::location(VerifyNewDomInfo),
    cl::desc("Verify new dominator info (time consuming)"));

static cl::opt<bool> VerifySiblingProperty("verify-sibling-property",
                                           cl::init(false));

void DTNode::addChild(DTNode *Child) {
  assert(!hasChild(Child));
  Children.push_back(Child);
}

void DTNode::removeChild(DTNode *Child) {
  assert(hasChild(Child));
  std::swap(*std::find(begin(), end(), Child), Children.back());
  Children.pop_back();
}

void DTNode::setIDom(DTNode *NewIDom) {
  if (IDom == NewIDom)
    return;

  if (IDom != nullptr)
    IDom->removeChild(this);

  IDom = NewIDom;
  NewIDom->addChild(this);
}

template <typename T>
static StringRef NameOrNullptrStr(T *V) {
  return V ? V->getName() : "nullptr";
}

void DTNode::dump(raw_ostream &OS) const {
  OS << "DTNode{ " << BB->getName() << ", IDom(" << NameOrNullptrStr(IDom)
     << "), Level(" << Level << "), RDom(" << NameOrNullptrStr(RDom)
     << "), PreorderParent(" << NameOrNullptrStr(PreorderParent) << ")\n"
     << "\tChildren: [";

  for (auto *Child : *this)
    OS << Child->getName() << ", ";

  OS << "]\n";
}

void NewDomTree::semiNCA(DFSResult &DFS, BlockTy Root, const Index MinLevel,
                         const BlockTy AttachTo /* = nullptr */) {
  assert(DFS.NodeToInfo.count(Root) != 0 && "DFS not run?");
  assert(DFS.NextDFSNum > 0 && "DFS not run?");

  struct SemiNCAInfo {
    BlockTy Label;
    BlockTy SDom;
  };

  DenseMap<BlockTy, SemiNCAInfo> Info;
  const Index LastNum = DFS.NextDFSNum - 1;
  DEBUG(dbgs() << "StartNum: " << 0 << ": " << Root->getName() << "\n");
  DEBUG(dbgs() << "LastNum: " << LastNum << ": "
               << DFS.NumToNode[LastNum]->getName() << "\n");

  // Step 0: initialize data structures.
  for (Index i = 0; i <= LastNum; ++i) {
    auto N = DFS.NumToNode[i];
    auto TN = getOrAddNode(N);
    if (N != Root)
      TN->setIDom(getOrAddNode(DFS.NodeToInfo[N].Parent));
    auto InfoIt = Info.find(N);
    InfoIt->second.SDom = N;
    InfoIt->second.Label = N;
  }

  auto RootNode = getNode(Root);
  RootNode->IDom = RootNode;
  auto AttachToTreeNode = getNode(AttachTo);

  if (RootNode == Entry || !AttachTo)
    RootNode->Level = 0;
  else
    RootNode->Level = AttachToTreeNode->Level + 1;

  // Step 1: compute semidominators.
  for (Index i = LastNum; i > 0; --i) {
    auto CurrentNode = DFS.NumToNode[i];
    DTNode *CurrentTreeNode = getNode(CurrentNode);
    auto &CurrentInfo = Info[CurrentNode];

    for (auto PredNode : DFS.NodeToInfo[CurrentNode].Predecessors) {
      if (PredNode == CurrentNode) continue;

      // Incoming arc from an unreachable node.
      if (DFS.NodeToInfo.count(PredNode) == 0) continue;

      DTNode *PredTreeNode = getNode(PredNode);
      if (PredTreeNode->Level < MinLevel) continue;

      BlockTy SDomCandidate = 
          getSDomCandidate(CurrentNode, PredNode, DFS, Label);

      BlockTy SDomCurrent = CurrentInfo.SDom;
      auto &SDomCandidateInfo = Info[SDomCandidate];
      if (DFS.NodeToInfo[CurrentInfo.SDom].Num >
          DFS.NodeToInfo[SDomCandidateInfo.SDom].Num) {
        CurrentInfo.SDom = SDomCandidateInfo.SDom;
        CurrentTreeNode->RDom = getNode(SDomCandidate);
      }
    }
    // Update Label for the current Block.
    CurrentInfo.Label = CurrentInfo.SDom;
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i <= LastNum; ++i) {
    const auto CurrentNode = DFS.NumToNode[i];
    const auto CurrentTreeNode = getNode(CurrentNode);
    const auto SDom = Info[CurrentNode].SDom;
    const auto &SDomInfo = Info[SDom];
    auto IDomCandidate = CurrentTreeNode->IDom;
    while (DFS.NodeToInfo[IDomCandidate->BB].Num > DFS.NodeToInfo[SDom].Num)
      IDomCandidate = IDomCandidate->IDom;

    CurrentTreeNode->setIDom(IDomCandidate);
    CurrentTreeNode->Level = IDomCandidate->Level + 1;
  }

  if (!AttachTo) return;


  RootNode->setIDom(AttachToTreeNode);
  RootNode->RDom = AttachToTreeNode;
}

// Non-recursive union-find-based semidominator path walker.
BlockTy NewDomTree::getSDomCandidate(const BlockTy Start, const BlockTy Pred,
                            DFSResult &DFS, DenseMap<BlockTy, BlockTy> &Label) {
  assert(Pred != Start && "Not a predecessor");
  const Index StartNum = DFS.nodeToNum[Start];
  const Index PredNum = DFS.nodeToNum[Pred];

  if (PredNum < StartNum) return Pred;

  BlockTy Next = Pred;
  SmallVector<BlockTy, 8> SDomPath;
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

void NewDomTree::computeReachableDominators(BlockTy Root, Index MinLevel) {
  auto &Lvls = levels;  // Don't capture `this`.
  auto LevelDescender = [MinLevel, &Lvls](BlockTy, BlockTy To) -> bool {  // CLion...
    auto LIt = Lvls.find(To);
    return LIt == Lvls.end() || LIt->second > MinLevel;
  };

  auto DFSRes = runDFS(root, LevelDescender);
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());
  DEBUG(DFSRes.dumpDFSNumbering());

  semiNCA(DFSRes, Root, MinLevel);
}

void NewDomTree::computeUnreachableDominators(
    BlockTy Root, BlockTy Incoming,
    SmallVectorImpl<std::pair<BlockTy, BlockTy>> &DiscoveredConnectingArcs) {
  assert(contains(Incoming));
  assert(!contains(Root));
  auto UnreachableDescender = [&DiscoveredConnectingArcs, this](BlockTy From,
                                                                BlockTy To) {
    // Arc unreachable -> reachable
    if (contains(To)) {
      DiscoveredConnectingArcs.push_back({From, To});
      return false;
    }

    return true;
  };

  auto DFSRes = runDFS(Root, UnreachableDescender);
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());
  DEBUG(DFSRes.dumpDFSNumbering());

  semiNCA(DFSRes, Root, /* MinLevel = */ 0, Incoming);
}

bool NewDomTree::contains(BlockTy BB) const { return TreeNodes.count(BB) != 0; }

DTNode *NewDomTree::getNode(BlockTy BB) {
  auto it = TreeNodes.find(BB);
  assert(it != TreeNodes.end());
  return it->second.get();
}

const DTNode *NewDomTree::getNode(BlockTy BB) const {
  auto it = TreeNodes.find(BB);
  assert(it != TreeNodes.end());
  return it->second.get();
}

DTNode *NewDomTree::addNode(BlockTy BB) {
  assert(!contains(BB));
  return (TreeNodes[BB] = make_unique<DTNode>(BB)).get();
}

DTNode *NewDomTree::getOrAddNode(BlockTy BB) {
  auto it = TreeNodes.find(BB);
  if (it != TreeNodes.end())
    return  it->second.get();

  return addNode(BB);
}

BlockTy NewDomTree::findNCA(BlockTy First, BlockTy Second) const {
  if (First == root || Second == root) return root;

  while (First != Second) {
    const auto LFIt = levels.find(First);
    assert(LFIt != levels.end());
    const Index LFirst = LFIt->second;

    const auto LSIt = levels.find(Second);
    assert(LSIt != levels.end());
    const Index LSecond = LSIt->second;

    if (LFirst < LSecond) std::swap(First, Second);

    const auto it = idoms.find(First);
    assert(it != idoms.end());
    First = it->second;
  }

  return First;
}

bool NewDomTree::dominates(BlockTy Src, BlockTy Dst) const {
  if (getIDom(Dst) == Src)
    return true;

  if (!isInOutValid) recomputeInOutNums();

  const auto SrcInOutIt = inOutNums.find(Src);
  assert(SrcInOutIt != inOutNums.end());
  const auto DstInOutIt = inOutNums.find(Src);
  assert(DstInOutIt != inOutNums.end());

  return SrcInOutIt->second.first <= DstInOutIt->second.first &&
         SrcInOutIt->second.second >= DstInOutIt->second.second;
}

void NewDomTree::insertArc(BlockTy From, BlockTy To) {
  // Source unreachable. We don't want to maintain a forest, so we ignore
  // unreachable nodes.
  if (!contains(From)) return;

  isInOutValid = false;

  // Connecting previously unreachable node.
  if (!contains(To))
    insertUnreachable(From, To);
  else  // Both were reachable.
    insertReachable(From, To);

  if (VerifyNewDomInfo && !verify(Verification::Basic))
    DEBUG(dbgs() << "Verification after insertion failed!\n");
}

void NewDomTree::insertUnreachable(BlockTy From, BlockTy To) {
  assert(!contains(To));
  DEBUG(dbgs() << "Inserting " << From->getName() << " -> (unreachable) "
               << To->getName() << "\n");

  SmallVector<std::pair<BlockTy, BlockTy>, 8> DiscoveredArcsToReachable;
  computeUnreachableDominators(To, From, DiscoveredArcsToReachable);

  DEBUG(dbgs() << "Inserted " << From->getName() << " -> (prev unreachable) "
               << To->getName() << "\n");
  DEBUG(dumpLevels());

  for (const auto &A : DiscoveredArcsToReachable)
    insertReachable(A.first, A.second);
}

void NewDomTree::insertReachable(BlockTy From, BlockTy To) {
  InsertionInfo II;
  const BlockTy NCA = findNCA(From, To);
  const BlockTy ToIDom = getIDom(To);

  DEBUG(dbgs() << "Inserting a reachable arc: " << From->getName() << " -> "
               << To->getName() << "\n");

  // Nothing affected.
  if (NCA == To || NCA == ToIDom) return;

  DEBUG(dbgs() << "Marking " << To->getName() << " affected\n");
  II.affected.insert(To);
  const Index ToLevel = getLevel(To);
  DEBUG(dbgs() << "Putting " << To->getName() << " into bucket\n");
  II.bucket.push({ToLevel, To});

  while (!II.bucket.empty()) {
    const BlockTy CurrentNode = II.bucket.top().second;
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
  DEBUG(dump());
}

void NewDomTree::visitInsertion(BlockTy N, Index RootLevel, BlockTy NCA,
                                InsertionInfo &II) {
  const Index NCALevel = getLevel(NCA);
  DEBUG(dbgs() << "Visiting " << N->getName() << "\n");

  for (const auto Succ : successors(N)) {
    const Index SuccLevel = getLevel(Succ);
    DEBUG(dbgs() << "\tSuccessor " << Succ->getName()
                 << ", level = " << SuccLevel << "\n");
    // Succ dominated by subtree root -- not affected.
    if (SuccLevel > RootLevel) {
      DEBUG(dbgs() << "\t\tdominated by subtree root\n");
      if (II.visited.count(Succ) != 0) continue;

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

void NewDomTree::updateInsertion(BlockTy NCA, InsertionInfo &II) {
  DEBUG(dbgs() << "Updating NCA = " << NCA->getName() << "\n");
  // Update idoms and start updating levels.
  for (const BlockTy N : II.affectedQueue) {
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
  for (const BlockTy N : II.visitedNotAffectedQueue) {
    DEBUG(dbgs() << "\tlevels[" << N->getName() << "] = levels["
                 << idoms[N]->getName() << "] + 1\n");
    levels[N] = levels[idoms[N]] + 1;
  }
}

void NewDomTree::deleteArc(BlockTy From, BlockTy To) {
  DEBUG(dbgs() << "Deleting arc " << From->getName() << " -> " << To->getName()
               << "\n");
  // Deletion in unreachable subtree -- nothing to do.
  if (!contains(From)) return;

  const auto NCA = findNCA(From, To);

  // To dominates From -- nothing to do.
  if (To == NCA) return;

  isInOutValid = false;

  const BlockTy IDomTo = getIDom(To);
  DEBUG(dbgs() << "NCA " << NCA->getName() << ", IDomTo " << IDomTo->getName()
               << "\n");

  // To stays reachable.
  if (From != IDomTo || isReachableFromIDom(To))
    deleteReachable(From, To);
  else
    deleteUnreachable(To);

  if (VerifyNewDomInfo && !verify(Verification::Basic)) {
    DEBUG(dbgs() << "Verification after deletion failed!\n");
    DEBUG(dbgs().flush());
  }
}

bool NewDomTree::isReachableFromIDom(BlockTy N) {
  for (auto *Succ : predecessors(N)) {
    // Incoming arc from an unreachable BlockTy.
    if (!contains(Succ)) continue;

    const BlockTy Support = findNCA(N, Succ);
    if (Support != N) {
      DEBUG(dbgs() << "\tIsReachable " << N->getName()
                   << " from support = " << Succ->getName() << "\n");
      return true;
    }
  }

  return false;
}

void NewDomTree::deleteReachable(BlockTy From, BlockTy To) {
  auto parentIt = preorderParents.find(To);
  if (parentIt != preorderParents.end() && From != parentIt->second) {
    assert(rdoms.count(To) != 0);
    if (rdoms[To] != From) return;
  }

  DEBUG(dbgs() << "Subtree needs to be rebuilt\n");
  const BlockTy IDomTo = getIDom(To);
  const BlockTy PrevIDomSubTree = getIDom(IDomTo);
  const Index Level = getLevel(IDomTo);
  auto DescendBelow = [Level, this](BlockTy, BlockTy To) {
    return getLevel(To) > Level;
  };

  DEBUG(dbgs() << "Top of subtree: " << IDomTo->getName() << " [" << Level
               << "]\n");

  auto DFSRes = runDFS(IDomTo, DescendBelow);
  DEBUG(DFSRes.dumpDFSNumbering());
  preorderParents.insert(DFSRes.parent.begin(), DFSRes.parent.end());

  DEBUG(dbgs() << "Running SNCA\n");
  semiNCA(DFSRes, IDomTo, Level, PrevIDomSubTree);
}

void NewDomTree::deleteUnreachable(BlockTy To) {
  DEBUG(dbgs() << "Deleting unreachable " << To->getName() << "\n");

  SmallVector<BlockTy, 8> affectedQueue;
  SmallDenseSet<BlockTy, 8> affected;

  const Index Level = getLevel(To);
  auto DescendCollect = [Level, &affectedQueue, &affected, this](BlockTy,
                                                                 BlockTy To) {
    if (getLevel(To) > Level) return true;
    if (affected.count(To) == 0) {
      affected.insert(To);
      affectedQueue.push_back(To);
    }
    return false;
  };

  auto DFSRes = runDFS(To, DescendCollect);
  DEBUG(DFSRes.dumpDFSNumbering());
  BlockTy MinNode = To;

  for (const BlockTy N : affectedQueue) {
    const BlockTy NCA = findNCA(N, To);
    if (NCA != N && getLevel(NCA) < getLevel(MinNode)) MinNode = NCA;
  }

  for (Index i = 0; i < DFSRes.nextDFSNum; ++i) {
    const BlockTy N = DFSRes.numToNode[i];
    DEBUG(dbgs() << "Erasing node info "  << N->getName()
                 << " (level " << levels[N] << ", idom "
                 << idoms[N]->getName() << ")\n");
    idoms.erase(N);
    rdoms.erase(N);
    levels.erase(N);
    preorderParents.erase(N);
  }

  if (MinNode == To) return;

  DEBUG(dbgs() << "DeleteUnreachable: running SNCA(MinNode = "
               << MinNode->getName() << ")\n");
  const Index MinLevel = getLevel(MinNode);
  const BlockTy PrevIDomMin = getIDom(MinNode);
  DFSRes = runDFS(MinNode, [MinLevel, this](BlockTy, BlockTy To) {
    return contains(To) && getLevel(To) > MinLevel;
  });
  DEBUG(DFSRes.dumpDFSNumbering());

  DEBUG(dbgs() << "Previous idoms[MinNode] = " << PrevIDomMin->getName()
               << "\n");
  semiNCA(DFSRes, MinNode, MinLevel, PrevIDomMin);
}

void NewDomTree::recomputeInOutNums() const {
  inOutNums.clear();

  DenseMap<BlockTy, SmallVector<BlockTy, 8>> Children;
  for (const auto NodeToIDom : idoms) {
    if (NodeToIDom.first == root) continue;

    Children[NodeToIDom.second].push_back(NodeToIDom.first);
  }

  DenseSet<BlockTy> Visited;
  std::vector<BlockTy> WorkList = {root};
  Index nextNum = 0;
  while (!WorkList.empty()) {
    const BlockTy Current = WorkList.back();

    if (Visited.count(Current) != 0) {
      WorkList.pop_back();
      inOutNums[Current].second = nextNum++;
      continue;
    }

    Visited.insert(Current);
    inOutNums[Current].first = nextNum++;
    for (const BlockTy C : Children[Current]) WorkList.push_back(C);
  }

  isInOutValid = true;
}

void NewDomTree::toOldDT(DominatorTree &DT) const {
  DominatorTree Temp;
  Temp.setNewRoot(root);

  std::vector<std::pair<Index, BlockTy>> LevelsNodes;
  LevelsNodes.reserve(levels.size());

  for (auto NodeToLevel : levels)
    LevelsNodes.push_back({NodeToLevel.second, NodeToLevel.first});

  std::sort(LevelsNodes.begin(), LevelsNodes.end());

  for (auto LN : LevelsNodes)
    if (LN.second != root)
      Temp.addNewBlock(LN.second, getIDom(LN.second));

  Temp.updateDFSNumbers();
  if (VerifyDomInfo)
    Temp.verifyDomTree();

  DT = std::move(Temp);
}

bool NewDomTree::verify(Verification VerificationLevel) const {
  assert(VerificationLevel != Verification::None);
  bool IsCorrect = true;

  const auto VL = static_cast<unsigned>(VerificationLevel);
  if ((VL & unsigned(Verification::Basic)) != 0) {
    if (!verifyNCA()) {
      IsCorrect = false;
      errs() << "\nIncorrect NCA!\n";
    }

    if (!verifyLevels()) {
      IsCorrect = false;
      errs() << "\nIncorrect levels!\n";
    }
  }

  if ((VL & unsigned(Verification::CFG)) != 0) {
    if (!verifyReachability()) {
      IsCorrect = false;
      errs() << "\nIncorrect reachability!\n";
    }

    if (!verifyParentProperty()) {
      IsCorrect = false;
      errs() << "\nParent property doesn't hold!\n";
    }
  }

  if ((VL & unsigned(Verification::Sibling)) != 0 && !verifySiblingProperty()) {
    IsCorrect = false;
    errs() << "\nSibling property doesn't hold!\n";
  }

  if ((VL & unsigned(Verification::OldDT)) != 0 && !verifyWithOldDT()) {
    IsCorrect = false;
    errs() << "\nIncorrect domtree!\n";
    DEBUG(dumpLegacyDomTree());
    DEBUG(dbgs().flush());
  }

  if (!IsCorrect)
    abort();
  return IsCorrect;
}

bool NewDomTree::verifyWithOldDT() const {
  assert(root);
  assert(!idoms.empty());

  DominatorTree DT(*root->getParent());
  bool Correct = true;

  for (const auto &NodeToIDom : idoms) {
    if (NodeToIDom.first == root) continue;

    auto BlockTy = NodeToIDom.first;
    auto IDom = NodeToIDom.second;
    auto DTN = DT.getNode(BlockTy);
    auto *CorrectIDom = DTN->getIDom()->getBlock();
    if (CorrectIDom != IDom) {
      errs() << "!! NewDT:\t" << BlockTy->getName() << " -> " << IDom->getName()
             << "\n   OldDT:\t" << BlockTy->getName() << " -> "
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
    if (!contains(&BB)) continue;

    // For every arc U -> V in the graph, NCA(U, V) = idoms[V] or V.
    for (auto *Succ : successors(&BB)) {
      if (!contains(Succ)) continue;
      // dbgs() << "Checking NCA(" << BB.getName() << ", " << Succ->getName() <<
      //          ")\n";

      auto NCA = findNCA(&BB, Succ);
      if (NCA != Succ && NCA != getIDom(Succ)) {
        Correct = false;
        DEBUG(dbgs() << "Error:\tNCA(" << BB.getName() << ", "
                     << Succ->getName() << ") = " << NCA->getName());
      }
    }
  }

  return Correct;
}

bool NewDomTree::verifyLevels() const {
  Function *F = root->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB) || &BB == root) continue;

    const Index BBL = getLevel(&BB);
    const auto IDom = getIDom(&BB);
    const Index IDomL = getLevel(IDom);
    if (BBL != (IDomL + 1)) {
      Correct = false;
      DEBUG(dbgs() << "Error:\tLevel(" << BB.getName() << ") = " << BBL << ", "
                   << "Level(" << IDom << ") = " << IDomL << "\n");
    }
  }

  return Correct;
}

bool NewDomTree::verifyReachability() const {
  bool Correct = true;

  auto DFSRes = runDFS(root, [] (BlockTy, BlockTy) { return true; });
  for (auto NodeToNum : DFSRes.nodeToNum)
    if (!contains(NodeToNum.first)) {
      errs() << "=================== Incorrect domtree! ===============\n";
      errs() << "DFS walk found a node not present in the DomTree "
             << NodeToNum.first->getName() << "\n";

      dumpIDoms(errs());
      Correct = false;
    }

  if (!Correct)
    DFSRes.dumpDFSNumbering(errs());

  return Correct;
}

bool NewDomTree::verifyParentProperty() const {
  bool Correct = true;
  for (auto NodeToIDom : idoms) {
    const BlockTy IDom = NodeToIDom.second;
    const BlockTy Target = NodeToIDom.first;

    if (IDom == root)
      continue;

    auto SkipIDom = [&] (BlockTy, BlockTy Succ) { return Succ != IDom; };
    auto DFSRes = runDFS(root, SkipIDom);
    if (DFSRes.nodeToNum.count(Target)) {
      errs() << "=================== Incorrect domtree! ===============\n";
      errs() << "DFS walk found a path from " << root->getName()
             << " to " << Target->getName() << " skipping its idom "
             << IDom->getName() << "\n";
      Target->getParent()->print(errs(), nullptr);

      print(errs());

      DFSRes.dumpDFSNumbering(errs());
      Correct = false;
      abort();
    }
  }

  return Correct;
}

bool NewDomTree::verifySiblingProperty() const {
  bool Correct = true;

  DenseMap<BlockTy, SmallVector<BlockTy, 8>> IDomToChildren;
  for (auto NodeToIDom : idoms)
    IDomToChildren[NodeToIDom.second].push_back(NodeToIDom.first);

  for (auto &ITC : IDomToChildren) {
    const auto& Siblings = ITC.second;
    for (auto N : Siblings) {
      for (auto S : Siblings) {
        if (S == N)
          continue;

        auto SkipSibling = [&](BlockTy, BlockTy Succ) { return Succ != S; };
        auto DFSRes = runDFS(root, SkipSibling);
        if (DFSRes.nodeToNum.count(N) == 0) {
          errs() << "=================== Incorrect domtree! ===============\n";
          errs() << "DFS walk didn't find a path from " << root->getName()
                 << " to " << N->getName() << " skipping its sibling "
                 << S->getName() << "\n";

          DFSRes.dumpDFSNumbering(errs());
          Correct = false;
        }
      }
    }
  }

  return Correct;
}

void NewDomTree::print(raw_ostream &OS) const {
  assert(!idoms.empty());
  std::set<BlockTy, NodeByName> ToPrint;
  ChildrenTy Children;

  if (!isInOutValid) recomputeInOutNums();

  for (const auto &NodeToIDom : idoms) {
    Children[NodeToIDom.second].push_back(NodeToIDom.first);
    ToPrint.insert(NodeToIDom.first);
  }

  OS << "\nNew Dominator Tree:\n";
  while (!ToPrint.empty()) printImpl(OS, root, Children, ToPrint);
  OS << "\n";
}

void NewDomTree::printImpl(raw_ostream &OS, BlockTy N, const ChildrenTy &Children,
                           std::set<BlockTy, NodeByName> &ToPrint) const {
  assert(isInOutValid);
  ToPrint.erase(N);
  const auto LevelIt = levels.find(N);
  assert(LevelIt != levels.end());
const auto Level = LevelIt->second;
  for (Index i = 0; i <= Level; ++i) OS << "  ";

  const auto InOutNumIt = inOutNums.find(N);
  assert(InOutNumIt != inOutNums.end());

  OS << '[' << (Level + 1) << "] %" << N->getName() << " {"
     << InOutNumIt->second.first << ", " << InOutNumIt->second.second << "}\n";

  const auto ChildrenIt = Children.find(N);
  if (ChildrenIt == Children.end()) return;

  std::vector<BlockTy> SortedChildren(ChildrenIt->second.begin(),
                                   ChildrenIt->second.end());
  std::sort(SortedChildren.begin(), SortedChildren.end());
  for (const auto &C : SortedChildren)
    if (ToPrint.count(C) != 0) printImpl(OS, C, Children, ToPrint);
}

void NewDomTree::DFSResult::dumpDFSNumbering(raw_ostream &OS) const {
  OS << "\nDFSNumbering:\n";
  OS << "\tnodeToNum size:\t" << nodeToNum.size() << "\n";
  OS << "\tparents size:\t" << parent.size() << "\n";

  using KeyValue = std::pair<BlockTy, Index>;
  std::vector<KeyValue> Sorted(nodeToNum.begin(), nodeToNum.end());

  sort(Sorted.begin(), Sorted.end(), [](KeyValue first, KeyValue second) {
    return first.second < second.second;
  });

  for (const auto &NodeToNum : Sorted)
    OS << NodeToNum.first->getName() << " {" << NodeToNum.second << "}\n";
}

void NewDomTree::dumpIDoms(raw_ostream &OS) const {
  OS << "BlockTy -> idom\n";
  for (auto NodeToIDom : idoms)
    OS << "\t" << NodeToIDom.first->getName() << " -> "
       << NodeToIDom.second->getName() << "\n";
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

    if (rdoms.count(BB) == 0) continue;

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
