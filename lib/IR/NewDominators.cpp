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

static cl::opt<bool, true>
    VerifyNewDomInfoX("verify-new-dom-info", cl::location(VerifyNewDomInfo),
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

template <typename T> static StringRef NameOrNullptrStr(T *V) {
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

void NewDomTree::semiNCA(DFSResult &DFS, const Index MinLevel,
                         DTNode *const AttachTo /* = nullptr */) {
  const Index NextDFSNum = static_cast<Index>(DFS.NumToNode.size());
  assert(NextDFSNum > 0 && "DFS not run?");

  DenseMap<BlockTy, SNCAInfo> SNCA;
  SNCA.reserve(NextDFSNum);
  const Index LastNum = NextDFSNum - 1;
  DEBUG(dbgs() << "StartNum: " << 0 << ": "
               << DFS.NumToNode.back()->getName() << "\n");
  DEBUG(dbgs() << "LastNum: " << LastNum << ": "
               << DFS.NumToNode.back()->getName() << "\n");

  // Step 0: initialize data structures.
  const BlockTy Root = DFS.NumToNode.front();
  DTNode *RootTreeNode = nullptr;
  for (Index i = 0; i <= LastNum; ++i) {
    auto N = DFS.NumToNode[i];
    DTNode *TreeN = getOrAddNode(N);
    if (N != Root)
      TreeN->IDom = getNode(DFS.NodeToInfo[N].Parent);
    else
      RootTreeNode = TreeN;

    TreeN->Children.clear();
    SNCA[N] = {N, N};
  }

  assert(RootTreeNode);

  if (AttachTo && RootTreeNode->IDom) {
    // Detach from previous idom.
    if (RootTreeNode->IDom->hasChild(RootTreeNode))
      RootTreeNode->IDom->removeChild(RootTreeNode);
  }

  RootTreeNode->IDom = RootTreeNode;
  if (Root == Entry || !AttachTo)
    RootTreeNode->Level = 0;
  else
    RootTreeNode->Level = AttachTo->Level + 1;

  // Step 1: compute semidominators.
  for (Index i = LastNum; i > 0; --i) {
    BlockTy CurrentNode = DFS.NumToNode[i];
    auto &CurrentNodeInfo = DFS.NodeToInfo[CurrentNode];
    auto &CurrentSNCAInfo = SNCA[CurrentNode];
    DTNode *CurrentTreeNode = getNode(CurrentNode);

    for (auto PredNode : CurrentNodeInfo.Predecessors) {
      if (PredNode == CurrentNode)
        continue;

      // Incoming arc from an unreachable node.
      if (DFS.NodeToInfo.count(PredNode) == 0)
        continue;

      if (getNode(PredNode)->Level < MinLevel)
        continue;

      BlockTy SDomCandidate =
          getSDomCandidate(CurrentNode, PredNode, DFS, SNCA);

      auto &CandidateInfo = SNCA[SDomCandidate];
      if (DFS.NodeToInfo[CurrentSNCAInfo.SDom].Num >
          DFS.NodeToInfo[CandidateInfo.SDom].Num) {
        CurrentSNCAInfo.SDom = CandidateInfo.SDom;
        CurrentTreeNode->RDom = getNode(SDomCandidate);
      }
    }
    // Update Label for the current Node.
    CurrentSNCAInfo.Label = CurrentSNCAInfo.SDom;
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i <= LastNum; ++i) {
    const BlockTy CurrentNode = DFS.NumToNode[i];
    DTNode *CurrentTreeNode = getNode(CurrentNode);
    const BlockTy SDom = SNCA[CurrentNode].SDom;
    DTNode *IDomCandidate = CurrentTreeNode->IDom;
    while (DFS.NodeToInfo[IDomCandidate->BB].Num > DFS.NodeToInfo[SDom].Num)
      IDomCandidate = IDomCandidate->IDom;

    CurrentTreeNode->IDom = IDomCandidate;
    DEBUG(dbgs() << "addChild(" << IDomCandidate->getName() << ", "
                 << CurrentNode->getName() << ")\n");
    DEBUG(dbgs().flush());
    IDomCandidate->addChild(CurrentTreeNode);
    CurrentTreeNode->Level = IDomCandidate->Level + 1;
  }

  DEBUG(dbgs() << "Entry " << Entry->getName() << "\n");
  if (!AttachTo)
    return;

  DEBUG(dbgs() << "Attaching Root " << RootTreeNode->getName() << " to "
               << AttachTo->getName() << "\n");

  if (RootTreeNode->IDom != AttachTo) {
    RootTreeNode->IDom = AttachTo;
    AttachTo->addChild(RootTreeNode);
  }

  RootTreeNode->RDom = AttachTo;
}

// Non-recursive union-find-based semidominator path walker.
NewDomTree::BlockTy
NewDomTree::getSDomCandidate(const BlockTy Start, const BlockTy Pred,
                             DFSResult &DFS,
                             DenseMap<BlockTy, SNCAInfo> &SNCA) {
  assert(Pred != Start && "Not a predecessor");
  const Index StartNum = DFS.NodeToInfo[Start].Num;
  const Index PredNum = DFS.NodeToInfo[Pred].Num;

  if (PredNum < StartNum)
    return Pred;

  BlockTy Next = Pred;
  DFSNodeInfo *NextInfo = &DFS.NodeToInfo[Next];
  SmallVector<BlockTy, 8> SDomPath;
  // Walk the SDom path up the spanning tree.
  do {
    SDomPath.push_back(Next);
    Next = NextInfo->Parent;
    NextInfo = &DFS.NodeToInfo[Next];
  } while (NextInfo->Num > StartNum);

  // Compress path.
  for (auto i = SDomPath.size() - 2; i < SDomPath.size(); --i) {
    const auto Current = SDomPath[i];
    const auto Parent = SDomPath[i + 1];

    if (DFS.NodeToInfo[SNCA[Current].Label].Num >
        DFS.NodeToInfo[SNCA[Parent].Label].Num)
      SNCA[Current].Label = SNCA[Parent].Label;

    DFS.NodeToInfo[Current].Parent = DFS.NodeToInfo[Parent].Parent;
  }

  return SNCA[Pred].Label;
}

DTNode *NewDomTree::addNode(BlockTy BB) {
  assert(!contains(BB));
  // make_unique not used because of the private ctor.
  auto &TN = (TreeNodes[BB] = std::unique_ptr<DTNode>(new DTNode(BB)));
  DEBUG(dbgs() << "New DTNode added " << TN->getName() << "\n");
  return TN.get();
}

DTNode *NewDomTree::getOrAddNode(BlockTy BB) {
  auto it = TreeNodes.find(BB);
  if (it != TreeNodes.end())
    return it->second.get();

  return addNode(BB);
}

void NewDomTree::computeReachableDominators(BlockTy Root, Index MinLevel) {
  auto LevelDescender = [MinLevel, this](BlockTy, BlockTy To) {
    return !contains(To) || getNode(To)->Level > MinLevel;
  };

  auto DFSRes = runDFS(Entry, LevelDescender);
  for (auto &NodeToInfo : DFSRes.NodeToInfo) {
    DEBUG(dbgs() << "Processing reachable Node -> preorder Parent arc:\n");
    DEBUG(dbgs() << "\t\t\t" << NameOrNullptrStr(NodeToInfo.first) << " -> "
                 << NameOrNullptrStr(NodeToInfo.second.Parent) << "\n");
    const auto Parent = NodeToInfo.second.Parent;
    if (Parent)
      getOrAddNode(NodeToInfo.first)->PreorderParent = getOrAddNode(Parent);
  }

  DEBUG(DFSRes.dumpDFSNumbering());

  semiNCA(DFSRes, MinLevel);
}

void NewDomTree::computeUnreachableDominators(
    BlockTy Root, DTNode *const Incoming,
    SmallVectorImpl<std::pair<BlockTy, DTNode *>> &DiscoveredConnectingArcs) {
  assert(!contains(Root));
  auto UnreachableDescender = [&DiscoveredConnectingArcs, this](BlockTy From,
                                                                BlockTy To) {
    // Arc unreachable -> reachable
    auto TNIt = TreeNodes.find(To);
    if (TNIt != TreeNodes.end()) {
      DiscoveredConnectingArcs.push_back({From, TNIt->second.get()});
      return false;
    }

    return true;
  };

  auto DFSRes = runDFS(Root, UnreachableDescender);
  for (auto &NodeToInfo : DFSRes.NodeToInfo) {
    const auto Parent = NodeToInfo.second.Parent;
    if (Parent)
      getOrAddNode(NodeToInfo.first)->PreorderParent = getOrAddNode(Parent);
  }

  DEBUG(DFSRes.dumpDFSNumbering());

  semiNCA(DFSRes, /* MinLevel = */ 0, Incoming);
}

bool NewDomTree::contains(BlockTy BB) const { return TreeNodes.count(BB) != 0; }

DTNode *NewDomTree::findNCA(DTNode *First, DTNode *Second) const {
  DTNode *const EntryTreeNode = getNode(Entry);
  if (First == EntryTreeNode || Second == EntryTreeNode)
    return EntryTreeNode;

  while (First != Second) {
    const Index LFirst = First->Level;
    const Index LSecond = Second->Level;

    if (LFirst < LSecond)
      std::swap(First, Second);

    First = First->IDom;
  }

  return First;
}

bool NewDomTree::dominates(DTNode *Src, DTNode *Dst) const {
  if (Dst->IDom == Src)
    return true;

  if (Src->IDom == Dst)
    return false;

  if (!isInOutValid)
    recomputeInOutNums();

  return Src->InNum <= Dst->InNum && Src->OutNum >= Dst->OutNum;
}

void NewDomTree::insertArc(BlockTy From, BlockTy To) {
  // Source unreachable. We don't want to maintain a forest, so we ignore
  // unreachable nodes.
  auto FromTNIt = TreeNodes.find(From);
  if (FromTNIt == TreeNodes.end())
    return;

  isInOutValid = false;

  auto ToTNIt = TreeNodes.find(To);
  // Connecting previously unreachable node.
  if (ToTNIt == TreeNodes.end())
    insertUnreachable(FromTNIt->second.get(), To);
  else // Both were reachable.
    insertReachable(FromTNIt->second.get(), ToTNIt->second.get());

  if (VerifyNewDomInfo && !verify(Verification::Basic))
    DEBUG(dbgs() << "Verification after insertion failed!\n");
}

void NewDomTree::insertUnreachable(DTNode *FromTN, BlockTy To) {
  assert(!contains(To));
  DEBUG(dbgs() << "Inserting " << FromTN->getName() << " -> (unreachable) "
               << To->getName() << "\n");

  SmallVector<std::pair<BlockTy, DTNode *>, 8> DiscoveredArcsToReachable;
  computeUnreachableDominators(To, FromTN, DiscoveredArcsToReachable);

  DEBUG(dbgs() << "Inserted " << FromTN->getName() << " -> (prev unreachable) "
               << To->getName() << "\n");
  DEBUG(dump());

  for (const auto &A : DiscoveredArcsToReachable)
    insertReachable(getNode(A.first), A.second);
}

void NewDomTree::insertReachable(DTNode *const FromTN, DTNode *const ToTN) {
  DTNode *const NCA = findNCA(FromTN, ToTN);
  DTNode *const ToIDom = ToTN->IDom;

  DEBUG(dbgs() << "Inserting a reachable arc: " << FromTN->getName() << " -> "
               << ToTN->getName() << "\n");

  // Nothing affected.
  if (NCA == ToTN || NCA == ToIDom)
    return;

  InsertionInfo II;
  DEBUG(dbgs() << "Marking " << ToTN->getName() << " affected\n");
  II.affected.insert(ToTN);
  const Index ToLevel = ToTN->Level;
  DEBUG(dbgs() << "Putting " << ToTN->getName() << " into bucket\n");
  II.bucket.push({ToLevel, ToTN});

  while (!II.bucket.empty()) {
    DTNode *const CurrentNode = II.bucket.top().second;
    II.bucket.pop();
    DEBUG(dbgs() << "\tAdding to visited and AQ: " << CurrentNode->getName()
                 << "\n");
    II.visited.insert(CurrentNode);
    II.affectedQueue.push_back(CurrentNode);

    visitInsertion(CurrentNode, CurrentNode->Level, NCA, II);
  }

  DEBUG(dbgs() << "IR: Almost end, entering update with NCA " << NCA->getName()
               << "\n");
  updateInsertion(NCA, II);

  DEBUG(dbgs() << "Clearing stuff\n");
  DEBUG(dump());
}

void NewDomTree::visitInsertion(DTNode *const TN, const Index RootLevel,
                                DTNode *const NCA, InsertionInfo &II) {
  const Index NCALevel = NCA->Level;
  DEBUG(dbgs() << "Visiting " << TN->getName() << "\n");

  for (const auto Succ : successors(TN->BB)) {
    DTNode *SuccTN = getNode(Succ);
    const Index SuccLevel = SuccTN->Level;
    DEBUG(dbgs() << "\tSuccessor " << Succ->getName()
                 << ", level = " << SuccLevel << "\n");
    // Succ dominated by subtree Entry -- not affected.
    if (SuccLevel > RootLevel) {
      DEBUG(dbgs() << "\t\tdominated by subtree Entry\n");
      if (II.visited.count(SuccTN) != 0)
        continue;

      DEBUG(dbgs() << "\t\tMarking visited not affected " << Succ->getName()
                   << "\n");
      II.visited.insert(SuccTN);
      II.visitedNotAffectedQueue.push_back(SuccTN);
      visitInsertion(SuccTN, RootLevel, NCA, II);
    } else if ((SuccLevel > NCALevel + 1) && II.affected.count(SuccTN) == 0) {
      DEBUG(dbgs() << "\t\tMarking affected and adding to bucket "
                   << Succ->getName() << "\n");
      II.affected.insert(SuccTN);
      II.bucket.push({SuccLevel, SuccTN});
    }
  }
}

void NewDomTree::updateInsertion(DTNode *NCA, InsertionInfo &II) {
  DEBUG(dbgs() << "Updating NCA = " << NCA->getName() << "\n");
  // Update idoms and start updating levels.
  for (DTNode *TN : II.affectedQueue) {
    DEBUG(dbgs() << "\tidoms[" << TN->getName() << "] = " << NCA->getName()
                 << "\n");
    TN->setIDom(NCA);
    DEBUG(dbgs() << "\tlevels[" << TN->getName() << "] = " << NCA->Level
                 << " + 1\n");

    TN->Level = NCA->Level + 1;
    TN->PreorderParent = nullptr;
  }

  DEBUG(dbgs() << "Before updating levels\n");
  updateLevels(II);
}

void NewDomTree::updateLevels(InsertionInfo &II) {
  DEBUG(dbgs() << "Updating levels\n");
  // Update levels of visited but not affected nodes;
  for (DTNode *TN : II.visitedNotAffectedQueue) {
    DEBUG(dbgs() << "\tlevels[" << TN->getName() << "] = levels["
                 << TN->IDom->getName() << "] + 1\n");
    TN->Level = TN->IDom->Level + 1;
  }
}

void NewDomTree::deleteArc(BlockTy From, BlockTy To) {
  DEBUG(dbgs() << "Deleting arc " << From->getName() << " -> " << To->getName()
               << "\n");
  // Deletion in unreachable subtree -- nothing to do.
  if (!contains(From))
    return;

  DTNode *const FromTN = getNode(From);
  DTNode *const ToTN = getNode(To);
  const auto NCA = findNCA(FromTN, ToTN);

  // To dominates From -- nothing to do.
  if (ToTN == NCA)
    return;

  isInOutValid = false;

  DTNode *const IDomTo = ToTN->IDom;
  DEBUG(dbgs() << "NCA " << NCA->getName() << ", IDomTo " << IDomTo->getName()
               << "\n");

  // To stays reachable.
  if (FromTN != IDomTo || isReachableFromIDom(ToTN))
    deleteReachable(FromTN, ToTN);
  else
    deleteUnreachable(ToTN);

  if (VerifyNewDomInfo && !verify(Verification::Basic)) {
    DEBUG(dbgs() << "Verification after deletion failed!\n");
    DEBUG(dbgs().flush());
  }
}

bool NewDomTree::isReachableFromIDom(DTNode *const TN) {
  for (auto *Succ : predecessors(TN->BB)) {
    // Incoming arc from an unreachable Node.
    if (!contains(Succ))
      continue;

    DTNode *const Support = findNCA(TN, getNode(Succ));
    if (Support != TN) {
      DEBUG(dbgs() << "\tIsReachable " << TN->getName()
                   << " from support = " << Succ->getName() << "\n");
      return true;
    }
  }

  return false;
}

void NewDomTree::deleteReachable(DTNode *const FromTN, DTNode *const ToTN) {
  if (ToTN->PreorderParent && FromTN != ToTN->PreorderParent) {
    assert(ToTN->RDom);
    if (ToTN->RDom != FromTN)
      return;
  }

  DEBUG(dbgs() << "Subtree needs to be rebuilt\n");
  DTNode *const IDomTo = ToTN->IDom;
  DTNode *const PrevIDomSubTree = IDomTo->IDom;
  const Index Level = IDomTo->Level;
  auto DescendBelow = [Level, this](BlockTy, BlockTy To) {
    return getNode(To)->Level > Level;
  };

  DEBUG(dbgs() << "Top of subtree: " << IDomTo->getName() << " [" << Level
               << "]\n");

  auto DFSRes = runDFS(IDomTo->BB, DescendBelow);
  DEBUG(DFSRes.dumpDFSNumbering());
  for (auto &NodeToInfo : DFSRes.NodeToInfo) {
    const auto Parent = NodeToInfo.second.Parent;
    if (Parent)
      getOrAddNode(NodeToInfo.first)->PreorderParent = getOrAddNode(Parent);
  }
  DEBUG(dbgs() << "Running SNCA\n");
  semiNCA(DFSRes, Level, PrevIDomSubTree);
}

void NewDomTree::deleteUnreachable(DTNode *const ToTN) {
  DEBUG(dbgs() << "Deleting unreachable " << ToTN->getName() << "\n");

  SmallVector<BlockTy, 8> affectedQueue;
  SmallDenseSet<BlockTy, 8> affected;

  const Index Level = ToTN->Level;
  auto DescendCollect = [Level, &affectedQueue, &affected, this](BlockTy,
                                                                 BlockTy To) {
    if (getNode(To)->Level > Level)
      return true;
    if (affected.count(To) == 0) {
      affected.insert(To);
      affectedQueue.push_back(To);
    }
    return false;
  };

  auto DFSRes = runDFS(ToTN->BB, DescendCollect);
  DEBUG(DFSRes.dumpDFSNumbering());
  DTNode *MinNode = ToTN;

  for (const BlockTy N : affectedQueue) {
    DTNode *const TN = getNode(N);
    DTNode *NCA = findNCA(TN, ToTN);
    if (NCA != TN && NCA->Level < MinNode->Level)
      MinNode = NCA;
  }

  const Index Size = static_cast<Index>(DFSRes.NumToNode.size());
  for (Index i = Size - 1; i < Size; --i) {
    const BlockTy N = DFSRes.NumToNode[i];
    DTNode *const TN = getNode(N);
    DEBUG(dbgs() << "Erasing node info " << N->getName() << " (level "
                 << TN->Level << ", idom " << TN->IDom->getName() << ")\n");

    eraseNode(TN); // TODO: Should we keep it around for the TN not to
                   // reappear under a different address?
  }

  if (MinNode == ToTN)
    return;

  DEBUG(dbgs() << "DeleteUnreachable: running SNCA(MinNode = "
               << MinNode->getName() << ")\n");
  const Index MinLevel = MinNode->Level;
  DTNode *const PrevIDomMin = MinNode->IDom;
  DFSRes = runDFS(MinNode->BB, [MinLevel, this](BlockTy, BlockTy To) {
    return contains(To) && getNode(To)->Level > MinLevel;
  });

  DEBUG(DFSRes.dumpDFSNumbering());
  DEBUG(dbgs() << "Previous idoms[MinNode] = " << PrevIDomMin->getName()
               << "\n");
  semiNCA(DFSRes, MinLevel, PrevIDomMin);
}

void NewDomTree::eraseNode(DTNode *TN) {
  assert(TN->getNumChildren() == 0);
  TN->IDom->removeChild(TN);
  TreeNodes.erase(TN->BB);
}

void NewDomTree::replaceWith(DTNode *Replace, DTNode *With) {
  for (auto &BlockToTN : TreeNodes) {
    auto *TN = BlockToTN.second.get();
    if (TN->IDom == Replace)
      TN->IDom = With;
    if (TN->RDom == Replace)
      TN->RDom = With;
    if (TN->PreorderParent == Replace)
      TN->PreorderParent = With;
  }

  if (getNode(Entry) == Replace)
    Entry = With->BB;

  eraseNode(Replace);
  for (auto *C : *With)
    updateLevels(C);
  isInOutValid = false;
}

void NewDomTree::updateLevels(DTNode *Start) {
  SmallVector<DTNode *, 64> WorkList = {Start};

  while (!WorkList.empty()) {
    DTNode *CurrentTN = WorkList.pop_back_val();

    CurrentTN->Level = CurrentTN->IDom->Level + 1;
    for (DTNode *C : *CurrentTN)
      WorkList.push_back(C);
  }
}

void NewDomTree::recomputeInOutNums() const {
  using PairT = PointerIntPair<DTNode *, 1, bool>;
  SmallVector<PairT, 64> WorkList = {{getNode(Entry), false}};

  Index NextNum = 0;
  while (!WorkList.empty()) {
    PairT &Current = WorkList.back();
    DTNode *CurrentTN = Current.getPointer();

    if (Current.getInt()) {
      WorkList.pop_back();
      CurrentTN->OutNum = NextNum++;
      continue;
    }

    CurrentTN->InNum = NextNum++;
    Current.setInt(true);
    for (DTNode *C : *CurrentTN)
      WorkList.push_back({C, false});
  }

  isInOutValid = true;
}

void NewDomTree::toOldDT(DominatorTree &DT) const {
  DominatorTree Temp;
  Temp.setNewRoot(Entry);

  std::vector<std::pair<Index, DTNode *>> LevelsNodes;
  LevelsNodes.reserve(TreeNodes.size());

  for (auto &TN : TreeNodes)
    LevelsNodes.push_back({TN.second->Level, TN.second.get()});

  std::sort(LevelsNodes.begin(), LevelsNodes.end());

  for (auto LN : LevelsNodes)
    if (LN.second->BB != Entry)
      Temp.addNewBlock(LN.second->BB, LN.second->IDom->BB);

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
  assert(Entry);
  assert(!TreeNodes.empty());

  DominatorTree DT(*Entry->getParent());
  bool Correct = true;

  for (const auto &BlockToNode : TreeNodes) {
    if (BlockToNode.first == Entry)
      continue;

    auto Node = BlockToNode.first;
    auto IDom = BlockToNode.second->IDom->BB;
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
  Function *F = Entry->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB))
      continue;

    // For every arc U -> V in the graph, NCA(U, V) = idoms[V] or V.
    for (auto *Succ : successors(&BB)) {
      if (!contains(Succ))
        continue;
      // dbgs() << "Checking NCA(" << BB.getName() << ", " << Succ->getName() <<
      //          ")\n";

      DTNode *const SuccTN = getNode(Succ);
      auto NCA = findNCA(getNode(&BB), SuccTN);
      if (NCA != SuccTN && NCA != SuccTN->IDom) {
        Correct = false;
        DEBUG(dbgs() << "Error:\tNCA(" << BB.getName() << ", "
                     << Succ->getName() << ") = " << NCA->getName());
      }
    }
  }

  return Correct;
}

bool NewDomTree::verifyLevels() const {
  Function *F = Entry->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB) || &BB == Entry)
      continue;

    const auto TN = getNode(&BB);
    const Index BBL = TN->Level;
    const auto IDom = TN->IDom;
    const Index IDomL = IDom->Level;
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

  auto DFSRes = runDFS(Entry, [](BlockTy, BlockTy) { return true; });
  for (auto NodeToInfo : DFSRes.NodeToInfo)
    if (!contains(NodeToInfo.first)) {
      errs() << "=================== Incorrect domtree! ===============\n";
      errs() << "DFS walk found a node not present in the DomTree "
             << NodeToInfo.first->getName() << "\n";

      dumpIDoms(errs());
      Correct = false;
    }

  if (!Correct)
    DFSRes.dumpDFSNumbering(errs());

  return Correct;
}

bool NewDomTree::verifyParentProperty() const {
  bool Correct = true;
  for (const auto &BlockToNode : TreeNodes) {
    const auto IDom = BlockToNode.second->IDom->BB;
    const auto Target = BlockToNode.first;

    if (IDom == Entry)
      continue;

    auto SkipIDom = [&](BlockTy, BlockTy Succ) { return Succ != IDom; };
    auto DFSRes = runDFS(Entry, SkipIDom);
    if (DFSRes.NodeToInfo.count(Target)) {
      errs() << "=================== Incorrect domtree! ===============\n";
      errs() << "DFS walk found a path from " << Entry->getName() << " to "
             << Target->getName() << " skipping its idom " << IDom->getName()
             << "\n";
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

  for (auto &BlockToNode : TreeNodes) {
    const auto &Siblings = BlockToNode.second->Children;
    for (const auto &N : Siblings) {
      for (const auto &S : Siblings) {
        if (S == N)
          continue;

        auto SkipSibling = [&](BlockTy, BlockTy Succ) { return Succ != S->BB; };
        auto DFSRes = runDFS(Entry, SkipSibling);
        if (DFSRes.NodeToInfo.count(N->BB) == 0) {
          errs() << "=================== Incorrect domtree! ===============\n";
          errs() << "DFS walk didn't find a path from " << Entry->getName()
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
  assert(!TreeNodes.empty());
  OS << "\nNew Dominator Tree:\n";
  if (!isInOutValid)
    recomputeInOutNums();

  printImpl(OS, getNode(Entry));
}

void NewDomTree::printImpl(raw_ostream &OS, const DTNode *TN) const {
  for (Index i = 0; i <= TN->Level; ++i)
    OS << "  ";
  OS << '[' << (TN->Level + 1) << "] %" << TN->getName() << " {" << TN->InNum
     << ", " << TN->OutNum << "}\n";

  SmallVector<DTNode *, 8> Ch(TN->begin(), TN->end());
  std::sort(Ch.begin(), Ch.end(),
            [](DTNode *F, DTNode *S) { return F->getInNum() < S->getInNum(); });

  for (auto C : Ch)
    printImpl(OS, C);
}

void NewDomTree::DFSResult::dumpDFSNumbering(raw_ostream &OS) const {
  OS << "\nDFSNumbering:\n";
  OS << "\tNodeToInfo size:\t" << NodeToInfo.size() << "\n";

  using KeyValue = std::pair<BlockTy, DFSNodeInfo>;
  std::vector<KeyValue> Sorted(NodeToInfo.begin(), NodeToInfo.end());

  sort(Sorted.begin(), Sorted.end(), [](KeyValue first, KeyValue second) {
    return first.second.Num < second.second.Num;
  });

  for (const auto &NodeToInfo : Sorted)
    OS << NodeToInfo.first->getName() << " {" << NodeToInfo.second.Num << "}\n";
}

void NewDomTree::dumpIDoms(raw_ostream &OS) const {
  OS << "Node -> idom\n";
  for (const auto &BlockToNode : TreeNodes)
    OS << "\t" << BlockToNode.first->getName() << " -> "
       << BlockToNode.second->IDom->getName() << "\n";
}

void NewDomTree::addDebugInfoToIR() {
  auto M = Entry->getParent()->getParent();
  auto *IntTy = IntegerType::get(M->getContext(), 1);

  for (const auto &BlockToNode : TreeNodes) {
    auto BB = BlockToNode.first;
    auto ID = BlockToNode.second->IDom->BB;

    std::string Buffer;
    raw_string_ostream RSO(Buffer);
    IRBuilder<> Builder(BB, BB->begin());

    RSO << "idom___" << ID->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
    Buffer.clear();

    auto RD = BlockToNode.second->RDom;
    if (!RD)
      continue;

    RSO << "rdom___" << RD->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
  }
}

void NewDomTree::dumpLegacyDomTree() const {
  DominatorTree DT(*Entry->getParent());
  DT.print(dbgs());
}
