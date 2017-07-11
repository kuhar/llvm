//===- GenericDomTreeConstruction.h - Dominator Calculation ------*- C++ -*-==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
/// \file
///
/// Generic dominator tree construction - This file provides routines to
/// construct immediate dominator information for a flow-graph based on the
/// Semi-NCA algorithm described in this dissertation:
///
///   Linear-Time Algorithms for Dominators and Related Problems
///   Loukas Georgiadis, Princeton University, November 2005, pp. 21-23:
///   ftp://ftp.cs.princeton.edu/reports/2005/737.pdf
///
/// This implements the O(n*log(n)) versions of EVAL and LINK, because it turns
/// out that the theoretically slower O(n*log(n)) implementation is actually
/// faster than the almost-linear O(n*alpha(n)) version, even for large CFGs.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_SUPPORT_GENERICDOMTREECONSTRUCTION_H
#define LLVM_SUPPORT_GENERICDOMTREECONSTRUCTION_H

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/GenericDomTree.h"
#include <queue>

#define DTB_DEBUG_TYPE "dom-tree-builder"
#define DTB_DEBUG(Arg) DEBUG_WITH_TYPE(DTB_DEBUG_TYPE, Arg)

namespace llvm {
namespace DomTreeBuilder {

template <typename NodePtr, bool Inverse>
struct ChildrenGetter {
  static auto Get(NodePtr N) -> decltype(reverse(children<NodePtr>(N))) {
    return reverse(children<NodePtr>(N));
  }
};

template <typename NodePtr>
struct ChildrenGetter<NodePtr, true> {
  static auto Get(NodePtr N) -> decltype(inverse_children<NodePtr>(N)) {
    return inverse_children<NodePtr>(N);
  }
};

// Information record used by Semi-NCA during tree construction.
template <typename DomTreeT>
struct SemiNCAInfo {
  using NodePtr = typename DomTreeT::NodePtr;
  using NodeT = typename DomTreeT::NodeType;
  using TreeNodePtr = DomTreeNodeBase<NodeT> *;
  static constexpr bool IsPostDom = DomTreeT::IsPostDominators;

  struct InfoRec {
    unsigned DFSNum = 0;
    unsigned Parent = 0;
    unsigned Semi = 0;
    NodePtr Label = nullptr;
    NodePtr IDom = nullptr;
    SmallVector<NodePtr, 2> ReverseChildren;
  };

  std::vector<NodePtr> NumToNode = {nullptr};
  DenseMap<NodePtr, InfoRec> NodeToInfo;

  void clear() {
    NumToNode = {nullptr};
    NodeToInfo.clear();
  }

  NodePtr getIDom(NodePtr BB) const {
    auto InfoIt = NodeToInfo.find(BB);
    if (InfoIt == NodeToInfo.end()) return nullptr;

    return InfoIt->second.IDom;
  }

  TreeNodePtr getNodeForBlock(NodePtr BB, DomTreeT &DT) {
    if (TreeNodePtr Node = DT.getNode(BB)) return Node;

    // Haven't calculated this node yet?  Get or calculate the node for the
    // immediate dominator.
    NodePtr IDom = getIDom(BB);

    assert(IDom || DT.DomTreeNodes[nullptr]);
    TreeNodePtr IDomNode = getNodeForBlock(IDom, DT);

    // Add a new tree node for this NodeT, and link it as a child of
    // IDomNode
    return (DT.DomTreeNodes[BB] = IDomNode->addChild(
                llvm::make_unique<DomTreeNodeBase<NodeT>>(BB, IDomNode)))
        .get();
  }

  static bool AlwaysDescend(NodePtr, NodePtr) { return true; }

  // Custom DFS implementation which can skip nodes based on a provided
  // predicate. It also collects ReverseChildren so that we don't have to spend
  // time getting predecessors in SemiNCA.
  template <bool Inverse, typename DescendCondition>
  unsigned runDFS(NodePtr V, unsigned LastNum, DescendCondition Condition,
                  unsigned AttachToNum) {
    assert(V);
    SmallVector<NodePtr, 64> WorkList = {V};
    if (NodeToInfo.count(V) != 0) NodeToInfo[V].Parent = AttachToNum;

    while (!WorkList.empty()) {
      const NodePtr BB = WorkList.pop_back_val();
      auto &BBInfo = NodeToInfo[BB];

      // Visited nodes always have positive DFS numbers.
      if (BBInfo.DFSNum != 0) continue;
      BBInfo.DFSNum = BBInfo.Semi = ++LastNum;
      BBInfo.Label = BB;
      NumToNode.push_back(BB);

      for (const NodePtr Succ : ChildrenGetter<NodePtr, Inverse>::Get(BB)) {
        const auto SIT = NodeToInfo.find(Succ);
        // Don't visit nodes more than once but remember to collect
        // RerverseChildren.
        if (SIT != NodeToInfo.end() && SIT->second.DFSNum != 0) {
          if (Succ != BB) SIT->second.ReverseChildren.push_back(BB);
          continue;
        }

        if (!Condition(BB, Succ)) continue;

        // It's fine to add Succ to the map, because we know that it will be
        // visited later.
        auto &SuccInfo = NodeToInfo[Succ];
        WorkList.push_back(Succ);
        SuccInfo.Parent = LastNum;
        SuccInfo.ReverseChildren.push_back(BB);
      }
    }

    return LastNum;
  };

  NodePtr eval(NodePtr VIn, unsigned LastLinked) {
    auto &VInInfo = NodeToInfo[VIn];
    if (VInInfo.DFSNum < LastLinked)
      return VIn;

    SmallVector<NodePtr, 32> Work;
    SmallPtrSet<NodePtr, 32> Visited;

    if (VInInfo.Parent >= LastLinked)
      Work.push_back(VIn);

    while (!Work.empty()) {
      NodePtr V = Work.back();
      auto &VInfo = NodeToInfo[V];
      NodePtr VAncestor = NumToNode[VInfo.Parent];

      // Process Ancestor first
      if (Visited.insert(VAncestor).second && VInfo.Parent >= LastLinked) {
        Work.push_back(VAncestor);
        continue;
      }
      Work.pop_back();

      // Update VInfo based on Ancestor info
      if (VInfo.Parent < LastLinked)
        continue;

      auto &VAInfo = NodeToInfo[VAncestor];
      NodePtr VAncestorLabel = VAInfo.Label;
      NodePtr VLabel = VInfo.Label;
      if (NodeToInfo[VAncestorLabel].Semi < NodeToInfo[VLabel].Semi)
        VInfo.Label = VAncestorLabel;
      VInfo.Parent = VAInfo.Parent;
    }

    return VInInfo.Label;
  }

  void runSemiNCA(DomTreeT &DT, const unsigned MinLevel = 0) {
    const unsigned NextDFSNum(NumToNode.size());
    // Initialize IDoms to spanning tree parents.
    for (unsigned i = 1; i < NextDFSNum; ++i) {
      const NodePtr V = NumToNode[i];
      auto &VInfo = NodeToInfo[V];
      VInfo.IDom = NumToNode[VInfo.Parent];
    }

    // Step #1: Calculate the semidominators of all vertices.
    for (unsigned i = NextDFSNum - 1; i >= 2; --i) {
      NodePtr W = NumToNode[i];
      auto &WInfo = NodeToInfo[W];

      // Initialize the semi dominator to point to the parent node.
      WInfo.Semi = WInfo.Parent;
      for (const auto &N : WInfo.ReverseChildren) {
        if (NodeToInfo.count(N) == 0)  // Skip unreachable predecessors.
          continue;

        const TreeNodePtr TN = DT.getNode(N);
        if (TN && TN->getLevel() < MinLevel)  // Skip too shallow predecessors.
          continue;

        unsigned SemiU = NodeToInfo[eval(N, i + 1)].Semi;
        if (SemiU < WInfo.Semi) WInfo.Semi = SemiU;
      }
    }

    // Step #2: Explicitly define the immediate dominator of each vertex.
    //          IDom[i] = NCA(SDom[i], SpanningTreeParent(i)).
    // Note that the parents were stored in IDoms and later got invalidated
    // during path compression in Eval.
    for (unsigned i = 2; i < NextDFSNum; ++i) {
      const NodePtr W = NumToNode[i];
      auto &WInfo = NodeToInfo[W];
      const unsigned SDomNum = NodeToInfo[NumToNode[WInfo.Semi]].DFSNum;
      NodePtr WIDomCandidate = WInfo.IDom;
      while (NodeToInfo[WIDomCandidate].DFSNum > SDomNum)
        WIDomCandidate = NodeToInfo[WIDomCandidate].IDom;

      WInfo.IDom = WIDomCandidate;
    }
  }

  template <typename DescendCondition>
  unsigned doFullDFSWalk(const DomTreeT &DT, DescendCondition DC) {
    unsigned Num = 0;

    if (DT.Roots.size() > 1) {
      auto &BBInfo = NodeToInfo[nullptr];
      BBInfo.DFSNum = BBInfo.Semi = ++Num;
      BBInfo.Label = nullptr;

      NumToNode.push_back(nullptr);  // NumToNode[n] = V;
    }

    if (DT.isPostDominator()) {
      for (auto *Root : DT.Roots) Num = runDFS<true>(Root, Num, DC, 1);
    } else {
      assert(DT.Roots.size() == 1);
      Num = runDFS<false>(DT.Roots[0], Num, DC, Num);
    }

    return Num;
  }

  void calculateFromScratch(DomTreeT &DT, const unsigned NumBlocks) {
    // Step #0: Number blocks in depth-first order and initialize variables used
    // in later stages of the algorithm.
    const unsigned LastDFSNum = doFullDFSWalk(DT, AlwaysDescend);

    runSemiNCA(DT);

    if (DT.Roots.empty()) return;

    // Add a node for the root.  This node might be the actual root, if there is
    // one exit block, or it may be the virtual exit (denoted by
    // (BasicBlock *)0) which postdominates all real exits if there are multiple
    // exit blocks, or an infinite loop.
    // It might be that some blocks did not get a DFS number (e.g., blocks of
    // infinite loops). In these cases an artificial exit node is required.
    const bool MultipleRoots = DT.Roots.size() > 1 || (DT.isPostDominator() &&
                                                       LastDFSNum != NumBlocks);
    NodePtr Root = !MultipleRoots ? DT.Roots[0] : nullptr;

    DT.RootNode = (DT.DomTreeNodes[Root] =
                       llvm::make_unique<DomTreeNodeBase<NodeT>>(Root, nullptr))
                      .get();
    attachNewSubtree(DT, DT.RootNode);
  }

  void attachNewSubtree(DomTreeT& DT, const TreeNodePtr AttachTo) {
    // Attach the first unreachable block to AttachTo.
    NodeToInfo[NumToNode[1]].IDom = AttachTo->getBlock();
    // Loop over all of the discovered blocks in the function...
    for (size_t i = 1, e = NumToNode.size(); i != e; ++i) {
      NodePtr W = NumToNode[i];
      DTB_DEBUG(dbgs() << "\tdiscovereed ureachable node " << BlockPrinter(W)
                       << "\n");

      // Don't replace this with 'count', the insertion side effect is important
      if (DT.DomTreeNodes[W]) continue;  // Haven't calculated this node yet?

      NodePtr ImmDom = getIDom(W);

      // Get or calculate the node for the immediate dominator
      TreeNodePtr IDomNode = getNodeForBlock(ImmDom, DT);

      // Add a new tree node for this BasicBlock, and link it as a child of
      // IDomNode
      DT.DomTreeNodes[W] = IDomNode->addChild(
          llvm::make_unique<DomTreeNodeBase<NodeT>>(W, IDomNode));
    }
  }

  void reattachExistingSubtree(DomTreeT& DT, const TreeNodePtr AttachTo) {
    NodeToInfo[NumToNode[1]].IDom = AttachTo->getBlock();
    for (size_t i = 1, e = NumToNode.size(); i != e; ++i) {
      const NodePtr N = NumToNode[i];
      const TreeNodePtr TN = DT.getNode(N);
      assert(TN);
      const TreeNodePtr NewIDom = DT.getNode(NodeToInfo[N].IDom);
      TN->setIDom(NewIDom);
    }
  }

  struct BlockPrinter {
    NodePtr N;

    BlockPrinter(NodePtr Block) : N(Block) {}
    BlockPrinter(TreeNodePtr TN) : N(TN ? TN->getBlock() : nullptr) {}

    friend raw_ostream &operator<<(raw_ostream &O, const BlockPrinter &BP) {
      if (!BP.N)
        O << "nullptr";
      else
        BP.N->printAsOperand(O, false);

      return O;
    }
  };

  struct InsertionInfo {
    using BucketElementTy = std::pair<unsigned, TreeNodePtr>;
    struct DecreasingLevel {
      bool operator()(const BucketElementTy &First,
                      const BucketElementTy &Second) const {
        return First.first > Second.first;
      }
    };

    std::priority_queue<BucketElementTy, SmallVector<BucketElementTy, 8>,
        DecreasingLevel>
        Bucket;
    DenseSet<TreeNodePtr> Affected;
    DenseSet<TreeNodePtr> Visited;
    SmallVector<TreeNodePtr, 8> AffectedQueue;
    SmallVector<TreeNodePtr, 8> VisitedNotAffectedQueue;
  };

  static void InsertEdge(DomTreeT &DT, const NodePtr From, const NodePtr To) {
    assert(From && To && "Cannot connect nullptrs");
    DTB_DEBUG(dbgs() << "Inserting edge " << BlockPrinter(From) << " -> "
                 << BlockPrinter(To) << "\n");
    const TreeNodePtr FromTN = DT.getNode(From);

    // Ignore egdes from unreachable nodes.
    if (!FromTN)
      return;

    DT.DFSInfoValid = false;

    const TreeNodePtr ToTN = DT.getNode(To);
    if (!ToTN)
      InsertUnreachable(DT, FromTN, To);
    else
      InsertReachable(DT, FromTN, ToTN);
  }

  static void InsertReachable(DomTreeT &DT, const TreeNodePtr From,
                              const TreeNodePtr To) {
    DTB_DEBUG(dbgs() << "\tReachable " << BlockPrinter(From->getBlock())
                    << " -> " << BlockPrinter(To->getBlock()) << "\n");
    const NodePtr NCDBlock = DT.findNearestCommonDominator(From->getBlock(),
                                                               To->getBlock());
    assert(NCDBlock);
    const TreeNodePtr NCD = DT.getNode(NCDBlock);
    assert(NCD);

    DTB_DEBUG(dbgs() << "\t\tNCA == " << BlockPrinter(NCD) << "\n");
    const TreeNodePtr ToIDom = To->getIDom();

    assert(NCD);
    // Nothing affected.
    if (NCD == To || NCD == ToIDom)
      return;

    InsertionInfo II;
    DTB_DEBUG(dbgs() << "Marking " << BlockPrinter(To) << " as affected\n");
    II.Affected.insert(To);
    const unsigned ToLevel = To->getLevel();
    DTB_DEBUG(dbgs() << "Putting " << BlockPrinter(To) << " into a Bucket\n");
    II.Bucket.push({ToLevel, To});

    while (!II.Bucket.empty()) {
      const TreeNodePtr CurrentNode = II.Bucket.top().second;
      II.Bucket.pop();
      DTB_DEBUG(dbgs() << "\tAdding to Visited and AffectedQueue: "
                       << BlockPrinter(CurrentNode) << "\n");
      II.Visited.insert(CurrentNode);
      II.AffectedQueue.push_back(CurrentNode);

      VisitInsertion(DT, CurrentNode, ToLevel, NCD, II);
    }

    UpdateInsertion(DT, NCD, II);
  }

  static void VisitInsertion(DomTreeT &DT, const TreeNodePtr TN,
                             const unsigned RootLevel, const TreeNodePtr NCD,
                             InsertionInfo &II) {
    const unsigned NCDLevel = NCD->getLevel();
    DTB_DEBUG(dbgs() << "Visiting " << BlockPrinter(TN) << "\n");

    assert(TN->getBlock());
    for (const NodePtr Succ :
         ChildrenGetter<NodePtr, IsPostDom>::Get(TN->getBlock())) {
      const TreeNodePtr SuccTN = DT.getNode(Succ);
      assert(SuccTN && "Unreachable successor found at reachable insertion");
      const unsigned SuccLevel = SuccTN->getLevel();

      DTB_DEBUG(dbgs() << "\tSuccessor " << BlockPrinter(Succ) << ", level = "
                       << SuccLevel << "\n");

      // Succ dominated by subtree From -- not affected.
      if (SuccLevel > RootLevel) {
        DTB_DEBUG(dbgs() << "\t\tDominated by subtree From\n");
        if (II.Visited.count(SuccTN) != 0)
          continue;

        DTB_DEBUG(dbgs() << "\t\tMarking visited not affected "
                         << BlockPrinter(Succ) << "\n");
        II.Visited.insert(SuccTN);
        II.VisitedNotAffectedQueue.push_back(SuccTN);
        VisitInsertion(DT, SuccTN, RootLevel, NCD, II);
      } else if ((SuccLevel > NCDLevel + 1) && II.Affected.count(SuccTN) == 0) {
        DTB_DEBUG(dbgs() << "\t\tMarking affected and adding "
                         << BlockPrinter(Succ) << " to a Bucket\n");
        II.Affected.insert(SuccTN);
        II.Bucket.push({SuccLevel, SuccTN});
      }
    }
  }

  static void UpdateInsertion(DomTreeT &DT, const TreeNodePtr NCD,
                              InsertionInfo &II) {
    DTB_DEBUG(dbgs() << "Updating NCD = " << BlockPrinter(NCD) << "\n");

    for (const TreeNodePtr TN : II.AffectedQueue) {
      DTB_DEBUG(dbgs() << "\tIDom(" << BlockPrinter(TN) << ") = "
                       << BlockPrinter(NCD) << "\n");
      TN->setIDom(NCD);
    }

    UpdateLevelsAfterInsertion(II);
  }

  static void UpdateLevelsAfterInsertion(InsertionInfo &II) {
    DTB_DEBUG(dbgs() << "Updating levels for visited but not affected nodes\n");

    for (const TreeNodePtr TN: II.VisitedNotAffectedQueue) {
      DTB_DEBUG(dbgs() << "\tlevel(" << BlockPrinter(TN) << ") = ("
                       << BlockPrinter(TN->getIDom()) << ") "
                       << TN->getIDom()->getLevel() << " + 1\n");
      TN->UpdateLevel();
    }
  }

  static void ComputeUnreachableDominators(
      DomTreeT &DT, const NodePtr Root, const TreeNodePtr Incoming,
      SmallVectorImpl<std::pair<NodePtr, TreeNodePtr>>
          &DiscoveredConnectingEdges) {
    assert(!DT.getNode(Root) && "Root must not be reachable");

    auto UnreachableDescender = [&DT, &DiscoveredConnectingEdges](NodePtr From,
                                                                  NodePtr To) {
      const TreeNodePtr ToTN = DT.getNode(To);
      if (!ToTN) return true;

      DiscoveredConnectingEdges.push_back({From, ToTN});
      return false;
    };

    SemiNCAInfo SNCA;
    SNCA.runDFS<IsPostDom>(Root, 0, UnreachableDescender, 0);
    SNCA.runSemiNCA(DT);
    SNCA.attachNewSubtree(DT, Incoming);

    DTB_DEBUG(dbgs() << "After adding unreachable nodes\n");
    DTB_DEBUG(DT.print(dbgs()));
  }

  static void InsertUnreachable(DomTreeT &DT, const TreeNodePtr From,
                                const NodePtr To) {
    DTB_DEBUG(dbgs() << "Inserting " << BlockPrinter(From)
                     << " -> (unreachable) " << BlockPrinter(To) << "\n");

    SmallVector<std::pair<NodePtr, TreeNodePtr>, 8> DiscoveredEdgesToReachable;
    ComputeUnreachableDominators(DT, To, From, DiscoveredEdgesToReachable);

    DTB_DEBUG(dbgs() << "Inserted " << BlockPrinter(From)
                     << " -> (prev unreachable) " << BlockPrinter(To) << "\n");

    DTB_DEBUG(DT.print(dbgs()));

    for (const auto &Edge : DiscoveredEdgesToReachable) {
      DTB_DEBUG(dbgs() << "\tInserting discovered connecting edge "
                       << BlockPrinter(Edge.first) << " -> "
                       << BlockPrinter(Edge.second) << "\n");
      InsertReachable(DT, DT.getNode(Edge.first), Edge.second);
    }
  }

  static void DeleteEdge(DomTreeT &DT, const NodePtr From, const NodePtr To) {
    assert(From && To && "Cannot disconnect nullptrs");
    DTB_DEBUG(dbgs() << "Deleting edge " << BlockPrinter(From) << " -> "
                     << BlockPrinter(To) << "\n");
    const TreeNodePtr FromTN = DT.getNode(From);
    // Deletion in an unreachable subtree -- nothing to do.
    if (!FromTN) return;

    const TreeNodePtr ToTN = DT.getNode(To);
    const NodePtr NCDBlock = DT.findNearestCommonDominator(From, To);
    const TreeNodePtr NCD = NCDBlock ? DT.getNode(NCDBlock) : nullptr;

    // To dominates From -- nothing to do.
    if (ToTN == NCD) return;

    const TreeNodePtr ToIDom = ToTN->getIDom();
    DTB_DEBUG(dbgs() << "\tNCD" << BlockPrinter(NCD) << ", ToIDom "
                     << BlockPrinter(ToIDom) << "\n");

    if (FromTN != ToIDom || IsReachableFromIDom(DT, ToTN))
      DeleteReachable(DT, FromTN, ToTN);
    else
      DeleteUnreachable(DT, ToTN);
  }

  static void DeleteReachable(DomTreeT &DT, const TreeNodePtr FromTN,
                              const TreeNodePtr ToTN) {
    DTB_DEBUG(dbgs() << "Deleting reachable " << BlockPrinter(FromTN) << " -> "
                     << BlockPrinter(ToTN) << "\n");
    DTB_DEBUG(dbgs() << "\tRebuilding subtree\n");

    const NodePtr ToIDom =
        DT.findNearestCommonDominator(FromTN->getBlock(), ToTN->getBlock());
    assert(ToIDom);
    const TreeNodePtr ToIDomTN = DT.getNode(ToIDom);
    const TreeNodePtr PrevIDomSubTree = ToIDomTN->getIDom();
    assert(PrevIDomSubTree);
    const unsigned Level = ToIDomTN->getLevel();

    auto DescendBelow = [Level, &DT](NodePtr, NodePtr To) {
      return DT.getNode(To)->getLevel() > Level;
    };

    DTB_DEBUG(dbgs() << "\tTop of subtree: " << BlockPrinter(ToIDomTN) << "\n");

    SemiNCAInfo SNCA;
    SNCA.runDFS<IsPostDom>(ToIDom, 0, DescendBelow, 0);
    DTB_DEBUG(dbgs() << "\tRunning Semi-NCA\n");
    SNCA.runSemiNCA(DT, Level);
    SNCA.reattachExistingSubtree(DT, PrevIDomSubTree);
  }

  static bool IsReachableFromIDom(DomTreeT &DT, const TreeNodePtr TN) {
    DTB_DEBUG(dbgs() << "IsReachableFromIDom " << BlockPrinter(TN) << "\n");
    for (const NodePtr Succ :
         ChildrenGetter<NodePtr, !IsPostDom>::Get(TN->getBlock())) {
      DTB_DEBUG(dbgs() << "\tSucc " << BlockPrinter(Succ) << "\n");
      if (!DT.getNode(Succ)) continue;

      const NodePtr Support =
          DT.findNearestCommonDominator(TN->getBlock(), Succ);
      DTB_DEBUG(dbgs() << "\tSupport " << BlockPrinter(Support) << "\n");
      if (Support != TN->getBlock()) {
        DTB_DEBUG(dbgs() << "\t" << BlockPrinter(TN)
                         << " is reachable from support "
                         << BlockPrinter(Support) << "\n");
        return true;
      }
    }

    return false;
  }

  static void DeleteUnreachable(DomTreeT &DT, const TreeNodePtr ToTN) {
    DTB_DEBUG(dbgs() << "Deleting unreachable subtree " << BlockPrinter(ToTN)
                     << "\n");
    assert(ToTN);

    SmallVector<NodePtr, 16> AffectedQueue;
    const unsigned Level = ToTN->getLevel();

    auto DescendAndCollect = [Level, &AffectedQueue, &DT](NodePtr, NodePtr To) {
      const TreeNodePtr TN = DT.getNode(To);
      assert(TN);
      if (TN->getLevel() > Level) return true;
      if (llvm::find(AffectedQueue, To) == AffectedQueue.end()) {
        AffectedQueue.push_back(To);
      }
      return false;
    };

    SemiNCAInfo SNCA;
    unsigned LastDFSNum =
        SNCA.runDFS<false>(ToTN->getBlock(), 0, DescendAndCollect, 0);

    TreeNodePtr MinNode = ToTN;

    for (const NodePtr N : AffectedQueue) {
      const TreeNodePtr TN = DT.getNode(N);
      const NodePtr NCDBlock =
          DT.findNearestCommonDominator(TN->getBlock(), ToTN->getBlock());
      assert(NCDBlock);
      const TreeNodePtr NCD = DT.getNode(NCDBlock);
      assert(NCD);

      if (NCD != TN && NCD->getLevel() < MinNode->getLevel()) MinNode = NCD;
    }

    for (unsigned i = LastDFSNum; i > 0; --i) {
      const NodePtr N = SNCA.NumToNode[i];
      const TreeNodePtr TN = DT.getNode(N);
      DTB_DEBUG(dbgs() << "Erasing node " << BlockPrinter(TN) << "\n");

      EraseNode(DT, TN);
    }

    if (MinNode == ToTN) return;

    DTB_DEBUG(dbgs() << "DeleteUnreachable: running DFS with MinNode = "
                     << BlockPrinter(MinNode) << "\n");
    const unsigned MinLevel = MinNode->getLevel();
    const TreeNodePtr PrevIDom = MinNode->getIDom();
    assert(PrevIDom);

    SNCA.clear();
    LastDFSNum =
        SNCA.runDFS<false>(MinNode->getBlock(), 0,
                           [MinLevel, &DT](NodePtr, NodePtr To) {
                             const TreeNodePtr ToTN = DT.getNode(To);
                             return ToTN && ToTN->getLevel() > MinLevel;
                           },
                           0);

    DTB_DEBUG(dbgs() << "\nDFSNumbering:\n");
    for (unsigned i = 1; i < SNCA.NumToNode.size(); ++i)
      DTB_DEBUG(
          dbgs()
          << BlockPrinter(SNCA.NumToNode[i]) << " {" << i << "} ("
          << BlockPrinter(
                 SNCA.NumToNode[SNCA.NodeToInfo[SNCA.NumToNode[i]].Parent])
          << ")\n");

    DTB_DEBUG(dbgs() << "Previous IDom(MinNode) = " << BlockPrinter(PrevIDom)
                     << "\nRunning Semi-NCA\n");

    SNCA.runSemiNCA(DT, MinLevel);
    SNCA.reattachExistingSubtree(DT, PrevIDom);
  }

  static void EraseNode(DomTreeT &DT, const TreeNodePtr TN) {
    assert(TN);
    assert(TN->getNumChildren() == 0);

    const TreeNodePtr IDom = TN->getIDom();
    assert(IDom);

    auto ChIt = llvm::find(IDom->Children, TN);
    assert(ChIt != IDom->Children.end());
    std::swap(*ChIt, IDom->Children.back());
    IDom->Children.pop_back();

    DT.DomTreeNodes.erase(TN->getBlock());
  }

  //~~
  //===--------------- DomTree correctness verification ---------------------===
  //~~

  // Checks if the tree contains all reachable nodes in the input graph.
  bool verifyReachability(const DomTreeT &DT) {
    clear();
    doFullDFSWalk(DT, AlwaysDescend);

    for (auto &NodeToTN : DT.DomTreeNodes) {
      const TreeNodePtr TN = NodeToTN.second.get();
      const NodePtr BB = TN->getBlock();

      if (!BB || NodeToInfo.count(BB) == 0) {
        errs() << "DomTree node " << BlockPrinter(BB)
               << " not found by DFS walk!\n";
        errs().flush();

        return false;
      }
    }

    for (const NodePtr N : NumToNode) {
      if (N && !DT.getNode(N)) {
        errs() << "CFG node " << BlockPrinter(N)
               << " not found in the DomTree!\n";
        errs().flush();

        return false;
      }
    }

    return true;
  }

  // Check if for every parent with a level L in the tree all of its children
  // have level L + 1.
  static bool VerifyLevels(const DomTreeT &DT) {
    for (auto &NodeToTN : DT.DomTreeNodes) {
      const TreeNodePtr TN = NodeToTN.second.get();
      const NodePtr BB = TN->getBlock();
      if (!BB) continue;

      const TreeNodePtr IDom = TN->getIDom();
      if (!IDom && TN->getLevel() != 0) {
        errs() << "Node without an IDom " << BlockPrinter(BB)
               << " has a nonzero level " << TN->getLevel() << "!\n";
        errs().flush();

        return false;
      }

      if (IDom && TN->getLevel() != IDom->getLevel() + 1) {
        errs() << "Node " << BlockPrinter(BB) << " has level "
               << TN->getLevel() << " while it's IDom "
               << BlockPrinter(IDom->getBlock()) << " has level "
               << IDom->getLevel() << "!\n";
        errs().flush();

        return false;
      }
    }

    return true;
  }

  // Checks if for every edge From -> To in the graph
  //     NCD(From, To) == IDom(To) or To.
  bool verifyNCD(const DomTreeT &DT) {
    clear();
    doFullDFSWalk(DT, AlwaysDescend);

    for (auto &BlockToInfo : NodeToInfo) {
      auto &Info = BlockToInfo.second;

      const NodePtr From = NumToNode[Info.Parent];
      if (!From) continue;

      const NodePtr To = BlockToInfo.first;
      const TreeNodePtr ToTN = DT.getNode(To);
      assert(ToTN);

      const NodePtr NCD = DT.findNearestCommonDominator(From, To);
      const TreeNodePtr NCDTN = NCD ? DT.getNode(NCD) : nullptr;
      const TreeNodePtr ToIDom = ToTN->getIDom();
      if (NCDTN != ToTN && NCDTN != ToIDom) {
        errs() << "NearestCommonDominator verification failed:\n\tNCD(From:"
               << BlockPrinter(From) << ", To:" << BlockPrinter(To) << ") = "
               << BlockPrinter(NCD) << ",\t (should be To or IDom[To]: "
               << BlockPrinter(ToIDom) << ")\n";
        errs().flush();

        return false;
      }
    }

    return true;
  }

  // The below routines verify the correctness of the dominator tree relative to
  // the CFG it's coming from.  A tree is a dominator tree iff it has two
  // properties, called the parent property and the sibling property.  Tarjan
  // and Lengauer prove (but don't explicitly name) the properties as part of
  // the proofs in their 1972 paper, but the proofs are mostly part of proving
  // things about semidominators and idoms, and some of them are simply asserted
  // based on even earlier papers (see, e.g., lemma 2).  Some papers refer to
  // these properties as "valid" and "co-valid".  See, e.g., "Dominators,
  // directed bipolar orders, and independent spanning trees" by Loukas
  // Georgiadis and Robert E. Tarjan, as well as "Dominator Tree Verification
  // and Vertex-Disjoint Paths " by the same authors.

  // A very simple and direct explanation of these properties can be found in
  // "An Experimental Study of Dynamic Dominators", found at
  // https://arxiv.org/abs/1604.02711

  // The easiest way to think of the parent property is that it's a requirement
  // of being a dominator.  Let's just take immediate dominators.  For PARENT to
  // be an immediate dominator of CHILD, all paths in the CFG must go through
  // PARENT before they hit CHILD.  This implies that if you were to cut PARENT
  // out of the CFG, there should be no paths to CHILD that are reachable.  If
  // there are, then you now have a path from PARENT to CHILD that goes around
  // PARENT and still reaches CHILD, which by definition, means PARENT can't be
  // a dominator of CHILD (let alone an immediate one).

  // The sibling property is similar.  It says that for each pair of sibling
  // nodes in the dominator tree (LEFT and RIGHT) , they must not dominate each
  // other.  If sibling LEFT dominated sibling RIGHT, it means there are no
  // paths in the CFG from sibling LEFT to sibling RIGHT that do not go through
  // LEFT, and thus, LEFT is really an ancestor (in the dominator tree) of
  // RIGHT, not a sibling.

  // It is possible to verify the parent and sibling properties in
  // linear time, but the algorithms are complex. Instead, we do it in a
  // straightforward N^2 and N^3 way below, using direct path reachability.


  // Checks if the tree has the parent property: if for all edges from V to W in
  // the input graph, such that V is reachable, the parent of W in the tree is
  // an ancestor of V in the tree.
  //
  // This means that if a node gets disconnected from the graph, then all of
  // the nodes it dominated previously will now become unreachable.
  bool verifyParentProperty(const DomTreeT &DT) {
    for (auto &NodeToTN : DT.DomTreeNodes) {
      const TreeNodePtr TN = NodeToTN.second.get();
      const NodePtr BB = TN->getBlock();
      if (!BB || TN->getChildren().empty()) continue;

      clear();
      doFullDFSWalk(DT, [BB](NodePtr From, NodePtr To) {
        return From != BB && To != BB;
      });

      for (TreeNodePtr Child : TN->getChildren())
        if (NodeToInfo.count(Child->getBlock()) != 0) {
          errs() << "Child " << BlockPrinter(Child->getBlock())
                 << " reachable after its parent " << BlockPrinter(BB)
                 << " is removed!\n";
          errs().flush();

          return false;
        }
    }

    return true;
  }

  // Check if the tree has sibling property: if a node V does not dominate a
  // node W for all siblings V and W in the tree.
  //
  // This means that if a node gets disconnected from the graph, then all of its
  // siblings will now still be reachable.
  bool verifySiblingProperty(const DomTreeT &DT) {
    for (auto &NodeToTN : DT.DomTreeNodes) {
      const TreeNodePtr TN = NodeToTN.second.get();
      const NodePtr BB = TN->getBlock();
      if (!BB || TN->getChildren().empty()) continue;

      const auto &Siblings = TN->getChildren();
      for (const TreeNodePtr N : Siblings) {
        clear();
        NodePtr BBN = N->getBlock();
        doFullDFSWalk(DT, [BBN](NodePtr From, NodePtr To) {
          return From != BBN && To != BBN;
        });

        for (const TreeNodePtr S : Siblings) {
          if (S == N) continue;

          if (NodeToInfo.count(S->getBlock()) == 0) {
            errs() << "Node " << BlockPrinter(S)
                   << " not reachable when its sibling " << BlockPrinter(N)
                   << " is removed!\n";
            errs().flush();

            return false;
          }
        }
      }
    }

    return true;
  }
};

template <class FuncT, class DomTreeT>
void Calculate(DomTreeT &DT, FuncT &F) {
  SemiNCAInfo<DomTreeT> SNCA;
  SNCA.template calculateFromScratch(DT, GraphTraits<FuncT *>::size(&F));
}

template <class DomTreeT>
void InsertEdge(DomTreeT &DT, typename DomTreeT::NodePtr From,
                typename DomTreeT::NodePtr To) {
  if (DT.isPostDominator())
    llvm_unreachable("Insertions are not implemented for postdominators yet");

  SemiNCAInfo<DomTreeT>::InsertEdge(DT, From, To);
}

template <class DomTreeT>
void DeleteEdge(DomTreeT &DT, typename DomTreeT::NodePtr From,
                typename DomTreeT::NodePtr To) {
  if (DT.isPostDominator())
    llvm_unreachable("Deletions are not implemented for postdominators yet");

  SemiNCAInfo<DomTreeT>::DeleteEdge(DT, From, To);
}

template <class DomTreeT>
bool Verify(const DomTreeT &DT) {
  SemiNCAInfo<DomTreeT> SNCA;
  return SNCA.verifyReachability(DT) && SNCA.VerifyLevels(DT) &&
         SNCA.verifyNCD(DT) && SNCA.verifyParentProperty(DT) &&
         SNCA.verifySiblingProperty(DT);
}

}  // namespace DomTreeBuilder
}  // namespace llvm

#endif
