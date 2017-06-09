//===- NewDominators.h - Dominator Info Calculation -------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the DominatorTree class, which provides fast and efficient
// dominance queries.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_NEW_DOMINATORS_H
#define LLVM_IR_NEW_DOMINATORS_H

#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include <memory>
#include <queue>
#include <utility>

namespace llvm {

class DominatorTree;
class Function;
class Instruction;
class Module;
class raw_ostream;

struct NodeByName {
  bool operator()(const BasicBlock *First, const BasicBlock *Second) const {
    const auto Cmp = First->getName().compare_numeric(Second->getName());
    if (Cmp == 0)
      return less{}(First, Second);

    return Cmp < 0;
  }
};

class DTNode {
public:
  using BlockTy = BasicBlock *;
  using Index = unsigned;

  BlockTy getBlock() const { return BB; }
  DTNode *getIDom() const { return IDom; }
  Index getLevel() const { return Level; }
  Index getInNum() const { return InNum; }
  Index getOutNum() const { return OutNum; }

  using ChildrenTy = SmallVector<DTNode *, 8>;
  using iterator = typename ChildrenTy::iterator;
  using const_iterator = typename ChildrenTy::const_iterator;

  iterator begin() { return Children.begin(); }
  iterator end() { return Children.end(); }
  const_iterator begin() const { return Children.begin(); }
  const_iterator end() const { return Children.end(); }
  size_t getNumChildren() const { return Children.size(); }

  iterator findChild(DTNode *Child) { return std::find(begin(), end(), Child); }

  const_iterator findChild(DTNode *Child) const {
    return std::find(begin(), end(), Child);
  }

  iterator findChild(BlockTy ChildBB) {
    return std::find_if(begin(), end(),
                        [ChildBB](DTNode *C) { return C->BB == ChildBB; });
  }

  const_iterator findChild(BlockTy ChildBB) const {
    return std::find_if(begin(), end(),
                        [ChildBB](DTNode *C) { return C->BB == ChildBB; });
  }

  bool hasChild(DTNode *Child) const { return findChild(Child) != end(); }

  bool hasChild(BlockTy ChildBB) const { return findChild(ChildBB) != end(); }

  StringRef getName() const { return BB->getName(); }
  void dump(raw_ostream &OS = dbgs()) const;

private:
  friend class NewDomTree;
  DTNode(BlockTy Block) : BB(Block) {}

  void setIDom(DTNode *NewIDom);

  BasicBlock *BB;
  DTNode *IDom = nullptr;
  Index Level = 0;
  ChildrenTy Children;
  DTNode *RDom = nullptr;
  DTNode *PreorderParent = nullptr;
  mutable Index InNum = 0;
  mutable Index OutNum = 0;

  void addChild(DTNode *Child);
  void removeChild(DTNode *Child);
};

class NewDomTree {
public:
  using BlockTy = DTNode::BlockTy;
  using Index = DTNode::Index;

  NewDomTree(BlockTy Entry) : Entry(Entry) {
    computeReachableDominators(Entry, 0);
    // recomputeInOutNums();
  }

  bool contains(BlockTy N) const;

  DTNode *getNode(BlockTy BB) const {
    const auto it = TreeNodes.find(BB);
    assert(it != TreeNodes.end());
    return it->second.get();
  }

  DTNode *findNCA(DTNode *First, DTNode *Second) const;

  bool dominates(DTNode *Src, DTNode *Dst) const;

  void insertArc(BlockTy From, BlockTy To);
  void deleteArc(BlockTy From, BlockTy To);

  void eraseNode(DTNode *TN);
  void replaceWith(DTNode *Replace, DTNode *With);

  void toOldDT(DominatorTree &DT) const;

  enum Verification : unsigned {
    None = 0,
    Basic = 1,
    CFG = 2,
    Sibling = 4,
    OldDT = 8,
    Normal = unsigned(Basic) | unsigned(CFG) | unsigned(OldDT),
    Full = unsigned(Basic) | unsigned(CFG) | unsigned(Sibling) | unsigned(OldDT)
  };

  bool verify(Verification VerificationLevel = Verification::Basic) const;
  bool verifyWithOldDT() const;
  bool verifyNCA() const;
  bool verifyLevels() const;
  bool verifyReachability() const;
  bool verifyParentProperty() const;
  bool verifySiblingProperty() const;

  void print(raw_ostream &OS) const;
  void dump() const { print(dbgs()); }
  void dumpIDoms(raw_ostream &OS = dbgs()) const;
  void addDebugInfoToIR();
  void viewCFG() const { Entry->getParent()->viewCFG(); }
  void dumpLegacyDomTree() const;

private:
  BlockTy Entry = nullptr;
  DenseMap<BlockTy, std::unique_ptr<DTNode>> TreeNodes;
  mutable bool isInOutValid = false;

  DTNode *addNode(BlockTy BB);
  DTNode *getOrAddNode(BlockTy BB);

  void computeReachableDominators(BlockTy Root, Index MinLevel);
  void computeUnreachableDominators(
      BlockTy Root, DTNode *Incoming,
      SmallVectorImpl<std::pair<BlockTy, DTNode *>> &DiscoveredConnectingArcs);

  struct DFSNodeInfo {
    SmallVector<BlockTy, 8> Predecessors;
    Index Num;
    BlockTy Parent;
  };

  struct DFSResult {
    std::vector<BlockTy> NumToNode;
    DenseMap<BlockTy, DFSNodeInfo> NodeToInfo;

    void dumpDFSNumbering(raw_ostream &OS = dbgs()) const;
  };

  template <typename DescendCondition>
  static DFSResult runDFS(BlockTy Start, DescendCondition Condition);

  void semiNCA(DFSResult &DFS, Index MinLevel, DTNode *AttachTo = nullptr);

  struct SNCAInfo {
    BlockTy Label;
    BlockTy SDom;
  };
  BlockTy getSDomCandidate(BlockTy Start, BlockTy Pred, DFSResult &DFS,
                           DenseMap<BlockTy, SNCAInfo> &SNCA);

  struct InsertionInfo {
    using BucketElementTy = std::pair<Index, DTNode *>;
    struct DecreasingLevel {
      bool operator()(const BucketElementTy &First,
                      const BucketElementTy &Second) const {
        return First.first > Second.first;
      }
    };

    std::priority_queue<BucketElementTy, SmallVector<BucketElementTy, 8>,
                        DecreasingLevel>
        bucket;
    DenseSet<DTNode *> affected;
    DenseSet<DTNode *> visited;
    SmallVector<DTNode *, 8> affectedQueue;
    SmallVector<DTNode *, 8> visitedNotAffectedQueue;
  };

  void insertUnreachable(DTNode *FromTN, BlockTy To);
  void insertReachable(DTNode *FromTN, DTNode *ToTN);
  void visitInsertion(DTNode *N, Index RootLevel, DTNode *NCA,
                      InsertionInfo &II);
  void updateInsertion(DTNode *NCA, InsertionInfo &II);
  void updateLevels(InsertionInfo &II);
  void updateLevels(DTNode *Start);

  bool isReachableFromIDom(DTNode *N);
  void deleteReachable(DTNode *FromTN, DTNode *ToTN);
  void deleteUnreachable(DTNode *ToTN);

  void recomputeInOutNums() const;
  void printImpl(raw_ostream &OS, const DTNode *TN) const;
};

template <typename DescendCondition>
NewDomTree::DFSResult NewDomTree::runDFS(BlockTy Start,
                                         DescendCondition Condition) {
  DFSResult Res;
  Index NextDFSNum = 0;
  SmallDenseSet<BlockTy, 64> Visited;
  SmallVector<BlockTy, 64> WorkList;

  Res.NodeToInfo[Start].Parent = nullptr;
  WorkList.push_back(Start);

  // Compute preorder numbers nad parents.
  while (!WorkList.empty()) {
    BlockTy BB = WorkList.back();
    WorkList.pop_back();
    if (Visited.count(BB) != 0)
      continue;

    auto &BBInfo = Res.NodeToInfo[BB];
    BBInfo.Num = NextDFSNum;
    Res.NumToNode.push_back(BB);
    ++NextDFSNum;
    Visited.insert(BB);
    for (auto *Succ : successors(BB)) {
      auto &SuccInfo = Res.NodeToInfo[Succ];
      if (Succ != BB)
        SuccInfo.Predecessors.push_back(BB);
      if (Visited.count(Succ) == 0)
        if (Condition(BB, Succ)) {
          WorkList.push_back(Succ);
          SuccInfo.Parent = BB;
        }
    }
  }

  return Res;
}

} // end namespace llvm

#endif // LLVM_IR_NEW_DOMINATORS_H
