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

#include <queue>
#include <utility>
#include "llvm/ADT/DenseMapInfo.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"

namespace llvm {

class DominatorTree;
class Function;
class Instruction;
class Module;
class raw_ostream;

class DTNode {
public:
  using BlockTy = BasicBlock *;
  using Index = unsigned;

  BlockTy getBlock() const { return BB; }
  DTNode *getIDom() const { return IDom; }
  Index getLevel() const { return Level; }
  Index getInNum() const { return InNum; }
  Index getOutNum() const { return OutNum; }

  using ChildrenTy = SmallVector<DTNode *, 4>;
  using iterator = typename ChildrenTy::iterator;
  using const_iterator = typename ChildrenTy::const_iterator;

  iterator begin() { return Children.begin(); }
  iterator end() { return Children.end(); }
  const_iterator begin() const { return Children.begin(); }
  const_iterator end() const { return Children.end(); }
  size_t getNumChildren() const { return Children.size(); }

  bool hasChild(DTNode *Child) const {
    return std::find(begin(), end(), Child) != Children.end();
  }

  bool hasChild(BlockTy ChildBB) const {
    return std::find_if(begin(), end(), [ChildBB] (DTNode* C) {
      return C->BB == ChildBB;
    }) != Children.end();
  }

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


struct NodeByName {
  bool operator()(const BlockTy first, const BlockTy second) const {
    const auto Cmp = first->getName().compare_numeric(second->getName());
    if (Cmp == 0) return less{}(first, second);

    return Cmp < 0;
  }
};

class NewDomTree {
public:
  using BlockTy = DTNode::BlockTy;
  using Index = DTNode::Index;
  NewDomTree(BlockTy Root) : root(Root) { computeReachableDominators(root, 0); }

  bool contains(BlockTy B) const;
  DTNode *getNode(BlockTy B);
  const DTNode *getNode(BlockTy B) const;

  BlockTy findNCA(DTNode *First, DTNode *Second) const;

  bool dominates(DTNode *Src, DTNode *Dst) const;

  void insertArc(BlockTy From, BlockTy To);
  void deleteArc(BlockTy From, BlockTy To);

  void toOldDT(DominatorTree& DT) const;

  enum Verification : unsigned {
    None    = 0,
    Basic   = 1,
    CFG     = 2,
    Sibling = 4,
    OldDT   = 8,
    Normal  = unsigned(Basic) | unsigned(CFG) | unsigned(OldDT),
    Full    = unsigned(Basic) | unsigned(CFG) | unsigned(Sibling) |
              unsigned(OldDT)
  };

  bool verify(Verification VerificationLevel = Verification::Basic) const;
  bool verifyWithOldDT() const;
  bool verifyNCA() const;
  bool verifyLevels() const;
  bool verifyReachability() const;
  bool verifyParentProperty() const;
  bool verifySiblingProperty() const;

  void print(DTNode *Start, raw_ostream &OS) const;
  void dump(raw_ostream &OS = dbgs()) const { print(Root, OS); }
  void dumpIDoms(raw_ostream &OS = dbgs()) const;
  void dumpLevels(raw_ostream &OS = dbgs()) const;
  void addDebugInfoToIR();
  void viewCFG() const { root->getParent()->viewCFG(); }
  void dumpLegacyDomTree() const;

 private:
  DTNode *Entry = nullptr;
  DenseMap<BlockTy, std::unique_ptr<DTNode>> TreeNodes;
  mutable bool isInOutValid = false;

  DTNode *addNode(BlockTy BB);
  DTNode *getOrAddNode(BlockTy BB);

  void computeReachableDominators(DTNode *Root, Index MinLevel);
  void computeUnreachableDominators(BTNode *Root, BlockTy Incoming,
      SmallVectorImpl<std::pair<BlockTy, BlockTy>> &DiscoveredConnectingArcs);

  struct DFSInfo {
    Index Num;
    BlockTy Parent;
    SmallVector<BlockTy, 4> Predecessors;
  };

  struct DFSResult {
    Index NextDFSNum = 0;
    DenseMap<BlockTy, DFSInfo> NodeToInfo;
    std::vector<BlockTy> NumToNode;

    void dumpDFSNumbering(raw_ostream &OS = dbgs()) const;
  };

  template <typename DescendCondition>
  static DFSResult runDFS(BlockTy Start, DescendCondition Condition);

  void semiNCA(DFSResult &DFS, BlockTy Root, Index MinLevel,
               BlockTy AttachTo = nullptr);

  struct InsertionInfo {
    using BucketElementTy = std::pair<Index, BlockTy>;
    struct DecreasingLevel {
      bool operator()(const BucketElementTy &First,
                      const BucketElementTy &Second) const {
        return First.first > Second.first;
      }
    };

    std::priority_queue<BucketElementTy, SmallVector<BucketElementTy, 8>,
                        DecreasingLevel>
        bucket;
    DenseSet<BlockTy> affected;
    DenseSet<BlockTy> visited;
    SmallVector<BlockTy, 8> affectedQueue;
    SmallVector<BlockTy, 8> visitedNotAffectedQueue;
  };

  BlockTy getSDomCandidate(BlockTy Start, BlockTy Pred, DFSResult &DFS,
                           DenseMap<BlockTy, BlockTy> &Labels);

  void insertUnreachable(BlockTy From, BlockTy To);
  void insertReachable(BlockTy From, BlockTy To);
  void visitInsertion(BlockTy N, Index RootLevel, BlockTy NCA,
                      InsertionInfo &II);
  void updateInsertion(BlockTy NCA, InsertionInfo &II);
  void updateLevels(InsertionInfo &II);

  bool isReachableFromIDom(BlockTy N);
  void deleteReachable(BlockTy From, BlockTy To);
  void deleteUnreachable(BlockTy To);

  void recomputeInOutNums() const;
};

template <typename DescendCondition>
NewDomTree::DFSResult NewDomTree::runDFS(BlockTy Start,
                                         DescendCondition Condition) {
  DFSResult Res;
  Res.NextDFSNum = 0;
  DenseSet<BlockTy> Visited;
  std::vector<BlockTy> WorkList;

  Res.NodeToInfo[Start].Parent = nullptr;
  WorkList.push_back(Start);

  // Compute preorder numbers and parents.
  while (!WorkList.empty()) {
    BlockTy BB = WorkList.back();
    WorkList.pop_back();
    if (Visited.count(BB) != 0) continue;

    Res.NodeToInfo[BB].Num = Res.NextDFSNum;
    Res.NumToNode.push_back(BB);
    ++Res.nextDFSNum;
    Visited.insert(BB);

    for (auto *Succ : reverse(successors(BB))) {
      DFSInfo &SuccInfo = Res.NodeToInfo[Succ];
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

}  // end namespace llvm

#endif  // LLVM_IR_NEW_DOMINATORS_H
