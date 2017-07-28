//===- llvm/unittests/IR/DominatorTreeTest.cpp - Constants unit tests -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <random>
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/GenericDomTreeConstruction.h"
#include "CFGBuilder.h"
#include "gtest/gtest.h"

#define DEBUG_TYPE "batch-update-tests"

using namespace llvm;

namespace {
const auto CFGInsert = CFGBuilder::ActionKind::Insert;
const auto CFGDelete = CFGBuilder::ActionKind::Delete;

struct PostDomTree : PostDomTreeBase<BasicBlock> {
  PostDomTree(Function &F) { recalculate(F); }
};

using DomUpdate = DominatorTree::UpdateType;
static_assert(std::is_same<DomUpdate, PostDomTree::UpdateType>::value,
              "Trees differing only in IsPostDom should have the same update types");
using DomSNCA = DomTreeBuilder::SemiNCAInfo<DomTreeBuilder::BBDomTree>;
using PostDomSNCA = DomTreeBuilder::SemiNCAInfo<DomTreeBuilder::BBPostDomTree>;
const auto Insert = DominatorTree::Insert;
const auto Delete = DominatorTree::Delete;
}  // namespace

TEST(DominatorTreeBatchUpdates, LegalizeDomUpdates) {
  CFGHolder Holder;
  CFGBuilder Builder(Holder.F, {{"A", "B"}}, {});

  BasicBlock *A = Builder.getOrAddBlock("A");
  BasicBlock *B = Builder.getOrAddBlock("B");
  BasicBlock *C = Builder.getOrAddBlock("C");
  BasicBlock *D = Builder.getOrAddBlock("D");

  std::vector<DomUpdate> Updates = {{Insert, B, C}, {Insert, C, D},
                                    {Delete, B, C}, {Insert, B, C},
                                    {Insert, B, D}, {Delete, C, D},
                                    {Delete, A, B}};
  SmallVector<DomUpdate, 4> Legalized;
  DomSNCA::LegalizeUpdates(Updates, Legalized);
  DEBUG(dbgs() << "Legalized updates:\t");
  DEBUG(for (auto &U : Legalized) dbgs() << U << ", ");
  DEBUG(dbgs() << "\n");
  EXPECT_EQ(Legalized.size(), 3UL);
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Insert, B, C}), Legalized.end());
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Insert, B, D}), Legalized.end());
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Delete, A, B}), Legalized.end());
}

TEST(DominatorTreeBatchUpdates, LegalizePostDomUpdates) {
  CFGHolder Holder;
  CFGBuilder Builder(Holder.F, {{"A", "B"}}, {});

  BasicBlock *A = Builder.getOrAddBlock("A");
  BasicBlock *B = Builder.getOrAddBlock("B");
  BasicBlock *C = Builder.getOrAddBlock("C");
  BasicBlock *D = Builder.getOrAddBlock("D");

  std::vector<DomUpdate> Updates = {{Insert, B, C}, {Insert, C, D},
                                    {Delete, B, C}, {Insert, B, C},
                                    {Insert, B, D}, {Delete, C, D},
                                    {Delete, A, B}};
  SmallVector<DomUpdate, 4> Legalized;
  PostDomSNCA::LegalizeUpdates(Updates, Legalized);
  DEBUG(dbgs() << "Legalized postdom updates:\t");
  DEBUG(for (auto &U : Legalized) dbgs() << U << ", ");
  DEBUG(dbgs() << "\n");
  EXPECT_EQ(Legalized.size(), 3UL);
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Insert, C, B}), Legalized.end());
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Insert, D, B}), Legalized.end());
  EXPECT_NE(llvm::find(Legalized, DomUpdate{Delete, B, A}), Legalized.end());
}

TEST(DominatorTreeBatchUpdates, SingleInsertion) {
  CFGHolder Holder;
  CFGBuilder Builder(Holder.F, {{"A", "B"}}, {{CFGInsert, {"B", "C"}}});

  DominatorTree DT(*Holder.F);
  EXPECT_TRUE(DT.verify());
  PostDomTree PDT(*Holder.F);
  EXPECT_TRUE(DT.verify());

  BasicBlock *B = Builder.getOrAddBlock("B");
  BasicBlock *C = Builder.getOrAddBlock("C");
  std::vector<DomUpdate> Updates = {{Insert, B, C}};

  ASSERT_TRUE(Builder.applyUpdate());

  DT.applyUpdates(Updates);
  EXPECT_TRUE(DT.verify());
  PDT.applyUpdates(Updates);
  EXPECT_TRUE(PDT.verify());
}

TEST(DominatorTreeBatchUpdates, SingleDeletion) {
  CFGHolder Holder;
  CFGBuilder Builder(Holder.F, {{"A", "B"}, {"B", "C"}},
                     {{CFGDelete, {"B", "C"}}});

  DominatorTree DT(*Holder.F);
  EXPECT_TRUE(DT.verify());
  PostDomTree PDT(*Holder.F);
  EXPECT_TRUE(DT.verify());

  BasicBlock *B = Builder.getOrAddBlock("B");
  BasicBlock *C = Builder.getOrAddBlock("C");
  std::vector<DomUpdate> Updates = {{Delete, B, C}};

  ASSERT_TRUE(Builder.applyUpdate());

  DT.applyUpdates(Updates);
  EXPECT_TRUE(DT.verify());
  PDT.applyUpdates(Updates);
  EXPECT_TRUE(PDT.verify());
}

TEST(DominatorTreeBatchUpdates, FewInsertion) {
  CFGHolder Holder;
  CFGBuilder Builder(Holder.F, {{"A", "B"}},
                     {{CFGInsert, {"B", "C"}}, {CFGInsert, {"C", "B"}},
                      {CFGInsert, {"C", "D"}}, {CFGInsert, {"D", "E"}}});

  DominatorTree DT(*Holder.F);
  EXPECT_TRUE(DT.verify());
//  PostDomTree PDT(*Holder.F);
//  EXPECT_TRUE(PDT.verify());

  BasicBlock *B = Builder.getOrAddBlock("B");
  BasicBlock *C = Builder.getOrAddBlock("C");
  BasicBlock *D = Builder.getOrAddBlock("D");
  BasicBlock *E = Builder.getOrAddBlock("E");

  std::vector<DomUpdate> Updates = {{Insert, B, C}, {Insert, C, B},
                                    {Insert, C, D}, {Insert, D, E}};

  while (Builder.applyUpdate())
    ;

  DT.applyUpdates(Updates);
  EXPECT_TRUE(DT.verify());
  //PDT.applyUpdates(Updates);
  //EXPECT_TRUE(PDT.verify());
}