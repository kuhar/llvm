//===-- dominators.cpp - Incremental dominators playground  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"
#include <cctype>
#include <string>
#include <vector>

namespace llvm {

struct Node {
  Node(int value) : value(value) {}

  Node *parent = nullptr;
  SmallVector<Node *, 8> children;
  //BasicBlock *value;
  int value;
};

struct NewDomTree {
  NewDomTree(Node * root) : root(root) {}

  DenseMap<Node*, Node*> idoms;
  DenseMap<Node*, Node*> sdoms;
  Node *root;
};

} // namespace llvm

using namespace llvm;

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);

  LLVMContext TheContext;
  auto *M = new Module("test", TheContext);
  FunctionType *FTy =
      TypeBuilder<void(), false>::get(M->getContext());
  auto *F = cast<Function>(
      M->getOrInsertFunction("test_f", FTy));

  auto MakeBB = [&] (StringRef name) -> BasicBlock * {
    return BasicBlock::Create(M->getContext(), name, F);
  };

  auto *BoolTy = IntegerType::get(M->getContext(), 1);
  auto *False = ConstantInt::get(BoolTy, 0);

  auto *Entry = MakeBB("entry");
  IRBuilder<> IRB(Entry);

  auto *BB_A = MakeBB("A");
  IRB.CreateBr(BB_A);
  auto *BB_B = MakeBB("B");
  auto *BB_C = MakeBB("C");
  auto *BB_D = MakeBB("D");
  auto *BB_E = MakeBB("E");

  IRB.SetInsertPoint(BB_A);
  IRB.CreateCondBr(False, BB_B, BB_D);

  IRB.SetInsertPoint(BB_B);
  IRB.CreateBr(BB_C);

  IRB.SetInsertPoint(BB_C);
  IRB.CreateCondBr(False, BB_D, BB_E);

  IRB.SetInsertPoint(BB_D);
  IRB.CreateBr(BB_E);

  IRB.SetInsertPoint(BB_E);
  IRB.CreateRetVoid();

  F->viewCFG();

  outs() << "Dominators\n";
}
