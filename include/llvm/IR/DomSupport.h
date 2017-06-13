//===- DomSupport.h - Dominator Support and Testing -------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_DOM_SUPPORT_H
#define LLVM_IR_DOM_SUPPORT_H

#include "Dominators.h"
#include "NewDominators.h"

#include "llvm/IR/TypeBuilder.h"

namespace llvm {

class Function;
class Instruction;
class Module;
class raw_ostream;

struct GraphCFG {
  using Index = DTNode::Index;
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
  using Index = DTNode::Index;
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

  static Optional<InputGraph> readFromFile(const std::string &filename);
  static InputGraph fromFunction(Function *F);
  static InputGraph fromModule(Module &M);

  void dump(raw_ostream &OS = dbgs()) const;
  void printCurrent(raw_ostream &Out) const;
  // Returns entry
  BasicBlock *toCFG();

  using CFGArc = std::pair<BasicBlock *, BasicBlock *>;
  struct CFGUpdate {
    Op action;
    CFGArc arc;
  };
  Optional<CFGUpdate> applyUpdate(bool UpdateIR = true);

private:
  bool connect(const Arc &A);
  bool disconnect(const Arc &A);
};

void connect(BasicBlock *From, BasicBlock *To);
void disconnect(BasicBlock *From, BasicBlock *To);

} // end namespace llvm

#endif // LLVM_IR_DOM_SUPPORT_H
