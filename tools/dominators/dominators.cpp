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
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Signals.h"

#include <cctype>
#include <fstream>
#include <memory>
#include <string>
#include <sstream>
#include <utility>
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

static cl::opt<std::string>
    InputFile(cl::Positional, cl::desc("<input file>"), cl::init("-"));

struct GraphCFG {
  LLVMContext context;
  Module module;
  Function *function;

  GraphCFG(StringRef moduleName = "GraphCFG")
      : module(moduleName, context) {
    FunctionType *FTy = TypeBuilder<void(), false>::get(context);
    function = cast<Function>(module.getOrInsertFunction("dummy_f", FTy));
  }
};

struct InputGraph {
  unsigned nodesNum = 0;
  unsigned entry = 0;

  using Arc = std::pair<unsigned, unsigned>;
  std::vector<Arc> arcs;

  enum class Op : char { Insert, Delete };
  struct Update { Op action; Arc arc; };
  std::vector<Update> updates;

  void dump() {
    dbgs() << "Nodes:\t" << nodesNum << ", entry:\t" << entry << "\n";
    dbgs() << "Arcs:\n";
    for (const auto &A : arcs)
      dbgs() << A.first << "\t->\t" << A.second << "\n";
    dbgs() << "Updates:\n";
    for (const auto &U : updates) {
      dbgs() << ((U.action == Op::Insert) ? "Ins " : "Del ")
             << U.arc.first << "\t->\t" << U.arc.second << "\n";
    }
  }

  std::unique_ptr<GraphCFG> toCFG() const;
};

InputGraph readInputGraph(std::string path) {
  dbgs() << "Reading input graph: " << path << "\n";
  std::ifstream IFS(path);
  dbgs() << IFS.good() << "\n";
  InputGraph Graph;

  for (std::string Line; std::getline(IFS, Line);) {
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

std::unique_ptr<GraphCFG> InputGraph::toCFG() const {
  std::unique_ptr<GraphCFG> CFGPtr = make_unique<GraphCFG>();
  GraphCFG &CFG = *CFGPtr;
  BasicBlock* EntryBB = nullptr;
  std::vector<BasicBlock *> Blocks(nodesNum);
  std::vector<std::vector<BasicBlock *>> Children(nodesNum);

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
  for (unsigned i = 1; i <= nodesNum; ++i)
    if (i != entry)
      Blocks[i - 1] = MakeBB(MakeName("n_", i));

  for (const auto &A : arcs)
    Children[A.first - 1].push_back(Blocks[A.second - 1]);

  auto *IntTy = IntegerType::get(CFG.context, 32);
  auto *Zero = ConstantInt::get(IntTy, 0);
  IRBuilder<> IRB(EntryBB);
  for (size_t i = 0; i < Children.size(); ++i) {
    const auto ChildrenNum = Children[i].size();
    if (ChildrenNum == 0)
      continue;

    auto *SrcBB = Blocks[i];
    IRB.SetInsertPoint(SrcBB);
    auto *Switch = IRB.CreateSwitch(Zero, Children[i].front());
    for (size_t c = 1; c < ChildrenNum; ++c) {
      auto *CaseInt = ConstantInt::get(IntTy, c);
      Switch->addCase(CaseInt, Children[i][c]);
    }
  }

  return CFGPtr;
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

  auto CFG = Graph.toCFG();
  CFG->function->viewCFG();
}
