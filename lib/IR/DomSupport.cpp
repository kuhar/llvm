//===- DomSupport.cpp - Dominators Support and Testing --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DomSupport.h"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <sstream>

#define DEBUG_TYPE "dom-support"

using namespace llvm;

void llvm::connect(BasicBlock *From, BasicBlock *To) {
  auto *IntTy =
      IntegerType::get(From->getParent()->getParent()->getContext(), 32);

  if (isa<UnreachableInst>(From->getTerminator()))
    From->getTerminator()->eraseFromParent();
  if (!From->getTerminator()) {
    IRBuilder<> IRB(From);
    IRB.CreateSwitch(ConstantInt::get(IntTy, 0), To);
    return;
  }

  SwitchInst *SI = cast<SwitchInst>(From->getTerminator());
  const auto Last = SI->getNumCases();

  auto *IntVal = ConstantInt::get(IntTy, Last);
  SI->addCase(IntVal, To);
}

void llvm::disconnect(BasicBlock *From, BasicBlock *To) {
  DEBUG(dbgs() << "Deleting BB arc " << From->getName() << " -> "
               << To->getName() << "\n";
        dbgs().flush());
  SwitchInst *SI = cast<SwitchInst>(From->getTerminator());

  if (SI->getNumCases() == 0) {
    SI->eraseFromParent();
    IRBuilder<> IRB(From);
    IRB.CreateUnreachable();
    return;
  }

  if (SI->getDefaultDest() == To) {
    auto FirstC = SI->case_begin();
    SI->setDefaultDest(FirstC->getCaseSuccessor());
    SI->removeCase(FirstC);
    return;
  }

  for (auto CIt = SI->case_begin(); CIt != SI->case_end(); ++CIt)
    if (CIt->getCaseSuccessor() == To) {
      SI->removeCase(CIt);
      return;
    }
}

BasicBlock *InputGraph::toCFG() {
  cfg = make_unique<GraphCFG>();
  GraphCFG &CFG = *cfg;
  BasicBlock *EntryBB = nullptr;
  std::vector<BasicBlock *> Blocks(nodesNum);

  auto MakeBB = [&](StringRef name) -> BasicBlock * {
    auto *BB = BasicBlock::Create(CFG.context, name, CFG.function);
    IRBuilder<> IRB(BB);
    IRB.CreateUnreachable();
    return BB;
  };

  auto MakeName = [](StringRef prefix, unsigned num) {
    std::string buffer;
    raw_string_ostream OS(buffer);
    OS << prefix << num;
    OS.flush();
    return OS.str();
  };

  EntryBB = Blocks[entry - 1] = MakeBB(MakeName("entry_n_", entry));
  CFG.numToBB[entry] = EntryBB;

  for (unsigned i = 1; i <= nodesNum; ++i)
    if (i != entry) {
      Blocks[i - 1] = MakeBB(MakeName("n_", i));
      CFG.numToBB[i] = Blocks[i - 1];
    }

  for (const auto &A : arcs)
    llvm::connect(Blocks[A.first - 1], Blocks[A.second - 1]);

  return EntryBB;
}

bool InputGraph::connect(const Arc &A) {
  if (std::find(arcs.begin(), arcs.end(), A) != arcs.end()) return false;

  arcs.push_back(A);
  return true;
}

bool InputGraph::disconnect(const Arc &A) {
  auto it = std::find(arcs.begin(), arcs.end(), A);
  if (it == arcs.end()) return false;

  std::swap(*it, arcs.back());
  arcs.pop_back();
  return true;
}

Optional<InputGraph::CFGUpdate> InputGraph::applyUpdate(bool UpdateIR
                                                        /* = true */) {
  if (updateIdx == updates.size()) return None;

  auto Next = updates[updateIdx++];
  bool Updated = false;
  if (Next.action == Op::Insert && connect(Next.arc))
    Updated = true;
  else if (disconnect(Next.arc))
    Updated = true;

  if (!Updated) return None;

  if (!UpdateIR)  // FIXME: Remove API hack when not updating IR...
    return CFGUpdate{Next.action, {nullptr, nullptr}};

  auto A = cfg->getArc(Next.arc);
  if (Next.action == Op::Insert)
    llvm::connect(A.first, A.second);
  else
    llvm::disconnect(A.first, A.second);

  return CFGUpdate{Next.action, A};
}

Optional<InputGraph> InputGraph::readFromFile(const std::string &filename) {
  DEBUG(dbgs() << "Reading input graph: " << filename << "\n");
  std::ifstream IFS(filename);

  if (!IFS.good()) {
    errs() << "Could not read graph input file\n";
    return None;
  }

  InputGraph Graph;

  for (std::string Line; std::getline(IFS, Line) && !Line.empty();) {
    std::istringstream ISS(Line);
    char Action;
    ISS >> Action;
    switch (Action) {
      default:
        llvm_unreachable("Unknown action");
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
        if (!(ISS >> x >> y)) llvm_unreachable("Parse error");
        Graph.arcs.push_back({x, y});
      } break;
      case 'e':
        break;
      case 'i': {
        unsigned x, y;
        if (!(ISS >> x >> y)) llvm_unreachable("Parse error");
        assert(x <= Graph.nodesNum);
        assert(y <= Graph.nodesNum);
        Graph.updates.push_back({InputGraph::Op::Insert, {x, y}});
      } break;
      case 'd': {
        unsigned x, y;
        if (!(ISS >> x >> y)) llvm_unreachable("Parse error");
        assert(x <= Graph.nodesNum);
        assert(y <= Graph.nodesNum);
        Graph.updates.push_back({InputGraph::Op::Delete, {x, y}});
      } break;
    }
  }

  return std::move(Graph);
}

InputGraph InputGraph::fromFunction(Function *F) {
  DenseMap<BasicBlock *, Index> BBToNum;
  Index nextNum = 0;
  for (auto &BB : *F) BBToNum[&BB] = nextNum++;

  InputGraph IG;
  IG.nodesNum = nextNum;
  IG.arcs.reserve(nextNum);
  IG.entry = BBToNum[&F->getEntryBlock()];

  for (auto &BB : *F)
    for (auto *Succ : successors(&BB))
      IG.arcs.push_back({BBToNum[&BB], BBToNum[Succ]});

  return IG;
}

InputGraph InputGraph::fromModule(Module &M) {
  assert(M.getFunctionList().size() == 1);
  return fromFunction(&M.getFunctionList().front());
}

void InputGraph::printCurrent(raw_ostream &Out) const {
  Out << nodesNum << ' ' << arcs.size() << ' ' << entry << ' ' << 1 << '\n';

  for (const auto &A : arcs) Out << "a " << A.first << " " << A.second << '\n';

  Out << "e\n";
}

void InputGraph::dump(raw_ostream &OS) const {
  OS << "Nodes:\t" << nodesNum << ", entry:\t" << entry << "\nArcs:\n";
  for (const auto &A : arcs) OS << A.first << "\t->\t" << A.second << "\n";

  OS << "Updates:\n";
  for (const auto &U : updates)
    OS << ((U.action == Op::Insert) ? "Ins " : "Del ") << U.arc.first
       << "\t->\t" << U.arc.second << "\n";
}
