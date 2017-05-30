//===-- dominators.cpp - Incremental dominators playground  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DomSupport.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"

#include <fstream>
#include <sstream>

using namespace llvm;

static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input file>"),
                                      cl::init("-"));
static cl::opt<std::string> OutputFile("o", cl::desc("<output file>"),
                                       cl::Required);

static cl::opt<bool> ToIR("to-ir", cl::desc("Graph to IR"));
static cl::opt<bool> ToGraph("to-graph", cl::desc("IR to graph"));
static cl::opt<unsigned> ApplyUpdates("apply-updates", cl::desc("Apply updates"),
                                      cl::init(0));
static cl::opt<bool> ApplyAll("apply-all", cl::desc("Apply all updates"));

static cl::opt<bool> ViewCFG("view-cfg", cl::desc("View CFG"));

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "dominators");

  if (InputFile.empty()) {
    errs() << "No input file\n";
    return 1;
  }

  auto Graph = InputGraph::readFromFile(InputFile);
  if (!Graph) {
    errs() << "Invalid input\n";
    return 0;
  }

  Graph->dump();
  auto *RootBB = Graph->toCFG();

  dbgs() << "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n";

  NewDomTree DT(RootBB);

  if (!DT.verifyAll())
    errs() << "NewDomTree verification failed.\n";

  DT.dump();
  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }

  Optional<InputGraph::CFGUpdate> Update;
  while ((Update = Graph->applyUpdate())) {
    if (Update->action == InputGraph::Op::Insert)
      DT.insertArc(Update->arc.first, Update->arc.second);
    else
      DT.deleteArc(Update->arc.first, Update->arc.second);

    DT.dump();
  }

  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }
}
