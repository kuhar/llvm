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
static cl::opt<std::string> OutputFile("o", cl::desc("<output file>"));

static cl::opt<bool> ToIR("to-ir", cl::desc("Graph to IR"));
static cl::opt<bool> ToGraph("to-graph", cl::desc("IR to graph"));
static cl::opt<unsigned> ApplyUpdates("apply-updates",
                                      cl::desc("Apply updates"), cl::init(0));
static cl::opt<bool> ApplyAll("apply-all", cl::desc("Apply all updates"));
static cl::opt<bool> RunDomTree("run-dom-tree", cl::desc("Run DomTree"),
                                cl::init(true));
static cl::opt<bool> ViewCFG("view-cfg", cl::desc("View CFG"));

enum class InputKind { IR, Graph };

bool isGraphFile(StringRef Filename) {
  return Filename.endswith(".txt");
}

bool isBitcodeFile(StringRef Filename) {
  return Filename.endswith(".bc");
}

bool isIRFile(StringRef Filename) {
  return Filename.endswith(".ll");
}

void updateGraph(InputGraph& IG) {
  unsigned UpdatesRequestes = 0;
  if (ApplyAll)
    UpdatesRequestes = static_cast<unsigned>(-1);
  else
    UpdatesRequestes = ApplyUpdates.getValue();

  Optional<InputGraph::CFGUpdate> Update;
  unsigned UpdatesPerformed = 0;
  while (UpdatesPerformed < UpdatesRequestes &&
         (Update = IG.applyUpdate(false)))
    ++UpdatesPerformed;

  if (UpdatesPerformed < UpdatesRequestes)
    dbgs() << "Requested " << UpdatesRequestes << " updates, performed only "
           << UpdatesPerformed << "\n";

  assert(UpdatesPerformed <= UpdatesRequestes);
}

std::error_code outputGraph(InputGraph &IG) {
  if (OutputFile.empty()) {
    IG.printCurrent(outs());
    return {};
  }

  std::error_code EC;
  raw_fd_ostream Out(OutputFile, EC, sys::fs::OpenFlags::F_None);
  if (EC)
    return EC;

  IG.printCurrent(Out);
  return {};
}

Optional<InputGraph> readGraph() {
  return InputGraph::readFromFile(InputFile);
}

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "dominators");

  if (InputFile.empty()) {
    errs() << "No input file\n";
    return 1;
  }

  if (ToGraph && ToIR) {
    errs() << "Two output type not allowed\n";
    return 1;
  }

  const InputKind Kind = isGraphFile(InputFile) ? InputKind::Graph
                                                : InputKind::IR;

  if (ToGraph && Kind == InputKind::Graph && !ApplyUpdates && !ApplyAll) {
    errs() << "Input and output kinds are the same (graph), but there are " <<
              "no updates to apply\n";
    return 1;
  }

  if (ApplyAll && ApplyUpdates) {
    errs() << "To many update flags\n";
    return 1;
  }

  auto Graph = readGraph();
  if (!Graph) {
    errs() << "Invalid input graph\n";
    return 1;
  }

  dbgs() << "\n\n~~~~~~~~ Input Graph ~~~~~~~~~~~~~~~\n\n";
  Graph->dump();

  if (ToGraph) {
    updateGraph(*Graph);
    auto EC = outputGraph(*Graph);
    if (EC) {
      errs() << "Could not output graph: " << EC.message() << '\n';
      return 1;
    }

    return 0;
  }

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
