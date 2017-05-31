//===-- dominators.cpp - Incremental dominators playground  ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DomSupport.h"

#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"

#include <fstream>
#include <sstream>

#define DEBUG_TYPE "dominators"

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

static bool isGraphFile(StringRef Filename) {
  return Filename.endswith(".txt");
}

static bool isIRFile(StringRef Filename) { return Filename.endswith(".ll"); }

static bool isBitcodeFile(StringRef Filename) {
  return Filename.endswith(".bc");
}

static void updateGraph(InputGraph &IG, bool UpdateIR) {
  unsigned UpdatesRequested = 0;
  if (ApplyAll)
    UpdatesRequested = static_cast<unsigned>(-1);
  else
    UpdatesRequested = ApplyUpdates.getValue();

  Optional<InputGraph::CFGUpdate> Update;
  unsigned UpdatesPerformed = 0;
  while (UpdatesPerformed < UpdatesRequested &&
         (Update = IG.applyUpdate(UpdateIR)))
    ++UpdatesPerformed;

  if (UpdatesPerformed < UpdatesRequested)
    dbgs() << "Requested " << UpdatesRequested << " updates, performed only "
           << UpdatesPerformed << "\n";

  assert(UpdatesPerformed <= UpdatesRequested);
}

static std::error_code outputGraph(InputGraph &IG) {
  if (OutputFile.empty()) {
    IG.printCurrent(outs());
    return {};
  }

  std::error_code EC;
  raw_fd_ostream Out(OutputFile, EC, sys::fs::OpenFlags::F_None);
  if (EC) return EC;

  IG.printCurrent(Out);
  return {};
}

static std::error_code outputIR(InputGraph &IG) {
  if (OutputFile.empty()) {
    IG.cfg->module.print(outs(), nullptr);
    return {};
  }
  std::error_code EC;
  raw_fd_ostream Out(OutputFile, EC, sys::fs::OpenFlags::F_None);
  if (EC) return EC;

  if (isIRFile(OutputFile)) {
    IG.cfg->module.print(Out, nullptr);
    return {};
  }

  WriteBitcodeToFile(&IG.cfg->module, Out);
  return {};
}

static Optional<InputGraph> readGraph() {
  if (isIRFile(InputFile)) {
    errs() << "The tool cannot read textual IR files\n";
    return None;
  }

  if (isGraphFile(InputFile)) return InputGraph::readFromFile(InputFile);

  if (isBitcodeFile(InputFile)) {
    auto *Context = new LLVMContext();
    SMDiagnostic Diags;
    auto M = parseIRFile(InputFile, Diags, *Context);
    if (!M) {
      Diags.print(InputFile.c_str(), errs());
      return None;
    }

    if (M->getFunctionList().size() != 1) {
      errs() << "Input modules must have exactly one function, not "
             << M->getFunctionList().size() << "\n";
      return None;
    }

    if (ViewCFG) M->getFunctionList().front().viewCFG();

    return InputGraph::fromModule(*M);
  }

  errs() << "Unknown file format for " << InputFile << "\n";
  return None;
}

static bool validateConsoleFlags() {
  if (InputFile.empty()) {
    errs() << "No input file\n";
    return false;
  }

  if (ToGraph && ToIR) {
    errs() << "Two output type not allowed\n";
    return false;
  }

  const InputKind Kind =
      isGraphFile(InputFile) ? InputKind::Graph : InputKind::IR;

  if (ToGraph && Kind == InputKind::Graph && !ApplyUpdates && !ApplyAll) {
    errs() << "Input and output kinds are the same (graph), but there are "
           << "no updates to apply\n";
    return false;
  }

  if (ApplyAll && ApplyUpdates) {
    errs() << "To many update flags\n";
    return false;
  }

  return true;
}

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "dominators");

  if (!validateConsoleFlags()) return 1;

  auto Graph = readGraph();
  if (!Graph) {
    errs() << "Invalid input graph\n";
    return 1;
  }

  DEBUG(dbgs() << "\n\n~~~~~~~~ Input Graph ~~~~~~~~~~~~~~~\n\n");
  DEBUG(Graph->dump());

  if (ToGraph) {
    updateGraph(*Graph, false);
    const auto EC = outputGraph(*Graph);
    if (EC) {
      errs() << "Could not output graph: " << EC.message() << '\n';
      return 1;
    }

    return 0;
  }

  auto *RootBB = Graph->toCFG();
  if (ViewCFG) RootBB->getParent()->viewCFG();

  if (ToIR) {
    auto EC = outputIR(*Graph);
    if (EC) {
      errs() << "Could not output IR: " << EC.message() << '\n';
      return 1;
    }

    return 0;
  }

  NewDomTree DT(RootBB);

  if (!DT.verifyAll()) errs() << "NewDomTree verification failed.\n";

  DT.dump();

  Optional<InputGraph::CFGUpdate> Update;
  while ((Update = Graph->applyUpdate())) {
    if (Update->action == InputGraph::Op::Insert)
      DT.insertArc(Update->arc.first, Update->arc.second);
    else
      DT.deleteArc(Update->arc.first, Update->arc.second);

    DEBUG(DT.dump());
  }

  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }
}
