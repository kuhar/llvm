//===-- dt-benchmark.cpp - DomTrees benchmarking tool  --------------------===//
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

#include <chrono>
#include <fstream>
#include <random>
#include <sstream>

#define DEBUG_TYPE "dt-benchmark"

using namespace llvm;

static cl::opt<std::string> InputFile(cl::Positional, cl::desc("<input file>"),
                                      cl::Required);
static cl::opt<unsigned> Iterations("i", cl::desc("No iterations"),
                                    cl::init(1));

static cl::opt<bool> OldDT("old", cl::desc("Test old DT"));
static cl::opt<bool> NewDT("new", cl::desc("Test new DT"));
static cl::opt<bool> Verify("verify", cl::desc("Verify correctness"),
                            cl::init(false));
static cl::opt<bool> Progress("progress", cl::desc("Show progress"));

extern bool llvm::VerifyDomInfo;
extern void TouchNOP(void *);

static std::unique_ptr<Module> GetModule(StringRef Filename) {
  auto *Context = new LLVMContext();
  SMDiagnostic Diags;
  auto M = parseIRFile(InputFile, Diags, *Context);
  if (!M)
    Diags.print(InputFile.c_str(), errs());

  return M;
}

template <typename F>
std::chrono::microseconds Time(StringRef Desc, F Fun, int No = -1,
                               int Total = -1) {
  const auto StartTime = std::chrono::steady_clock::now();
  Fun();
  const auto EndTime = std::chrono::steady_clock::now();
  const auto ElapsedMs = std::chrono::duration_cast<std::chrono::microseconds>(
      EndTime - StartTime);

  if (Progress) {
    std::string Buff;
    raw_string_ostream RSO(Buff);
    RSO << '[' << No << '/' << Total << "]\t";
    RSO << Desc << "\t" << ElapsedMs.count() << "\tus\n";
    RSO.flush();
    outs() << Buff;
  }
  return ElapsedMs;
};

static void RunOld(Module &M) {
  const int NumFun = M.getFunctionList().size();
  int current = -1;
  std::chrono::microseconds TotalElapsed{0};
  for (auto &F : M.getFunctionList()) {
    if (F.getBasicBlockList().empty())
      continue;

    DEBUG(dbgs() << F.getName() << "\n");

    TotalElapsed += Time("Old DT",
                         [&] {
                           DominatorTree DT(F);
                           TouchNOP(&DT);
                         },
                         ++current, NumFun);
  }

  outs() << "Old DT\t" << TotalElapsed.count() << "\tus\n";
}

static void RunNew(Module &M) {
  const int NumFun = M.getFunctionList().size();
  int current = -1;
  std::chrono::microseconds TotalElapsed{0};
  for (auto &F : M.getFunctionList()) {
    if (F.getBasicBlockList().empty())
      continue;

    DEBUG(dbgs() << F.getName() << "\n");

    TotalElapsed += Time("New DT",
                         [&] {
                           NewDomTree NDT(&F.getEntryBlock());
                           TouchNOP(&NDT);
                           if (VerifyDomInfo)
                             NDT.verify(NewDomTree::Verification::Normal);
                         },
                         ++current, NumFun);
  }

  outs() << "New DT\t" << TotalElapsed.count() << "\tus\n";
}

int main(int argc, char **argv) {
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);
  cl::ParseCommandLineOptions(argc, argv, "dominators");

  auto M = GetModule(InputFile);
  if (!M)
    return 1;

  outs() << "Bitcode read; module has " << M->getFunctionList().size()
         << " functions\n";

  VerifyDomInfo = Verify.getValue();
  if (VerifyDomInfo)
    outs() << "=== Verification on ===\n";

  if (OldDT)
    for (unsigned i = 0; i < Iterations; ++i)
      RunOld(*M);

  if (NewDT)
    for (unsigned i = 0; i < Iterations; ++i)
      RunNew(*M);

  return 0;
}
