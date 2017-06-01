//===--- fuzz-llvm-as.cpp - Fuzzer for llvm-as using lib/Fuzzer -----------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Build tool to fuzz the LLVM assembler (llvm-as) using
// lib/Fuzzer. The main reason for using this tool is that it is much
// faster than using afl-fuzz, since it is run in-process.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DomSupport.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Program.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"

#include <chrono>
#include <fstream>
#include <random>
#include <sstream>

using namespace llvm;

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *Data, size_t Size) {

  return 0;
}
