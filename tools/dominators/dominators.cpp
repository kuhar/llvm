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
#include "llvm/IR/CFG.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Dominators.h"
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

using namespace llvm;

static cl::opt<std::string>
    InputFile(cl::Positional, cl::desc("<input file>"), cl::init("-"));
static cl::opt<bool>
    ViewCFG("view-cfg", cl::desc("View CFG"));


using Node = BasicBlock *;
using Index = unsigned;

struct NodeByName {
  bool operator() (const Node first, const Node second) const {
    const auto Cmp = first->getName().compare(second->getName());
    if (Cmp == 0)
      return less{}(first, second);

    return Cmp < 0;
  }
};

class NewDomTree {
public:
  NewDomTree(Node root) : root(root) {}

  void computeDFSNumbering();
  void computeDominators();

  bool contains(Node N) const;
  Node getIDom(Node N) const;
  Index getLevel(Node N) const;
  Node findNCA(Node First, Node Second) const;

  bool verifyAll() const;
  bool verifyWithOldDT() const;
  bool verifyNCA() const;
  bool verifyLevels() const;
  void print(raw_ostream& OS) const;
  void dump() const { print(dbgs()); }

// private: // Public for testing purposes.
  Node root;
  Index currentDFSNum = 0;
  DenseMap<Node, Index> nodeToNum;
  DenseMap<Index, Node> numToNode;
  DenseMap<Node, Node> parents;
  DenseMap<Node, Node> idoms;
  DenseMap<Node, Node> sdoms;
  DenseMap<Node, Index> levels;

  Node getSDomCandidate(Node Start, Node Pred, DenseMap<Node, Node> &Labels);
  using ChildrenTy = DenseMap<Node, SmallVector<Node, 8>>;
  void printImpl(raw_ostream& OS, Node N, const ChildrenTy &Children,
                 std::set<Node, NodeByName> &ToPrint) const;

public:
  void dumpDFSNumbering(raw_ostream& OS = dbgs()) const;
  void addDebugInfoToIR();
  void viewCFG() const { root->getParent()->viewCFG(); }
  void dumpLegacyDomTree(raw_ostream &OS = dbgs()) const {
    DominatorTree DT(*root->getParent());
    DT.print(OS);
  }
};

void NewDomTree::computeDFSNumbering() {
  currentDFSNum = 0;
  parents[root] = root;

  DenseSet<Node> Visited;
  std::vector<Node> WorkList;
  WorkList.push_back(root);

  while (!WorkList.empty()) {
    BasicBlock *BB = WorkList.back();
    WorkList.pop_back();
    if (Visited.count(BB) != 0)
      continue;


    nodeToNum[BB] = currentDFSNum;
    numToNode[currentDFSNum] = BB;
    ++currentDFSNum;

    Visited.insert(BB);
    for (const auto& Succ : reverse(successors(BB)))
      if (Visited.count(Succ) == 0) {
        WorkList.push_back(Succ);
        parents[Succ] = BB;
      }
  }
}

void NewDomTree::computeDominators() {
  DenseMap<Node, Node> Label;

  // Step 0: initialize data structures.
  for (const auto &NodeToNum : nodeToNum) {
    Node N = NodeToNum.first;
    idoms[N] = parents[N];
    sdoms[N] = N;
    Label[N] = N;
  }

  levels[root] = 0;

  // Step 1: compute semidominators.
  assert(currentDFSNum > 0 && "DFS not run?");
  for (Index i = currentDFSNum - 1; i >= 1; --i) {
    auto CurrentNode = numToNode[i];
    for (auto PredNode : predecessors(CurrentNode)) {
      assert(nodeToNum.count(PredNode) != 0);
      Node SDomCandidate = getSDomCandidate(CurrentNode, PredNode, Label);
      if (nodeToNum[sdoms[CurrentNode]] > nodeToNum[sdoms[SDomCandidate]])
        sdoms[CurrentNode] = sdoms[SDomCandidate];
    }
    // Update Label for the current Node.
    Label[CurrentNode] = sdoms[CurrentNode];
  }

  // Step 3: compute immediate dominators as
  //   IDoms[i] = NCA(SDoms[i], SpanningTreeParent(i)).
  // Note that IDoms were initialized to tree parents, so we don't need the
  // original Parents array.
  for (Index i = 1; i < currentDFSNum; ++i) {
    const auto CurrentNode = numToNode[i];
    const auto SDom = sdoms[CurrentNode];
    auto IDomCandidate = idoms[CurrentNode];
    while (nodeToNum[IDomCandidate] > nodeToNum[SDom])
      IDomCandidate = idoms[IDomCandidate];

    idoms[CurrentNode] = IDomCandidate;
    levels[CurrentNode] = levels[IDomCandidate] + 1;
  }
}

// Non-recursive union-find-based semidominator path walker.
Node NewDomTree::getSDomCandidate(const Node Start, const Node Pred,
                                  DenseMap<Node, Node> &Label) {
  assert(Pred != Start && "Not a predecessor");
  const Index StartNum = nodeToNum[Start];
  const Index PredNum = nodeToNum[Pred];

  if (PredNum < StartNum)
    return Pred;

  Node Next = Pred;
  SmallVector<Node, 8> SDomPath;
  // Walk the SDom path up the spanning tree.
  do {
    SDomPath.push_back(Next);
    Next = parents[Next];
  } while (nodeToNum[Next] > StartNum);

  // Compress path.
  for (auto i = SDomPath.size() - 2; i < SDomPath.size(); --i) {
    const auto Current = SDomPath[i];
    const auto Parent = SDomPath[i + 1];

    if (nodeToNum[Label[Current]] > nodeToNum[Label[Parent]])
      Label[Current] = Label[Parent];
    parents[Current] = parents[Parent];
  }

  return Label[Pred];
}

bool NewDomTree::contains(Node N) const {
  return nodeToNum.find(N) != nodeToNum.end();
}

Node NewDomTree::getIDom(Node N) const {
  assert(contains(N));
  const auto it = idoms.find(N);
  assert(it != idoms.end());
  return it->second;
}

Index NewDomTree::getLevel(Node N) const {
  assert(contains(N));
  const auto it = levels.find(N);
  assert(it != levels.end());
  return it->second;
}

Node NewDomTree::findNCA(Node First, Node Second) const {
  if (First == root || Second == root)
    return root;

  while (First != Second) {
    const auto LFIt = levels.find(First);
    assert(LFIt != levels.end());
    const Index LFirst = LFIt->second;

    const auto LSIt = levels.find(Second);
    assert(LSIt != levels.end());
    const Index LSecond = LSIt->second;

    if (LFirst < LSecond)
      std::swap(First, Second);

    const auto it = idoms.find(First);
    assert(it != idoms.end());
    First = it->second;
  }

  return First;
}

bool NewDomTree::verifyAll() const {
  bool IsCorrect = true;

  if (!verifyWithOldDT()) {
    IsCorrect = false;
    errs() << "\nIncorrect domtree!\n";
    dumpLegacyDomTree();
  }

  if (!verifyNCA()) {
    IsCorrect = false;
    errs() << "\nIncorrect NCA!\n";
  }

  if (!verifyLevels()) {
    IsCorrect = false;
    errs() << "\nIncorrect levels!\n";
  }

  return IsCorrect;
}

bool NewDomTree::verifyWithOldDT() const {
  assert(root);
  assert(!nodeToNum.empty());

  DominatorTree DT(*root->getParent());
  bool Correct = true;

  for (const auto& NodeToIDom : idoms) {
    if (NodeToIDom.first == root)
      continue;

    auto Node = NodeToIDom.first;
    auto IDom = NodeToIDom.second;
    auto DTN = DT.getNode(Node);
    auto *CorrectIDom = DTN->getIDom()->getBlock();
    if (CorrectIDom != IDom) {
      errs() << "!! NewDT:\t" << Node->getName() << " -> " <<
                IDom->getName() << "\n   OldDT:\t" << Node->getName() <<
                " -> " << CorrectIDom->getName() << "\n";
      Correct = false;
    }
  }

  return Correct;
}

bool NewDomTree::verifyNCA() const {
  Function *F = root->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB))
      continue;

    // For every arc U -> V in the graph, NCA(U, V) = idoms[V] or V.
    for (auto *Succ : successors(&BB)) {
      // dbgs() << "Checking NCA(" << BB.getName() << ", " << Succ->getName() <<
      //          ")\n";

      auto NCA = findNCA(&BB, Succ);
      if (NCA != Succ && NCA != getIDom(Succ)) {
        Correct = false;
        dbgs() << "Error:\tNCA(" << BB.getName() << ", " << Succ->getName() <<
                  ") = " << NCA->getName();
      }
    }
  }

  return Correct;
}

bool NewDomTree::verifyLevels() const {
  Function *F = root->getParent();
  bool Correct = true;
  for (auto &BB : *F) {
    if (!contains(&BB) || &BB == root)
      continue;

    const Index BBL = getLevel(&BB);
    const auto IDom = getIDom(&BB);
    const Index IDomL = getLevel(IDom);
    if (BBL != (IDomL + 1)) {
      Correct = false;
      dbgs() << "Error:\tLevel(" << BB.getName() << ") = " << BBL << ", " <<
             "Level(" << IDom << ") = " << IDomL << "\n";
    }
  }

  return Correct;
}

void NewDomTree::print(raw_ostream& OS) const {
  assert(!idoms.empty());
  std::set<Node, NodeByName> ToPrint;
  ChildrenTy Children;

  for (const auto &NodeToIDom : idoms) {
    Children[NodeToIDom.second].push_back(NodeToIDom.first);
    ToPrint.insert(NodeToIDom.first);
  }

  dbgs() << "\nPreorder New Dominator Tree:\n";
  while (!ToPrint.empty())
    printImpl(OS, *ToPrint.begin(), Children, ToPrint);
  dbgs() << "\n";
}

void NewDomTree::printImpl(raw_ostream &OS, Node N, const ChildrenTy &Children,
                           std::set<Node, NodeByName> &ToPrint) const {
  ToPrint.erase(N);
  const auto LevelIt = levels.find(N);
  assert(LevelIt != levels.end());
  const auto Level = LevelIt->second;
  for (Index i = 0; i <= Level; ++i)
    OS << "  ";

  const auto NodeNumIt = nodeToNum.find(N);
  assert(NodeNumIt != nodeToNum.end());
  OS << '[' << (Level + 1) << "] %" << N->getName() << " {" <<
        NodeNumIt->second << "}\n";

  const auto ChildrenIt = Children.find(N);
  if (ChildrenIt == Children.end())
    return;

  std::vector<Node> SortedChildren(ChildrenIt->second.begin(),
                                   ChildrenIt->second.end());
  std::sort(SortedChildren.begin(), SortedChildren.end());
  for (const auto& C : SortedChildren)
    if (ToPrint.count(C) != 0)
      printImpl(OS, C, Children, ToPrint);
}

void NewDomTree::dumpDFSNumbering(raw_ostream &OS) const {
  OS << "\nDFSNumbering:\n";
  OS << "\tnodeToNum size:\t" << nodeToNum.size() << "\n";
  OS << "\tparents size:\t" << parents.size() << "\n";

  using KeyValue = std::pair<Node, Index>;
  std::vector<KeyValue> Sorted(nodeToNum.begin(),
                                             nodeToNum.end());

  sort(Sorted.begin(), Sorted.end(), [](KeyValue first, KeyValue second) {
    return first.first->getName().compare(second.first->getName()) < 0;
  });

  for (const auto &NodeToNum : Sorted)
    OS << NodeToNum.first->getName() << " {" << NodeToNum.second << "}\n";
}

void NewDomTree::addDebugInfoToIR() {
  auto M = root->getParent()->getParent();
  auto *IntTy = IntegerType::get(M->getContext(), 1);

  for (const auto& NodeToIDom : idoms) {
    auto BB = NodeToIDom.first;
    auto SD = sdoms[BB];
    auto ID = NodeToIDom.second;

    std::string Buffer;
    raw_string_ostream RSO(Buffer);
    IRBuilder<> Builder(BB, BB->begin());

    RSO << "idom___" << ID->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
    Buffer.clear();

    RSO << "sdom___" << SD->getName() << "___";
    RSO.flush();
    Builder.CreateAlloca(IntTy, nullptr, Buffer);
  }
}

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

  void dump(raw_ostream &OS = dbgs()) {
    OS << "Nodes:\t" << nodesNum << ", entry:\t" << entry << "\nArcs:\n";
    for (const auto &A : arcs)
      OS << A.first << "\t->\t" << A.second << "\n";
    OS << "Updates:\n";
    for (const auto &U : updates) {
      OS << ((U.action == Op::Insert) ? "Ins " : "Del ") << U.arc.first <<
            "\t->\t" << U.arc.second << "\n";
    }
  }

  std::unique_ptr<GraphCFG> toCFG() const;
};

InputGraph readInputGraph(std::string path) {
  dbgs() << "Reading input graph: " << path << "\n";
  std::ifstream IFS(path);
  dbgs() << IFS.good() << "\n";
  InputGraph Graph;

  for (std::string Line; std::getline(IFS, Line) && !Line.empty();) {
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
  std::vector<SmallVector<BasicBlock *, 4>> Children(nodesNum);

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

  dbgs() << "\n\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n";

  NewDomTree DT(&CFG->function->getEntryBlock());
  DT.computeDFSNumbering();
  DT.dumpDFSNumbering();
  DT.computeDominators();

  if (!DT.verifyAll()) {
    errs() << "NewDomTree verification failed.\n";
  }
  DT.dump();

  if (ViewCFG) {
    DT.addDebugInfoToIR();
    DT.viewCFG();
  }
}
