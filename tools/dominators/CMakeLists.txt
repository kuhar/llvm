set(LLVM_LINK_COMPONENTS
  Analysis
  BitReader
  BitWriter
  Core
  IRReader
  Support
  )

add_llvm_tool(dominators
  dominators.cpp
  )

