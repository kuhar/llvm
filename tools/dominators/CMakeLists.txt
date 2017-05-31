set(LLVM_LINK_COMPONENTS
  Analysis
  BitReader
  BitWriter
  Core
  Support
  )

add_llvm_tool(dominators
  dominators.cpp
  )

