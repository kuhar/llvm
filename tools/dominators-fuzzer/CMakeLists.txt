set(LLVM_LINK_COMPONENTS
    Analysis
    BitReader
    BitWriter
    Core
    IRReader
    Support
    )
add_llvm_tool(dominators-fuzzer
              dominators-fuzzer.cpp)
target_link_libraries(dominators-fuzzer
                      LLVMFuzzer)

