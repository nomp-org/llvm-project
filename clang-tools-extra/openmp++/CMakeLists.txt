set(LLVM_LINK_COMPONENTS support)

include_directories(${CMAKE_CURRENT_SOURCE_DIR})

add_clang_executable(omp++ omp++.cxx CodeGen.cpp For.cpp)

clang_target_link_libraries(omp++ PRIVATE
  clangAST
  clangASTMatchers
  clangBasic
  clangLex
  clangDynamicASTMatchers
  clangFrontend
  clangSerialization
  clangRewrite
  clangTooling
)
