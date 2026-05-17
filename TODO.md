# Testing strategy
1. should every module test the content of examples (harder from the mir pass)?
2. some modules are missing smaller tests
   1. hir/hir_print
   2. ast/ast_print
3. some don't but could:
   1. ast/pretty_print
   2. nst/*
4. compiler integration tests can be replaced with e2e-tests
5. llvm integration tests can be replaced with e2e-tests

# Code reorg.
1. Move llvm to codegen/
2. review the runtime: move the llvm parts where they belong (llvm vs c)

# Compilation
1. Pre-build the runtime and link it (same as with the stdlib)