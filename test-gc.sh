#!/usr/bin/env bash

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  --llvm-ir examples/gc.tm -o target/gc.ll || exit 1

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  --assembly examples/gc.tm -o target/gc.s || exit 1

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  examples/gc.tm -o target/gc              || exit 1

export GC_ENABLE=1
export GC_TEST_DUMP=1
export GC_TEST_VERBOSE=2
export GC_TEST_DUMP_COLOR=1

target/gc 1