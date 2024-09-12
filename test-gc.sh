#!/usr/bin/env bash

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  --llvm-ir examples/gc.tm  || exit 1

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  --assembly examples/gc.tm || exit 1

cargo run \
  --features transmute-crt/gc-test \
  --features transmute-llvm/gc-aggressive \
  --bin tmc -- \
  examples/gc.tm            || exit 1

export GC_ENABLE=1
export GC_TEST_DUMP=1
export GC_TEST_VERBOSE=2
export GC_TEST_DUMP_COLOR=1

./gc 1