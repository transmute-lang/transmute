#!/usr/bin/env bash

cargo run --bin tmc -- --llvm-ir examples/gc.tm  || exit 1
cargo run --bin tmc -- --assembly examples/gc.tm || exit 1
cargo run --bin tmc -- examples/gc.tm            || exit 1

export GC_ENABLE=1
export GC_TEST_DUMP=1
export GC_TEST_VERBOSE=2
export GC_TEST_DUMP_COLOR=1

./gc 1