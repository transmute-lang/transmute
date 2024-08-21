#!/usr/bin/env bash

export LLVM_SYS_180_PREFIX=/usr/local/llvm-18.1

cargo run -- examples/fibo_rec.tm -o target/fibo_rec
target/fibo_rec 10