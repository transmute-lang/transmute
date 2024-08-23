#!/usr/bin/env bash

export LLVM_SYS_180_PREFIX=/usr/local/llvm-18.1

cargo build || exit 1
cargo test --workspace --no-fail-fast
