#!/usr/bin/env bash

# https://lib.rs/crates/cargo-llvm-cov

source <(cargo llvm-cov show-env --export-prefix)

cargo llvm-cov clean --workspace
cargo build
cargo test --workspace
cargo llvm-cov report --html --hide-instantiations