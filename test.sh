#!/usr/bin/env bash

cargo test || exit 1
cargo build || exit 1

for f in examples/*; do
  target/debug/transmute "$f"
done