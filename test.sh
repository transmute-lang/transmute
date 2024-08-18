#!/usr/bin/env bash

export LLVM_SYS_180_PREFIX=/usr/local/llvm-18.1

cargo build || exit 1
cargo test #|| exit 1

for f in examples/*; do
  echo -e "\e[0;34mExecuting ${f} ...\e[0m"
  target/debug/tmi "$f" --output-html
done

./gen-html.sh