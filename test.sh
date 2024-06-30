#!/usr/bin/env bash

cargo build || exit 1
cargo test #|| exit 1

for f in examples/*; do
  target/debug/transmute "$f" --output-html
done

./gen-html.sh