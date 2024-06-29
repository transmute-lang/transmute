#!/usr/bin/env bash

cargo build

for f in examples/*; do
  target/debug/transmute "$f"
done