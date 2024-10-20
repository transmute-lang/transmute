#!/usr/bin/env bash

clang -c -fPIC print.c -o print.o || exit 1
ar r libprint.a print.o || exit 1
rm print.o || exit 1

cargo fmt || exit 1
cargo test || exit 1
cargo build || exit 1

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -L. -lprint \
  -lpthread -lm -ldl \
  -o main || exit 1

./main