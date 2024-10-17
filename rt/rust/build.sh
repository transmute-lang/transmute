#!/usr/bin/env bash

cargo fmt || exit 1
cargo test || exit 1
cargo build || exit 1

clang -c -fPIC print.c -o print.o
ar r libprint.a print.o
rm print.o

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -L. -lprint \
  -lpthread -lm -ldl \
  -o main || exit 1

./main