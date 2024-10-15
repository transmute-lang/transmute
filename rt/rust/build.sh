#!/usr/bin/env bash

cargo fmt || exit 1
cargo build || exit 1

clang -c -fPIC println.c -o println.o
ar r libprintln.a println.o
rm println.o

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -L. -lprintln \
  -lpthread -lm -ldl \
  -o main || exit 1

./main