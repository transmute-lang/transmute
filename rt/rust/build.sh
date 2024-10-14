#!/usr/bin/env bash

cargo fmt || exit 1
cargo build || exit 1

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -lpthread -lm -ldl \
  -o main || exit 1

./main