#!/usr/bin/env bash

clang -D GC_LOGS -D GC_TEST -c -o gc.o ../c/res/gc.c -fPIC || exit 1
ar r libgc.a gc.o || exit 1
rm gc.o || exit 1

cargo fmt || exit 1
cargo build || exit 1

clang main.c \
  -L../../target/debug -ltransmute_rustrt \
  -L. -lgc \
  -lpthread -lm -ldl \
  -o main || exit 1

export GC_ENABLE=1
export GC_LOG_LEVEL=3
export GC_PRINT_STATS=0
export GC_TEST_DUMP=0
export GC_TEST_DUMP_COLOR=0
export GC_TEST_FINAL_RUN=1
export GC_TEST_POOL_SIZE=2048
./main