#!/usr/bin/env bash

mkdir -p "$TRANSMUTE_STDLIB_PATH"

pushd ../stdlib || exit 1
cargo build
popd || exit 1

cp ../target/debug/libtransmute_stdlib.a "$TRANSMUTE_STDLIB_PATH"

mkdir -p target

clang -ggdb -Wall -Werror -Wpedantic -Wno-zero-length-array \
  -D GC_TEST \
  -D GC_LOGS \
  -D GC_LOGS_COLOR \
  -D GC_PTHREAD \
  src/runtimelib/rtlib.c \
  src/gc/gc.c \
  test/test.c \
  "$TRANSMUTE_STDLIB_PATH/libtransmute_stdlib.a" \
  -lpthread -lm -ldl \
  -o target/test || exit 1

if [ "$GC_DEBUG" == 1 ]; then
  GC_TEST_POOL_SIZE=704 \
  GC_LOG_LEVEL=0 \
  gdb --command=gdb.in target/test
else
  GC_TEST_POOL_SIZE=704 \
  GC_LOG_LEVEL=2 \
  GC_TEST_DUMP=0 \
  GC_TEST_DUMP_COLOR=1 \
  GC_TEST_STEP=0 \
  GC_PRINT_STATS=1 \
  target/test
fi