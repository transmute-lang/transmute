#!/usr/bin/env bash

mkdir -p target/

cbindgen --config cbindgen.toml --output bindings/rust.h || exit 1

cargo fmt || exit 1
cargo build || exit 1

CFLAGS="-Wall -Werror -Wpedantic -Wno-zero-length-array"

clang $CFLAGS -c -fPIC -ggdb gc.c -D GC_TEST -D GC_LOGS -o target/gc.o || exit 1
clang $CFLAGS -c -fPIC -ggdb  llvm-support.c -o target/llvm-support.o || exit 1

clang $CFLAGS \
      -D GC_TEST \
      target/llvm-support.o \
      target/gc.o \
      test.c \
      target/debug/libtransmute_rustcrt.a \
      -lpthread -lm -ldl -lssl -lcrypto \
      -ggdb \
      -o target/test || exit 1

if [ "$GC_DEBUG" == 1 ]; then
  GC_TEST_POOL_SIZE=512 \
  GC_LOG_LEVEL=0 \
  gdb --command=gdb.in target/test
else
  GC_TEST_POOL_SIZE=512 \
  GC_LOG_LEVEL=2 \
  GC_TEST_DUMP=0 \
  GC_TEST_DUMP_COLOR=1 \
  target/test
fi