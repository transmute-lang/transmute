#!/usr/bin/env bash

pushd ../stdlib || exit 1
cargo build
./cbindgen.sh
popd || exit 1

mkdir -p target/

CFLAGS="-Wall -Werror -Wpedantic -Wno-zero-length-array"

clang $CFLAGS -c -fPIC -ggdb src/gc/gc.c -D GC_TEST -D GC_LOGS -D GC_LOGS_COLOR -D GC_PTHREAD -o target/gc.o || exit 1

clang $CFLAGS \
      -D GC_TEST \
      target/gc.o \
      test/test.c \
      ../stdlib/target/debug/libtransmute_stdlib.a \
      -lpthread -lm -ldl -lssl -lcrypto \
      -ggdb \
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
  GC_PRINT_STATS=1 \
  target/test
fi