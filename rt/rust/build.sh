#!/usr/bin/env bash

#clang -c -fPIC print.c -o print.o || exit 1
#ar r libprint.a print.o || exit 1
#rm print.o || exit 1
#
#clang -c -fPIC llvm.c -o llvm.o || exit 1
#ar r libllvm.a llvm.o || exit 1
#rm llvm.o || exit 1

mkdir -p target

clang -c -fPIC support.c -o target/support.o || exit 1
ar r target/libsupport.a target/support.o || exit 1
#rm support.o || exit 1

cargo fmt || exit 1
cargo test || exit 1
cargo build || exit 1

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -Ltarget -lsupport \
  -lpthread -lm -ldl \
  -o target/main || exit 1

RUST_BACKTRACE=1 target/main || exit 1

target/main | grep 'test:' > target/test.out

cat target/test.out | grep expect-live | cut -d: -f3 | sort > target/expected-live
cat target/test.out | grep actual-live | cut -d: -f3 | sort > target/actual-live

if ! diff --color target/expected-live target/actual-live; then
  echo -e "\033[0;31mmissing\033[0m vs \033[0;32mshould not be\033[0m"
  exit 1
fi

echo
echo
echo
echo
echo "todo: generate LLVM IR for"
echo "  cargo build"
echo "  support.c (without LlvmStackFrame *gc_root)"
echo
echo
echo
echo
