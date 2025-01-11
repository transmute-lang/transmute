#!/usr/bin/env bash

clang -c -fPIC print.c -o print.o || exit 1
ar r libprint.a print.o || exit 1
rm print.o || exit 1

clang -c -fPIC llvm.c -o llvm.o || exit 1
ar r libllvm.a llvm.o || exit 1
rm llvm.o || exit 1

cargo fmt || exit 1
cargo test || exit 1
cargo build || exit 1

clang main.c \
  -L../../target/debug/ -ltransmute_rustrt \
  -L. -lprint \
  -L. -lllvm \
  -lpthread -lm -ldl \
  -o main || exit 1

RUST_BACKTRACE=1 ./main || exit 1

./main | grep 'test:' > target/test.out

cat target/test.out | grep expect-live | cut -d: -f3 > target/expected
cat target/test.out | grep actual-live | cut -d: -f3 | while read -r actual; do
  if ! grep "$actual" target/expected &>/dev/null; then
    echo "Unexpected live block: $actual"
    cat target/test.out
    exit 1
  fi
done

echo "OK"