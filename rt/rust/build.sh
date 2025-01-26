#!/usr/bin/env bash

rm -rf target/release
rm -f target/*.a
mkdir -p target/{obj,test}

clang -c -fPIC support.c -o target/obj/support.o || exit 1
clang -c -fPIC mainrt.c -o target/obj/mainrt.o || exit 1
ar r target/libtmcrt.a target/obj/support.o target/obj/mainrt.o || exit 1
#clang target/obj/*.o -o target/tmcrt.so

cargo fmt || exit 1
cargo test || exit 1
cargo build --features test-wrapper || exit 1

#RUSTFLAGS="--emit=llvm-bc,llvm-ir" cargo build --release || exit 1

# https://stackoverflow.com/questions/3821916/how-to-merge-two-ar-static-libraries-into-one#comment36843318_23621751
ar cqT target/libtmrt.a target/debug/libtransmute_rustrt.a target/libtmcrt.a || exit 1
echo -e 'create target/libtmrt.a\naddlib target/libtmrt.a\nsave\nend' | ar -M || exit 1

clang main.c \
  -L./target -ltmrt \
  -lpthread -lm -ldl -lssl -lcrypto \
  -o target/main || exit 1

RUST_BACKTRACE=1 target/main || exit 1

target/main | grep 'test:' > target/test/out

cat target/test/out | grep expect-live | cut -d: -f3 | sort > target/test/expected-live
cat target/test/out | grep actual-live | cut -d: -f3 | sort > target/test/actual-live

if ! diff --color target/test/expected-live target/test/actual-live; then
  echo -e "\033[0;31mmissing\033[0m vs \033[0;32mshould not be\033[0m"
  exit 1
fi
