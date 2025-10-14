#!/usr/bin/env bash

source setenv

cargo fmt                                                                                                     || exit 1

## prepare stdlib
./build-stdlib.sh                                                                                             || exit 1

## test runtime
pushd runtime                                                                                                 || exit 1
./test.sh                                                                                                     || exit 1
popd                                                                                                          || exit 1

cargo test -p transmute-core                                                                                  || exit 1

cargo test -p transmute-ast                                                                                   || exit 1

cargo test -p transmute-hir                                                                                   || exit 1
#cargo test -p transmute-hir -F gc-functions                                                                   || exit 1

cargo test -p transmute-mir                                                                                   || exit 1

cargo test -p transmute-llvm                                                                                  || exit 1
#cargo test -p transmute-llvm -F gc-functions                                                                  || exit 1
#cargo test -p transmute-llvm -F gc-aggressive                                                                 || exit 1
#cargo test -p transmute-llvm -F gc-functions -F gc-aggressive                                                 || exit 1

cargo test -p tmc                                                                                             || exit 1
#cargo test -p tmc -F rt-c --no-default-features                                                               || exit 1

cargo build -p tmi                                                                                            || exit 1
cargo test -p tmi                                                                                             || exit 1

cargo build --bin tmi --release                                                                               || exit 1
for f in examples/*.tm; do
  if [ "$f" != "examples/arrays_bounds.tm" ]; then
    echo -e "\033[0;34mExecuting ${f} 9 ...\033[0m"
    target/release/tmi "$f" 9                                                                                 #|| exit 1
  fi
done

cargo build --bin tmc --release                                                                               || exit 1

echo "Executing GC test"
./test-gc.sh                                                                                                  || exit 1

echo "OK."