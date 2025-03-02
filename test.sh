#!/usr/bin/env bash

source .env
export LLVM_SYS_180_PREFIX
export LIBTRANSMUTE_STDLIB_PATH

cargo fmt                                                                                                     || exit 1

pushd runtime                                                                                                 || exit 1
./build.sh                                                                                                    || exit 1
popd                                                                                                          || exit 1

#cargo test -p transmute-stdlib                                                                                || exit 1
cargo build -p transmute-stdlib                                                                               || exit 1

cargo test -p transmute-core                                                                                  || exit 1

cargo test -p transmute-ast                                                                                   || exit 1

cargo test -p transmute-hir                                                                                   || exit 1
#cargo test -p transmute-hir -F gc-functions                                                                   || exit 1

cargo test -p transmute-mir                                                                                   || exit 1

cargo test -p transmute-llvm -F runtime                                                                       || exit 1
#cargo test -p transmute-llvm -F runtime -F gc-functions                                                       || exit 1
#cargo test -p transmute-llvm -F runtime -F gc-aggressive                                                      || exit 1
#cargo test -p transmute-llvm -F runtime -F gc-functions -F gc-aggressive                                      || exit 1
cargo test -p transmute-llvm -F rt-c                                                                          || exit 1
#cargo test -p transmute-llvm -F rt-c -F gc-functions                                                          || exit 1
#cargo test -p transmute-llvm -F rt-c -F gc-aggressive                                                         || exit 1
#cargo test -p transmute-llvm -F rt-c -F gc-functions -F gc-aggressive                                         || exit 1

cargo test -p tmc                                                                                             || exit 1
#cargo test -p tmc -F rt-c --no-default-features                                                               || exit 1

cargo build -p tmi                                                                                            || exit 1
cargo test -p tmi                                                                                             || exit 1

cargo build --bin tmi --release                                                                               || exit 1
for f in examples/*.tm; do
  echo -e "\e[0;34mExecuting ${f} ...\e[0m"
  target/release/tmi "$f" 9                                                                                   #|| exit 1
done

cargo build --bin tmc --release                                                                               || exit 1

./test-gc.sh                                                                                                  || exit 1

echo "OK."