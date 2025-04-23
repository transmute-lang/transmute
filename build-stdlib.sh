#!/usr/bin/env bash

#cargo test -p transmute-stdlib                                                                                || exit 1
cargo build -p transmute-stdlib                                                                               || exit 1
rm -rf target/debug/transmute-stdlib                                                                          || exit 1
mkdir -p target/debug/transmute-stdlib/src/stdlib                                                             || exit 1
cp target/debug/libtransmute_stdlib.a target/debug/transmute-stdlib/                                          || exit 1
cp stdlib/src/stdlib/*.tm target/debug/transmute-stdlib/src/stdlib                                            || exit 1
cp stdlib/src/stdlib.tm target/debug/transmute-stdlib/src/                                                    || exit 1