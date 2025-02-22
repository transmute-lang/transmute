#!/usr/bin/env bash

RUSTUP_TOOLCHAIN=nightly \
  cbindgen --config cbindgen.toml --output bindings/transmute-stdlib.h
