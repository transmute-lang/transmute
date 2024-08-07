#!/usr/bin/env bash

rm -rf target/html
mkdir -p target/html

ls hir/src/output/snapshots | while read -r f; do
  if grep "<!DOCTYPE html>" "hir/src/output/snapshots/$f" &>/dev/null; then
    sed -n -e '/<!DOCTYPE html>/,$p' "hir/src/output/snapshots/$f" > "target/html/$f.html"
    echo "Wrote target/html/$f.html"
  fi
done
