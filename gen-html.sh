#!/usr/bin/env bash

rm -rf target/html
mkdir -p target/html

ls src/snapshots | while read -r f; do
  if grep "<!DOCTYPE html>" "src/snapshots/$f" &>/dev/null; then
    sed -n -e '/<!DOCTYPE html>/,$p' "src/snapshots/$f" > "target/html/$f.html"
    echo "Wrote target/html/$f.html"
  fi
done
