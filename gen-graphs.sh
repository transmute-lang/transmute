#!/usr/bin/env bash

rm -rf target/graphs
mkdir -p target/graphs

ls src/snapshots | while read -r f; do
  if grep "graphviz file" "src/snapshots/$f" &>/dev/null; then
    sed -n -e '/graphviz file/,$p' "src/snapshots/$f" | dot -Tpng > "target/graphs/$f.png"
  fi
done
