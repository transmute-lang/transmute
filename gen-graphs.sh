#!/usr/bin/env bash

rm -rf target/graphs
mkdir -p target/graphs

echo "<html><body><dl>" >> target/graphs/index.html

ls src/snapshots | while read -r f; do
  if grep "graphviz file" "src/snapshots/$f" &>/dev/null; then
    sed -n -e '/graphviz file/,$p' "src/snapshots/$f" | dot -Tpng > "target/graphs/$f.png"
    echo "<dt>$f</dt><dd><img src=\"$f.png\"></dd>" >> target/graphs/index.html
  fi
done

echo "</dl></body></html>" >> target/graphs/index.html