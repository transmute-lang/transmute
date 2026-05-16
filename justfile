export TRANSMUTE_STDLIB_PATH := "target/debug/transmute-stdlib/"
export TRANSMUTE_STDLIB := "transmute_stdlib"

@build-stdlib:
    cargo build -p transmute-stdlib
    rm -rf target/debug/transmute-stdlib
    mkdir -p "$TRANSMUTE_STDLIB_PATH/src/stdlib"
    cp target/debug/lib$TRANSMUTE_STDLIB.a "$TRANSMUTE_STDLIB_PATH"
    cp stdlib/src/stdlib/*.tm "$TRANSMUTE_STDLIB_PATH"/src/stdlib
    cp stdlib/src/stdlib.tm "$TRANSMUTE_STDLIB_PATH"/src/

ensure-stdlib:
    #!/usr/bin/env sh
    [ -d "$TRANSMUTE_STDLIB_PATH/src/stdlib" ] || just build-stdlib

@build-test-runtime: build-stdlib
    mkdir -p target/runtime
    clang -ggdb -Wall -Werror -Wpedantic -Wno-zero-length-array \
      -D GC_TEST \
      -D GC_LOGS \
      -D GC_LOGS_COLOR \
      -D GC_PTHREAD \
      runtime/src/runtimelib/rtlib.c \
      runtime/src/gc/codegen-llvm/gc.c \
      runtime/test/test.c \
      "$TRANSMUTE_STDLIB_PATH/lib$TRANSMUTE_STDLIB.a" \
      -lpthread -lm -ldl \
      -o target/runtime/test

@test-runtime: build-test-runtime
    GC_TEST_POOL_SIZE=704 \
      GC_LOG_LEVEL=2 \
      GC_TEST_DUMP=0 \
      GC_TEST_DUMP_COLOR=1 \
      GC_TEST_STEP=0 \
      GC_PRINT_STATS=1 \
      target/runtime/test

@build-runtime: test-runtime
    cargo build -p transmute-runtime

@debug-runtime: build-test-runtime
    GC_TEST_POOL_SIZE=704 \
      GC_LOG_LEVEL=0 \
      gdb --command=gdb.in target/test

@eval e n:
    cargo run --bin tmi -- examples/{{e}}.tm
    ./{{e}} {{n}}

@compile e:
    cargo run --bin tmc -- examples/{{e}}.tm -o target/{{e}}

@exec e n: (compile e)
    mkdir -p target/exec-llvm-out/
    target/{{e}} {{n}}

exec-all:
    #!/usr/bin/env sh
    for f in examples/*.tm; do
      n="$(head -n1 "$f" | tr -d '#')"
      just exec "$(basename "$f" ".tm")" "$n"
    done

@compile-to-c e:
    cargo run --bin tmc -- --c examples/{{e}}.tm -o target/{{e}}.c

@compile-c e: ensure-stdlib (compile-to-c e)
    clang -o target/{{e}} target/{{e}}.c -L"$TRANSMUTE_STDLIB_PATH" -l$TRANSMUTE_STDLIB

@exec-c e n: (compile-c e)
    mkdir -p target/exec-c-out/
    target/{{e}} {{n}}

exec-c-all:
    #!/usr/bin/env sh
    for f in examples/*.tm; do
      n="$(head -n1 "$f" | tr -d '#')"
      just exec-c "$(basename "$f" ".tm")" "$n"
    done

test-exec:
    #!/usr/bin/env sh
    rm -rf target/exec-llvm-out/
    rm -rf target/exec-c-out/
    mkdir -p target/exec-llvm-out/
    mkdir -p target/exec-c-out/
    just build-runtime
    cargo build --bin tmc
    for f in examples/*.tm; do
      n="$(head -n1 "$f" | tr -d '#')"
      name="$(basename "$f" ".tm")"
      target/debug/tmc "examples/$name.tm" -o "target/$name-llvm"
      if [ -f "target/$name-llvm" ]; then
        "target/$name-llvm" "$n" \
          > target/exec-llvm-out/$name.stdout \
          2> target/exec-llvm-out/$name.stderr \
          && echo Ok $name \
          || echo Error $name
      fi
      target/debug/tmc --c "examples/$name.tm" -o "target/$name.c"
      clang -o "target/$name-c" "target/$name.c" -L"$TRANSMUTE_STDLIB_PATH" -l$TRANSMUTE_STDLIB
      if [ -f "target/$name-c" ]; then
        "target/$name-c" "$n" \
          > target/exec-c-out/$name.stdout \
          2> target/exec-c-out/$name.stderr \
          && echo Ok $name \
          || echo Error $name
        fi
    done
    echo;echo;echo
    diff -y target/exec-llvm-out target/exec-c-out
