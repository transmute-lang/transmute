# transmute

Transmute is a general purpose programming language.

## Examples

### Fibonacci
```
let fibonacci(n: number): number = {
    if n <= 1 {
        ret n;
    }
    fibonacci(n - 1) + fibonacci(n - 2);
}

fibonacci(5);
```

### Factorial
```
let fact(n: number): number = {
    let product = 1;
    while n > 0 {
        product = product * n;
        n = n - 1;
    }
    product;
}

fact(3);
```

# Build
Build + test everything:
```shell
$ ./test.sh
```

## Required dependencies:
### Cargo
```
cargo install cbindgen
cargo install cargo-insta
```

### System
#### LLVM
##### macOS
```
brew install llvm@18
```

##### Linux
* Get clang 18 (on ubuntu: https://ubuntuhandbook.org/index.php/2023/09/how-to-install-clang-17-or-16-in-ubuntu-22-04-20-04/)
    * this install `clang-18` in `/usr/lib/llvm-18/`
* install the requried dependencies: `sudo apt install libpolly-18-dev libzstd-dev libz-dev`
* Make sure:
    * `clang` is in your `PATH` and points to clang-18
    * `llvm-link` is in your `PATH`
