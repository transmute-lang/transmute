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
## Required dependencies:
### Cargo
```
cargo install --force cbindgen
```

### System
#### LLVM
##### macOS
```
brew install llvm@18
```

##### Linux
Download and compile LLVM 18, put it in /usr/local/llvm-18.1