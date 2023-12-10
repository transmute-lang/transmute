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