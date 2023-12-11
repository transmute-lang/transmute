# Specification

## Variables
Variables are declared with the `let` keyword, followed by an equal sign and an expression:
```
let x = 0;
```

Variables can be shadowed as such:
```
let x = 0;
let x = 1;
```
the variable `x` is 1, and the second `let` shadows the first one.

### Issues / improvements

## Function
As variables, functions are declared with the `let` keyword:
```
let f(a: number, b: number): number = {
    ...
}
```
The curly braces can be omitted if the function is composed of only one expression:
```
let f(a: number, b: number): number = ...;
```
Functions of a given signature (same name, same parameter types) can only be declared once in their scope.

### Issues / improvements
 - function parameters cannot be reassigned
 - make the `=` optional when using the curly braces version
 - do not allow a function to be redefined in the same scope