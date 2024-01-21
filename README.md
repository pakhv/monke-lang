# monke-lang-interpreter
Monkey programming language interpreter implementation in Rust. Written following the book ["Writing An Interpreter In Go"](https://interpreterbook.com/) by Thorsten Ball (thx to Primeagen for recommendation, *works at Nextflix btw... rust mentioned*).

- The `monke-lang-interpreter` project consists of three main parts: lexer, parser and evaluator
- The `repl` project is a read-eval-print loop for trying the interpreter out

Example of a Monkey code that this interpreter is able to parse and evaluate:
```
let map = fn(arr, f) {
    let iter = fn(arr, accumulated) {
        if (len(arr) == 0) {
            accumulated
        } else {
            iter(rest(arr), push(accumulated, f(first(arr))));
        }
    };

    iter(arr, []);
};

let a = [1, 2, 3, 4];
let double = fn(x) { x * 2 };
map(a, double);
```
