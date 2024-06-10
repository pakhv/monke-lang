# monke-lang
Monkey programming language Interpreter and Compiler implementation in Rust. 

Written following the books ["Writing An Interpreter In Go"](https://interpreterbook.com/) and ["Writing A Compiler In Go"](https://compilerbook.com/) by Thorsten Ball (thx to Primeagen for recommendation, *works at Nextflix btw... rust mentioned*).

- The `monke-lang` project consists of: lexer, parser, evaluator, compiler and virtual machine
- The `interpreter-repl` project is a read-eval-print loop for trying an interpreter out
- The `compiler-repl` project is a read-eval-print loop for trying a compiler and vm out
- The `benchmark` project lets you measure time it takes to calculate 35th Fibonacci number using interpreter and vm with compiler*

*somehow I managed to make compiled code execution barely faster than evaluation with interpreter which is kinda impressive ![ICANT somebody help me](https://cdn.7tv.app/emote/60e7328e484ebd628b556b3e/2x.webp)
**benchmark was ran in release mode (otherwise it would take as much time as learning every javascript framework that ever existed)
***`cargo run -r -- --engine=vm` and `cargo run -r -- --engine=eval` to run benchmark

Monkey lang code example:
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
