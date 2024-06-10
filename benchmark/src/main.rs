use std::{cell::RefCell, rc::Rc, str::FromStr, time::SystemTime};

use clap::Parser;
use monke_lang::{
    compiler::compiler::Compiler,
    evaluator::{environment::Environment, evaluator::eval},
    lexer::lexer::Lexer,
    vm::vm::Vm,
};

#[derive(Clone, Debug)]
enum Engine {
    Vm,
    Eval,
}

impl FromStr for Engine {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            vm if vm.to_lowercase() == "vm" => Ok(Engine::Vm),
            eval if eval.to_lowercase() == "eval" => Ok(Engine::Eval),
            str => Err(format!("Couldn't convert \"{str}\" to Engine enum")),
        }
    }
}

#[derive(Parser)]
#[clap(author, version, about)]
struct Arguments {
    #[clap(short = 'H', long, help = "use \"vm\" or \"eval\"")]
    engine: Engine,
}

const INPUT: &str = "
let fibonacci = fn(x) {
    if (x == 0) {
        0
    } else {
        if (x == 1) {
            return 1;
        } else {
            fibonacci(x - 1) + fibonacci(x - 2);
        }
    }
};

fibonacci(30);
";

fn main() {
    let arguments = Arguments::parse();

    let lexer = Lexer::new(INPUT.to_string());
    let mut parser = monke_lang::parser::parser::Parser::new(lexer);

    let program = parser.parse_program().unwrap();

    let (result, duration) = match arguments.engine {
        Engine::Vm => {
            let mut compiler = Compiler::new();
            compiler.compile(program).unwrap();

            let byte_code = compiler.byte_code().unwrap();

            let mut vm = Vm::new(byte_code);

            let start_time = SystemTime::now();
            _ = vm.run();

            (
                vm.last_popped_stack_elem().unwrap(),
                start_time.elapsed().unwrap(),
            )
        }
        Engine::Eval => {
            let env = Environment::new();
            let env = &Rc::new(RefCell::new(env));

            let start_time = SystemTime::now();
            (eval(program, env).unwrap(), start_time.elapsed().unwrap())
        }
    };

    println!(
        "engine={:?} result={result} duration={duration:?}",
        arguments.engine,
    );
}
