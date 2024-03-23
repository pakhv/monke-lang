use monke_lang_interpreter::{
    compiler::compiler::Compiler,
    evaluator::{environment::Environment, evaluator::eval, types::Object},
    lexer::lexer::Lexer,
    parser::parser::Parser,
    vm::vm::Vm,
};
use std::{
    cell::RefCell,
    io::{self, Result, Write},
    rc::Rc,
};

const MONKEY_FACE: &str = r#"
             __,__
     .--.  .-"   "-.  .--.
    / .. \/ .-. .-. \/ .. \
    | | '|  /  Y  \  |' | |
    | \  \ \ 0 | 0 / /  / |
     \'- ,\ .-"""-. /, -'/
      ''-' /_ ^ ^ _\ '-''
          | \._ _./ |
          \  \'~'/  /
           '._'-'_.'
             '---'
"#;

fn main() -> Result<()> {
    let mut buffer = String::new();
    io::stdout().write_all(b"Enter your monke code\n>> ")?;
    io::stdout().flush()?;

    let env = Environment::new();
    let env = &Rc::new(RefCell::new(env));

    while let Ok(_) = io::stdin().read_line(&mut buffer) {
        let lexer = Lexer::new(buffer.clone());
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            print_error(err, &mut buffer)?;
        }

        let program = program.unwrap();

        let mut compiler = Compiler::new();

        if let Err(err) = &compiler.compile(program) {
            print_error(err, &mut buffer)?;
        }

        let byte_code = compiler.byte_code();
        let mut vm = Vm::new(byte_code);

        if let Err(err) = &vm.run() {
            print_error(err, &mut buffer)?;
        }

        let stack_elem = vm.stack_top();
        assert!(stack_elem.is_some());
        let stack_elem = stack_elem.unwrap();

        println!("{stack_elem}");

        buffer.clear();
        io::stdout().write_all(b">> ")?;
        io::stdout().flush()?;
    }

    Ok(())
}

fn print_error(error: &str, buffer: &mut String) -> Result<()> {
    println!("{MONKEY_FACE}");
    println!("{error}");

    buffer.clear();
    io::stdout().write_all(b">> ")?;
    io::stdout().flush()
}
