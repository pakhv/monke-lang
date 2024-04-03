use monke_lang_interpreter::{
    compiler::{compiler::Compiler, symbol_table::SymbolTable},
    evaluator::types::{Null, Object},
    lexer::lexer::Lexer,
    parser::parser::Parser,
    vm::vm::Vm,
};
use std::io::{self, Result, Write};

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

    const GLOBALS_SIZE: usize = 65536;

    let mut constants = vec![];
    let mut globals = vec![Object::Null(Null {}); GLOBALS_SIZE];
    let mut symbols_table = SymbolTable::new();

    while let Ok(_) = io::stdin().read_line(&mut buffer) {
        let lexer = Lexer::new(buffer.clone());
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            print_error(err, &mut buffer)?;
        }

        let program = program.unwrap();

        let mut compiler = Compiler::new_with_state(symbols_table.clone(), constants.clone());

        if let Err(err) = &compiler.compile(program) {
            print_error(err, &mut buffer)?;
            continue;
        }

        symbols_table = compiler.symbol_table.clone();

        let byte_code = compiler.byte_code();
        constants = byte_code.constants.clone();

        let mut vm = Vm::new_with_global_store(byte_code, globals.clone());

        if let Err(err) = &vm.run() {
            print_error(err, &mut buffer)?;
        }

        globals = vm.globals.clone();
        let stack_elem = vm.last_popped_stack_elem();

        match stack_elem {
            Ok(result) => println!("{result}"),
            Err(err) => {
                print_error(&err, &mut buffer)?;
                continue;
            }
        }

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
