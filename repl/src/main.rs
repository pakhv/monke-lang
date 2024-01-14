use monke_lang_interpreter::{
    evaluator::evaluator::eval, lexer::lexer::Lexer, parser::parser::Parser,
};
use std::io::{self, Result, Write};

fn main() -> Result<()> {
    const MONKEY_FACE: &str = r#"
             __,__
     .--.  .-"    "-. .--.
    / .. \/ .-. .-. \/ .. \
    | | '|  /  Y  \  |' | |
    | \  \ \ 0 | 0 / /  / |
     \ '- ,\.-""""-./, -'/
      ''-' /_ ^ ^ _\ '-''
          | \._ _./ |
          \  \'~'/  /
           '._'-'_.'
             '---'
"#;
    let mut buffer = String::new();
    io::stdout().write_all(b"Enter your monke code\n>> ")?;
    io::stdout().flush()?;

    while let Ok(_) = io::stdin().read_line(&mut buffer) {
        let lexer = Lexer::new(buffer.clone());
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        match program {
            Ok(p) => match eval(p) {
                Ok(result) => println!("{}\n", result.to_string()),
                Err(err) => {
                    println!("{MONKEY_FACE}");
                    println!("{err}");
                }
            },
            Err(err) => {
                println!("{MONKEY_FACE}");
                println!("{err}");
            }
        };

        buffer.clear();
        io::stdout().write_all(b">> ")?;
        io::stdout().flush()?;
    }

    Ok(())
}
