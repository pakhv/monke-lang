use monke_lang_interpreter::lexer::lexer::Lexer;
use std::io::{self, Result, Write};

fn main() -> Result<()> {
    let mut buffer = String::new();
    io::stdout().write_all(b"Enter your monke code >> ")?;
    io::stdout().flush()?;

    while let Ok(_) = io::stdin().read_line(&mut buffer) {
        let mut lexer = Lexer::new(buffer.clone());

        while let Some(token) = lexer.next_token() {
            println!("{token:?}");
        }

        buffer.clear();
        io::stdout().write_all(b">> ")?;
        io::stdout().flush()?;
    }

    Ok(())
}
