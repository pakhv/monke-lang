#[derive(Debug)]
pub enum Token {
    Illegal,
    Eof,
    // Identifiers + literals
    Ident(String),
    Int(String),
    // Operators
    Assign,
    Plus,
    // Delimiters
    Comma,
    Semicolon,
    Lparen,
    Rparen,
    Lbrace,
    Rbrace,
    // Keywords
    Function,
    Let,
}
