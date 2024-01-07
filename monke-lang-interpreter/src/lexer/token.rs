use std::str::FromStr;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    Illegal,
    // Identifiers + literals
    Ident(String),
    Int(String),
    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    Lt,
    Gt,
    Eq,
    Ne,
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
    True,
    False,
    If,
    Else,
    Return,
}

impl FromStr for Token {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "fn" => Ok(Token::Function),
            "let" => Ok(Token::Let),
            "true" => Ok(Token::True),
            "false" => Ok(Token::False),
            "if" => Ok(Token::If),
            "else" => Ok(Token::Else),
            "return" => Ok(Token::Return),
            ident => Err(format!("Display not implemented for identifier {ident}")),
        }
    }
}
