use lexer::token::Token;

mod lexer;

#[derive(Debug, Default)]
pub struct Lexer {
    pub input: Vec<char>,
    pub read_position: usize,
    pub ch: Option<char>,
}

impl Lexer {
    pub fn new(input: String) -> Self {
        let mut lexer = Lexer {
            input: input.chars().collect(),
            ..Default::default()
        };
        lexer.advance();

        lexer
    }

    pub fn advance(&mut self) {
        self.ch = self.input.get(self.read_position).copied();
        self.read_position += 1;
    }

    fn advance_and_return(&mut self, token: Token) -> Option<Token> {
        self.advance();
        Some(token)
    }

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespaces();

        match self.ch {
            None => None,
            Some(ch) => match ch {
                '=' => self.advance_and_return(Token::Assign),
                ';' => self.advance_and_return(Token::Semicolon),
                '(' => self.advance_and_return(Token::Lparen),
                ')' => self.advance_and_return(Token::Rparen),
                '{' => self.advance_and_return(Token::Lbrace),
                '}' => self.advance_and_return(Token::Rbrace),
                ',' => self.advance_and_return(Token::Comma),
                '+' => self.advance_and_return(Token::Plus),
                ch if is_letter(ch) => {
                    let ident = self.read_while(&is_letter);
                    Some(lookup_ident(ident))
                }
                ch if is_digit(ch) => {
                    let number = self.read_while(&is_digit);
                    Some(Token::Int(number))
                }
                ch => panic!("Unknown character {ch}"),
            },
        }
    }

    fn read_while(&mut self, condition: &dyn Fn(char) -> bool) -> String {
        let mut buffer = String::new();

        while let Some(ch) = self.ch {
            if condition(ch) {
                buffer.push(ch);
            } else {
                break;
            }

            self.advance();
        }

        buffer
    }

    fn skip_whitespaces(&mut self) {
        loop {
            if self.ch.is_none() {
                break;
            }

            let ch = self.ch.unwrap();
            if ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' {
                self.advance();
                continue;
            }

            break;
        }
    }
}

fn is_digit(ch: char) -> bool {
    match ch as u8 {
        b'0'..=b'9' => true,
        _ => false,
    }
}

fn is_letter(ch: char) -> bool {
    match ch as u8 {
        b'a'..=b'z' | b'A'..=b'Z' | b'_' => true,
        _ => false,
    }
}

fn lookup_ident(ident: String) -> Token {
    match ident.as_str() {
        "let" => Token::Let,
        "fn" => Token::Function,
        _ => Token::Ident(ident),
    }
}

#[cfg(test)]
mod tests {
    use crate::{lexer::token::Token, Lexer};

    #[test]
    fn lexer_next_token_test_simple() {
        let input = "=+(){},;";
        let mut lexer = Lexer::new(String::from(input));

        let expected_tokens = vec![
            Token::Assign,
            Token::Plus,
            Token::Lparen,
            Token::Rparen,
            Token::Lbrace,
            Token::Rbrace,
            Token::Comma,
            Token::Semicolon,
        ];

        for expected_token in expected_tokens {
            assert_eq!(lexer.next_token().unwrap(), expected_token);
        }
    }

    #[test]
    fn lexer_next_token_test() {
        let input = r#"let five = 5;
let ten = 10;
let add = fn(x, y) {
    x + y;
};
let result = add(five, ten);"#;

        let mut lexer = Lexer::new(String::from(input));

        let expected_tokens = vec![
            Token::Let,
            Token::Ident(String::from("five")),
            Token::Assign,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("ten")),
            Token::Assign,
            Token::Int(String::from("10")),
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("add")),
            Token::Assign,
            Token::Function,
            Token::Lparen,
            Token::Ident(String::from("x")),
            Token::Comma,
            Token::Ident(String::from("y")),
            Token::Rparen,
            Token::Lbrace,
            Token::Ident(String::from("x")),
            Token::Plus,
            Token::Ident(String::from("y")),
            Token::Semicolon,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident(String::from("result")),
            Token::Assign,
            Token::Ident(String::from("add")),
            Token::Lparen,
            Token::Ident(String::from("five")),
            Token::Comma,
            Token::Ident(String::from("ten")),
            Token::Rparen,
            Token::Semicolon,
        ];

        for expected_token in expected_tokens {
            assert_eq!(lexer.next_token().unwrap(), expected_token);
        }
    }
}
