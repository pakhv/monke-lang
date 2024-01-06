use std::str::FromStr;

use super::token::Token;

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

    pub fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespaces();

        match self.ch {
            None => None,
            Some(ch) => match ch {
                ';' => self.advance_and_return(Token::Semicolon),
                '(' => self.advance_and_return(Token::Lparen),
                ')' => self.advance_and_return(Token::Rparen),
                '{' => self.advance_and_return(Token::Lbrace),
                '}' => self.advance_and_return(Token::Rbrace),
                ',' => self.advance_and_return(Token::Comma),
                '+' => self.advance_and_return(Token::Plus),
                '-' => self.advance_and_return(Token::Minus),
                '*' => self.advance_and_return(Token::Asterisk),
                '/' => self.advance_and_return(Token::Slash),
                '<' => self.advance_and_return(Token::Lt),
                '>' => self.advance_and_return(Token::Gt),
                '=' => self.peeked_token('=', Token::Eq, Token::Assign),
                '!' => self.peeked_token('=', Token::Ne, Token::Bang),
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

    fn advance(&mut self) {
        self.ch = self.input.get(self.read_position).copied();
        self.read_position += 1;
    }

    fn advance_and_return(&mut self, token: Token) -> Option<Token> {
        self.advance();
        Some(token)
    }

    fn peek(&self) -> Option<char> {
        self.input.get(self.read_position).copied()
    }

    fn peeked_token(
        &mut self,
        expected: char,
        matched_token: Token,
        not_matched_token: Token,
    ) -> Option<Token> {
        let token = match self.peek() {
            Some(ch) if ch == expected => self.advance_and_return(matched_token),
            None | Some(_) => Some(not_matched_token),
        };

        self.advance();
        token
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
    match ch {
        '0'..='9' => true,
        _ => false,
    }
}

fn is_letter(ch: char) -> bool {
    match ch {
        'a'..='z' | 'A'..='Z' | '_' => true,
        _ => false,
    }
}

fn lookup_ident(ident: String) -> Token {
    let special_key_ident = Token::from_str(&ident);

    match special_key_ident {
        Ok(ident) => ident,
        Err(_) => Token::Ident(ident),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_next_token_test() {
        let input = r#"let five = 5;
let ten = 10;
let add = fn(x, y) {
    x + y;
};

let result = add(five, ten);
!-/*5;
5 < 10 > 5;

if (5 < 10) {
    return true;
} else {
    return false;
}

10 == 10;
10 != 9;"#;

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
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::Int(String::from("5")),
            Token::Lt,
            Token::Int(String::from("10")),
            Token::Gt,
            Token::Int(String::from("5")),
            Token::Semicolon,
            Token::If,
            Token::Lparen,
            Token::Int(String::from("5")),
            Token::Lt,
            Token::Int(String::from("10")),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::Rbrace,
            Token::Else,
            Token::Lbrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::Rbrace,
            Token::Int(String::from("10")),
            Token::Eq,
            Token::Int(String::from("10")),
            Token::Semicolon,
            Token::Int(String::from("10")),
            Token::Ne,
            Token::Int(String::from("9")),
            Token::Semicolon,
        ];

        for expected_token in expected_tokens {
            assert_eq!(lexer.next_token().unwrap(), expected_token);
        }

        assert_eq!(lexer.next_token(), None);
    }
}
