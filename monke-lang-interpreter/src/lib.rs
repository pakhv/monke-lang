use lexer::token::Token;

mod lexer;

#[derive(Debug, Default)]
pub struct Lexer {
    pub input: String,
    pub position: usize, // current position in input (points to current char)
    pub read_position: usize, // current reading position in input (after current char)
    pub ch: Option<u8>,  // current char under examination
}

impl Lexer {
    pub fn new(input: String) -> Self {
        let mut lexer = Lexer {
            input,
            position: 0,
            ..Default::default()
        };
        lexer.read_char();

        lexer
    }

    pub fn read_char(&mut self) {
        let cur_char = self.input.as_bytes().get(self.read_position);

        self.ch = if let Some(ch) = cur_char {
            self.read_position += 1;
            Some(*ch)
        } else {
            None
        }
    }

    pub fn next_token(&mut self) -> Option<Token> {
        let token = match self.ch {
            None => None,
            Some(ch) => match ch {
                b'=' => Some(Token::Assign),
                b';' => Some(Token::Semicolon),
                b'(' => Some(Token::Lparen),
                b')' => Some(Token::Rparen),
                b'{' => Some(Token::Lbrace),
                b'}' => Some(Token::Rbrace),
                b',' => Some(Token::Comma),
                b'+' => Some(Token::Plus),
                0 => Some(Token::Eof),
                _ => todo!(),
            },
        };

        self.read_char();
        token
    }
}

#[cfg(test)]
mod tests {
    use crate::{lexer::token::Token, Lexer};

    #[test]
    fn it_works() {
        let input = "=+(){},;";
        let lexer = Lexer::new(String::from(input));

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
    }
}
