use crate::lexer::{lexer::Lexer, token::Token};

use super::ast::{Program, Statement};

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

impl Parser {
    pub fn new(mut lexer: Lexer) -> Self {
        let cur_token = lexer.next_token();
        let peek_token = lexer.next_token();

        Parser {
            lexer,
            cur_token,
            peek_token,
        }
    }

    pub fn parse_program(&mut self) -> Program {
        let program = Program { statements: vec![] };

        while self.cur_token.is_some() {
            self.parse_statement();

            self.next_token();
        }

        program
    }

    fn parse_statement(&self) -> Box<dyn Statement> {
        match &self.cur_token {
            Some(token) => match token {
                Token::Let => todo!(),
                _ => todo!(),
            },
            None => todo!(),
        }
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }
}

#[cfg(test)]
mod tests {
    use super::Parser;
    use crate::{
        lexer::{lexer::Lexer, token::Token},
        parser::ast::LetStatement,
    };

    #[test]
    fn test_let_statements() {
        let input = r#"let x = 5;
let y = 10;
let foobar = 838383;"#;
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        assert!(program.statements.len() == 3);

        let expected_identifiers = vec![
            Token::Ident(String::from("x")),
            Token::Ident(String::from("foobar")),
            Token::Ident(String::from("y")),
        ];

        for (expected_token, statement) in expected_identifiers.iter().zip(program.statements) {
            let let_statement = statement
                .as_any()
                .downcast_ref::<LetStatement>()
                .expect("expected let statement");

            assert!(let_statement_valid(let_statement, expected_token));
        }
    }

    fn let_statement_valid(statement: &LetStatement, expected_token: &Token) -> bool {
        if Token::Let != statement.token {
            return false;
        }

        if &statement.name != expected_token {
            return false;
        }

        true
    }
}
