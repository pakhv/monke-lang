use super::super::error::InterpreterResult;
use super::ast::{Expression, Identifier, LetStatement, Program, ReturnStatement, Statement};
use crate::lexer::{lexer::Lexer, token::Token};
use crate::parser::ast::{ExpressionStatement, ExpressionType};

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

type ParsePrefixFn = fn(&Parser) -> Box<dyn Expression>;
type ParseInfixFn = fn(&Parser, Box<dyn Expression>) -> Box<dyn Expression>;

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

    pub fn parse_program(&mut self) -> InterpreterResult<Program> {
        let mut program = Program { statements: vec![] };

        while self.cur_token.is_some() {
            let statement = self.parse_statement()?;
            program.statements.push(statement);

            self.next_token();
        }

        Ok(program)
    }

    fn parse_statement(&mut self) -> InterpreterResult<Box<dyn Statement>> {
        match &self.cur_token {
            Some(token) => match token {
                Token::Let => Ok(self.parse_let_statement()?),
                Token::Return => Ok(self.parse_return_statement()?),
                _ => Ok(self.parse_expression_statement()?),
            },
            None => Err(String::from(
                "unable to parse statement, there is no tokens",
            )),
        }
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }

    fn parse_let_statement(&mut self) -> InterpreterResult<Box<dyn Statement>> {
        if !self.expect_peek(Token::Ident(String::new())) {
            return Err(String::from(
                "unable to parse let statement, identifier expected",
            ));
        }

        let statement_name = self.cur_token.clone().unwrap();

        if !self.expect_peek(Token::Assign) {
            return Err(String::from(
                "unable to parse let statement, assign token expected",
            ));
        }

        loop {
            self.next_token();

            match &self.cur_token {
                Some(Token::Semicolon) => break,
                Some(_) => (),
                None => {
                    return Err(String::from(
                        "unable to parse let statement, couldn't find end of statement",
                    ))
                }
            }
        }

        Ok(Box::new(LetStatement {
            token: Token::Let,
            name: Identifier {
                token: statement_name,
            },
            value: Box::new(Identifier {
                token: Token::Illegal,
            }),
        }))
    }

    fn parse_return_statement(&mut self) -> InterpreterResult<Box<dyn Statement>> {
        loop {
            self.next_token();

            match &self.cur_token {
                Some(Token::Semicolon) => break,
                Some(_) => (),
                None => {
                    return Err(String::from(
                        "unable to parse let statement, couldn't find end of statement",
                    ))
                }
            }
        }

        Ok(Box::new(ReturnStatement {
            token: Token::Return,
            return_value: Box::new(Identifier {
                token: Token::Illegal,
            }),
        }))
    }

    fn parse_expression_statement(&mut self) -> InterpreterResult<Box<dyn Statement>> {
        let cur_token = self.cur_token.clone().unwrap();
        let statement_expression = self.parse_expression(ExpressionType::Lowest as usize)?;

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Semicolon)
        {
            self.next_token();
        }

        Ok(Box::new(ExpressionStatement {
            token: cur_token,
            expression: statement_expression,
        }))
    }

    fn parse_expression(&self, expression_type: usize) -> InterpreterResult<Box<dyn Expression>> {
        let prefix = self.get_prefix_fn();

        Ok(prefix(&self))
    }

    fn expect_peek(&mut self, token: Token) -> bool {
        match &self.peek_token {
            Some(t) if t == &token => {
                self.next_token();
                true
            }
            Some(Token::Ident(_)) | Some(Token::Int(_)) => match token {
                Token::Ident(_) | Token::Int(_) => {
                    self.next_token();
                    true
                }
                _ => false,
            },
            None | Some(_) => false,
        }
    }

    fn get_prefix_fn(&self) -> ParsePrefixFn {
        match &self.cur_token {
            Some(t) => match t {
                Token::Ident(_) => Self::parse_identifier,
                _ => todo!(),
            },
            None => todo!(),
        }
    }

    fn parse_identifier(parser: &Parser) -> Box<dyn Expression> {
        Box::new(Identifier {
            token: parser.cur_token.clone().unwrap(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::Parser;
    use crate::{
        lexer::{lexer::Lexer, token::Token},
        parser::ast::{
            ExpressionStatement, Identifier, LetStatement, Node, Program, ReturnStatement,
        },
    };

    #[test]
    fn let_statements_test() {
        let input = r#"let x = 5;
let y = 10;
let foobar = 838383;"#;
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        assert!(program.statements.len() == 3);

        let expected_identifiers = vec![
            Token::Ident(String::from("x")),
            Token::Ident(String::from("y")),
            Token::Ident(String::from("foobar")),
        ];

        for (expected_token, statement) in expected_identifiers.iter().zip(program.statements) {
            let let_statement = statement
                .as_any()
                .downcast_ref::<LetStatement>()
                .expect("expected let statement");

            assert!(let_statement_valid(let_statement, expected_token));
        }
    }

    #[test]
    fn return_statements_test() {
        let input = r#"
return 5;
return 10;
return 993322;
"#;
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        assert!(program.statements.len() == 3);

        for statement in program.statements {
            let return_statement = statement
                .as_any()
                .downcast_ref::<ReturnStatement>()
                .expect("expected let statement");

            assert_eq!(return_statement.token, Token::Return);
        }
    }

    #[test]
    fn pretty_print_test() {
        let program = Program {
            statements: vec![Box::new(LetStatement {
                token: Token::Let,
                name: Identifier {
                    token: Token::Ident(String::from("myVar")),
                },
                value: Box::new(Identifier {
                    token: Token::Ident(String::from("anotherVar")),
                }),
            })],
        };

        assert_eq!(
            program.pretty_print(),
            String::from("let myVar = anotherVar;")
        );
    }

    #[test]
    fn identifier_expression_test() {
        let input = "foobar;";
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        assert!(program.statements.len() == 1);
        let expression_statement = program
            .statements
            .first()
            .unwrap()
            .as_any()
            .downcast_ref::<ExpressionStatement>()
            .expect("expected expression statement");

        let identifier = expression_statement
            .expression
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("expected identifier expresssion");

        assert_eq!(identifier.token, Token::Ident(String::from("foobar")));
    }

    fn let_statement_valid(statement: &LetStatement, expected_token: &Token) -> bool {
        if Token::Let != statement.token {
            return false;
        }

        if &statement.name.token != expected_token {
            return false;
        }

        true
    }
}
