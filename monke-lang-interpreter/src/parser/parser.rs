use std::collections::HashMap;
use std::rc::Rc;

use super::super::result::InterpreterResult;
use super::ast::{
    ArrayLiteral, BlockStatement, Boolean, CallExpression, Expression, FunctionLiteral,
    HashLiteral, Identifier, IfExpression, IndexExpression, InfixExpression, IntegerLiteral,
    LetStatement, PrefixExpression, Program, ReturnStatement, Statement, StringLiteral,
};
use crate::lexer::{lexer::Lexer, token::Token};
use crate::parser::ast::{ExpressionStatement, ExpressionType};

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

type ParsePrefixFn = fn(&mut Parser) -> InterpreterResult<Expression>;
type ParseInfixFn = fn(&mut Parser, Expression) -> InterpreterResult<Expression>;

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
        let mut statements = vec![];

        while self.cur_token.is_some() {
            let statement = self.parse_statement()?;
            statements.push(Rc::new(statement));

            self.next_token();
        }

        Ok(Program::Statements(statements))
    }

    fn parse_statement(&mut self) -> InterpreterResult<Statement> {
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

    fn parse_let_statement(&mut self) -> InterpreterResult<Statement> {
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

        self.next_token();

        let value = Rc::new(self.parse_expression(ExpressionType::Lowest as usize)?);

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Semicolon)
        {
            self.next_token();
        }

        Ok(Statement::Let(LetStatement {
            token: Token::Let,
            name: Identifier {
                token: statement_name,
            },
            value,
        }))
    }

    fn parse_return_statement(&mut self) -> InterpreterResult<Statement> {
        let token = self.cur_token.clone().unwrap();

        self.next_token();

        let return_value = Rc::new(self.parse_expression(ExpressionType::Lowest as usize)?);

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Semicolon)
        {
            self.next_token();
        }

        Ok(Statement::Return(ReturnStatement {
            token,
            return_value,
        }))
    }

    fn parse_expression_statement(&mut self) -> InterpreterResult<Statement> {
        let cur_token = self.cur_token.clone().unwrap();
        let statement_expression = Rc::new(self.parse_expression(ExpressionType::Lowest as usize)?);

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Semicolon)
        {
            self.next_token();
        }

        Ok(Statement::Expression(ExpressionStatement {
            token: cur_token,
            expression: statement_expression,
        }))
    }

    fn parse_block_statement(&mut self) -> InterpreterResult<Statement> {
        let token = self.cur_token.clone().unwrap();
        let mut statements = vec![];

        self.next_token();

        while self.cur_token.as_ref().is_some_and(|t| t != &Token::Rbrace) {
            statements.push(Rc::new(self.parse_statement()?));
            self.next_token();
        }

        Ok(Statement::Block(BlockStatement { token, statements }))
    }

    fn parse_expression(&mut self, precedence: usize) -> InterpreterResult<Expression> {
        let prefix_fn = self.get_prefix_fn()?;
        let mut left = prefix_fn(self)?;

        while self
            .peek_token
            .as_ref()
            .is_some_and(|t| t != &Token::Semicolon)
            && precedence < get_precedence(&self.peek_token)
        {
            let infix_fn = self.get_infix_fn()?;
            self.next_token();
            left = infix_fn(self, left)?;
        }

        Ok(left)
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

    fn get_prefix_fn(&self) -> InterpreterResult<ParsePrefixFn> {
        match &self.cur_token {
            Some(t) => match t {
                Token::Ident(_) => Ok(Self::parse_identifier),
                Token::Int(_) => Ok(Self::parse_integer_literal),
                token if token == &Token::Minus || token == &Token::Bang => {
                    Ok(Self::parse_prefix_expression)
                }
                token if token == &Token::True || token == &Token::False => Ok(Self::parse_boolean),
                Token::Lparen => Ok(Self::parse_grouped_expression),
                Token::If => Ok(Self::parse_if_expression),
                Token::Function => Ok(Self::parse_function_literal),
                Token::String(_) => Ok(Self::parse_string),
                Token::Lbracket => Ok(Self::parse_array_literal),
                Token::Lbrace => Ok(Self::parse_hash_literal),
                _ => todo!(),
            },
            None => Err(String::from(
                "unable to parse expression, unknown prefix expression type",
            )),
        }
    }

    fn get_infix_fn(&self) -> InterpreterResult<ParseInfixFn> {
        match &self.peek_token {
            Some(t) => match t {
                Token::Plus => Ok(Self::parse_infix_expression),
                Token::Minus => Ok(Self::parse_infix_expression),
                Token::Asterisk => Ok(Self::parse_infix_expression),
                Token::Slash => Ok(Self::parse_infix_expression),
                Token::Lt => Ok(Self::parse_infix_expression),
                Token::Gt => Ok(Self::parse_infix_expression),
                Token::Eq => Ok(Self::parse_infix_expression),
                Token::Ne => Ok(Self::parse_infix_expression),
                Token::Lparen => Ok(Self::parse_call_expression),
                Token::Lbracket => Ok(Self::parse_index_expression),
                _ => todo!(),
            },
            None => Err(String::from(
                "unable to parse expression, unknown prefix expression type",
            )),
        }
    }

    fn parse_identifier(parser: &mut Parser) -> InterpreterResult<Expression> {
        Ok(Expression::Identifier(Identifier {
            token: parser.cur_token.clone().unwrap(),
        }))
    }

    fn parse_integer_literal(parser: &mut Parser) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();

        let value = if let Token::Int(ref number_str) = token {
            number_str
                .parse::<i64>()
                .map_err(|_| String::from("unable to parse integer literal, isize cast error"))?
        } else {
            return Err(String::from(
                "unable to parse integer literal, wrong token found",
            ));
        };

        Ok(Expression::IntegerLiteral(IntegerLiteral { token, value }))
    }

    fn parse_prefix_expression(parser: &mut Parser) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();
        parser.next_token();
        let right = Rc::new(parser.parse_expression(ExpressionType::Prefix as usize)?);

        Ok(Expression::Prefix(PrefixExpression { token, right }))
    }

    fn parse_infix_expression(
        parser: &mut Parser,
        left: Expression,
    ) -> InterpreterResult<Expression> {
        let cur_token = parser.cur_token.clone();
        let cur_precedence = get_precedence(&cur_token);

        parser.next_token();
        let right = Rc::new(parser.parse_expression(cur_precedence)?);

        Ok(Expression::Infix(InfixExpression {
            token: cur_token.unwrap(),
            left: Rc::new(left),
            right,
        }))
    }

    fn parse_boolean(parser: &mut Parser) -> InterpreterResult<Expression> {
        let cur_token = parser.cur_token.clone().unwrap();
        let is_true = cur_token == Token::True;

        Ok(Expression::Boolean(Boolean {
            value: is_true,
            token: cur_token,
        }))
    }

    fn parse_grouped_expression(parser: &mut Parser) -> InterpreterResult<Expression> {
        parser.next_token();
        let expr = parser.parse_expression(ExpressionType::Lowest as usize)?;

        if !parser.expect_peek(Token::Rparen) {
            return Err(String::from(
                "unable to parse grouped expression, couldn't find closing parentheses",
            ));
        }

        Ok(expr)
    }

    fn parse_if_expression(parser: &mut Parser) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();

        if !parser.expect_peek(Token::Lparen) {
            return Err(String::from(
                "unable to parse if expression, couldn't find opening parentheses",
            ));
        }

        parser.next_token();
        let condition = Rc::new(parser.parse_expression(ExpressionType::Lowest as usize)?);

        if !parser.expect_peek(Token::Rparen) {
            return Err(String::from(
                "unable to parse if expression, couldn't find closing parentheses",
            ));
        }

        if !parser.expect_peek(Token::Lbrace) {
            return Err(String::from(
                "unable to parse if expression, couldn't find opening brace for consequence statement",
            ));
        }

        let consequence = Rc::new(parser.parse_block_statement()?);

        let mut alternative = None;

        if parser
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Else)
        {
            parser.next_token();

            if !parser.expect_peek(Token::Lbrace) {
                return Err(String::from(
                    "unable to parse if expression, couldn't find opening brace for alternative statement",
                ));
            }

            alternative = Some(Rc::new(parser.parse_block_statement()?));
        }

        Ok(Expression::If(IfExpression {
            token,
            condition,
            consequence,
            alternative,
        }))
    }

    fn parse_function_literal(parser: &mut Parser) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();

        if !parser.expect_peek(Token::Lparen) {
            return Err(String::from(
                "unable to parse function literal, couldn't find opening paretheses",
            ));
        }

        let parameters = parser.parse_function_parameters()?;

        if !parser.expect_peek(Token::Lbrace) {
            return Err(String::from(
                "unable to parse function literal, couldn't find opening brace",
            ));
        }

        let body = Rc::new(parser.parse_block_statement()?);

        Ok(Expression::FunctionLiteral(FunctionLiteral {
            token,
            parameters,
            body,
        }))
    }

    fn parse_function_parameters(&mut self) -> InterpreterResult<Vec<Identifier>> {
        let mut identifiers = vec![];

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Rparen)
        {
            self.next_token();
            return Ok(identifiers);
        }

        self.next_token();

        if self.cur_token.is_none() {
            return Err(String::from(
                "unable to parse function parameters, couldn't find identifier",
            ));
        }

        identifiers.push(Identifier {
            token: self.cur_token.clone().unwrap(),
        });

        while self.peek_token.as_ref().is_some_and(|t| t == &Token::Comma) {
            self.next_token();
            self.next_token();

            if self.cur_token.is_none() {
                return Err(String::from(
                    "unable to parse function parameters, couldn't find identifier",
                ));
            }

            identifiers.push(Identifier {
                token: self.cur_token.clone().unwrap(),
            });
        }

        if !self.expect_peek(Token::Rparen) {
            return Err(String::from(
                "unable to parse function parameters, couldn't find closing parentheses",
            ));
        }

        Ok(identifiers)
    }

    fn parse_call_expression(
        parser: &mut Parser,
        function: Expression,
    ) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();
        let arguments = parser.parse_expression_list(Token::Rparen)?;

        Ok(Expression::Call(CallExpression {
            token,
            arguments,
            function: Rc::new(function),
        }))
    }

    fn parse_expression_list(&mut self, end: Token) -> InterpreterResult<Vec<Rc<Expression>>> {
        let mut arguments = vec![];

        if self.peek_token.as_ref().is_some_and(|t| t == &end) {
            self.next_token();
            return Ok(arguments);
        }

        self.next_token();
        arguments.push(Rc::new(
            self.parse_expression(ExpressionType::Lowest as usize)?,
        ));

        while self.peek_token.as_ref().is_some_and(|t| t == &Token::Comma) {
            self.next_token();
            self.next_token();

            arguments.push(Rc::new(
                self.parse_expression(ExpressionType::Lowest as usize)?,
            ));
        }

        if !self.expect_peek(end) {
            return Err(String::from(
                "unable to parse call arguments, couldn't find closing parentheses",
            ));
        }

        Ok(arguments)
    }

    fn parse_string(parser: &mut Parser) -> InterpreterResult<Expression> {
        Ok(Expression::StringLiteral(StringLiteral {
            token: parser.cur_token.clone().unwrap(),
        }))
    }

    fn parse_array_literal(parser: &mut Parser) -> InterpreterResult<Expression> {
        Ok(Expression::ArrayLiteral(ArrayLiteral {
            token: parser.cur_token.clone().unwrap(),
            elements: parser.parse_expression_list(Token::Rbracket)?,
        }))
    }

    fn parse_index_expression(
        parser: &mut Parser,
        left: Expression,
    ) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();

        parser.next_token();
        let index = Rc::new(parser.parse_expression(ExpressionType::Lowest as usize)?);

        if !parser.expect_peek(Token::Rbracket) {
            return Err(String::from(
                "unable to parse index expression, couldn't find closing bracket",
            ));
        }

        Ok(Expression::IndexExpression(IndexExpression {
            token,
            left: Rc::new(left),
            index,
        }))
    }

    fn parse_hash_literal(parser: &mut Parser) -> InterpreterResult<Expression> {
        let token = parser.cur_token.clone().unwrap();
        let mut pairs = HashMap::new();

        while parser
            .peek_token
            .as_ref()
            .is_some_and(|t| t != &Token::Rbrace)
        {
            parser.next_token();
            let key = Rc::new(parser.parse_expression(ExpressionType::Lowest as usize)?);

            if !parser.expect_peek(Token::Colon) {
                return Err(String::from(
                    "unable to parse hash literal, couldn't find colon",
                ));
            }

            parser.next_token();
            let value = Rc::new(parser.parse_expression(ExpressionType::Lowest as usize)?);

            pairs.insert(key, value);

            if (parser.peek_token.is_none()
                || parser
                    .peek_token
                    .as_ref()
                    .is_some_and(|t| t != &Token::Rbrace))
                && !parser.expect_peek(Token::Comma)
            {
                return Err(String::from(
                    "unable to parse hash literal, couldn't find closing brace or comma",
                ));
            }
        }

        if !parser.expect_peek(Token::Rbrace) {
            return Err(String::from(
                "unable to parse hash literal, couldn't find closing brace",
            ));
        }

        Ok(Expression::HashLiteral(HashLiteral { token, pairs }))
    }
}

fn get_precedence(token: &Option<Token>) -> usize {
    let expr_type = match token {
        Some(t) => match t {
            Token::Plus => ExpressionType::Sum,
            Token::Minus => ExpressionType::Sum,
            Token::Asterisk => ExpressionType::Product,
            Token::Slash => ExpressionType::Product,
            Token::Lt => ExpressionType::LessGreater,
            Token::Gt => ExpressionType::LessGreater,
            Token::Eq => ExpressionType::Equals,
            Token::Ne => ExpressionType::Equals,
            Token::Lparen => ExpressionType::Call,
            Token::Lbracket => ExpressionType::Index,
            _ => ExpressionType::Lowest,
        },
        None => ExpressionType::Lowest,
    };

    expr_type as usize
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::Parser;
    use crate::{
        lexer::{lexer::Lexer, token::Token},
        parser::ast::{
            Boolean, Expression, Identifier, InfixExpression, IntegerLiteral, LetStatement,
            Program, Statement,
        },
    };

    fn parse_input(input: &str) -> Program {
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        program.unwrap()
    }

    #[test]
    fn let_statements_test() {
        let expected: Vec<(&str, Token, Expression)> = vec![
            (
                "let x = 5;",
                Token::Ident(String::from("x")),
                Expression::IntegerLiteral(IntegerLiteral {
                    token: Token::Int(String::from("5")),
                    value: 5,
                }),
            ),
            (
                "let y = true;",
                Token::Ident(String::from("y")),
                Expression::Boolean(Boolean {
                    token: Token::True,
                    value: true,
                }),
            ),
            (
                "let foobar = y;",
                Token::Ident(String::from("foobar")),
                Expression::Identifier(Identifier {
                    token: Token::Ident(String::from("y")),
                }),
            ),
        ];

        for (input, let_ident, expression) in expected {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert!(statements.len() == 1);

            let let_statement = match statements.first().unwrap().as_ref() {
                crate::parser::ast::Statement::Let(let_statement) => let_statement,
                actual => panic!("let statement expected, but got {actual}"),
            };

            assert_eq!(let_statement.name.token, let_ident);

            match (&let_statement.value.as_ref(), expression) {
                (Expression::IntegerLiteral(int), Expression::IntegerLiteral(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Expression::Boolean(bool), Expression::Boolean(exp)) => {
                    assert_eq!(bool.value, exp.value)
                }
                (Expression::Identifier(ident), Expression::Identifier(exp)) => {
                    assert_eq!(ident.token, exp.token)
                }
                (actual, _) => panic!("integer literal expected, but got {actual}"),
            };
        }
    }

    #[test]
    fn return_statements_test() {
        let expected: Vec<(&str, Expression)> = vec![
            (
                "return 5;",
                Expression::IntegerLiteral(IntegerLiteral {
                    token: Token::Int(String::from("5")),
                    value: 5,
                }),
            ),
            (
                "return true;",
                Expression::Boolean(Boolean {
                    token: Token::True,
                    value: true,
                }),
            ),
            (
                "return y;",
                Expression::Identifier(Identifier {
                    token: Token::Ident(String::from("y")),
                }),
            ),
        ];

        for (input, expression) in expected {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert_eq!(statements.len(), 1);

            let return_statement = match statements.first().unwrap().as_ref() {
                crate::parser::ast::Statement::Return(return_statement) => return_statement,
                actual => panic!("return statement expected {actual}"),
            };

            match (&return_statement.return_value.as_ref(), expression) {
                (Expression::IntegerLiteral(int), Expression::IntegerLiteral(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Expression::Boolean(bool), Expression::Boolean(exp)) => {
                    assert_eq!(bool.value, exp.value)
                }
                (Expression::Identifier(ident), Expression::Identifier(exp)) => {
                    assert_eq!(ident.token, exp.token)
                }
                (actual, _) => panic!("integer literal expected, but got {actual}"),
            };
        }
    }

    #[test]
    fn pretty_print_test() {
        let program = Program::Statements(vec![Rc::new(Statement::Let(LetStatement {
            token: Token::Let,
            name: Identifier {
                token: Token::Ident(String::from("myVar")),
            },
            value: Rc::new(Expression::Identifier(Identifier {
                token: Token::Ident(String::from("anotherVar")),
            })),
        }))]);

        assert_eq!(program.to_string(), String::from("let myVar = anotherVar;"));
    }

    #[test]
    fn identifier_expression_test() {
        let input = "foobar;";
        let program = parse_input(input);

        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };

        assert_eq!(statements.len(), 1);

        let expression_statement = match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => expr,
            actual => panic!("expression statement expected, but got {actual}"),
        };

        let identifier = match &expression_statement.expression.as_ref() {
            Expression::Identifier(ident) => ident,
            actual => panic!("identifier expresssion expected, but got {actual}"),
        };

        assert_eq!(identifier.token, Token::Ident(String::from("foobar")));
    }

    #[test]
    fn integer_literal_expression_test() {
        let input = "5;";
        let program = parse_input(input);

        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };

        assert_eq!(statements.len(), 1);

        let expression_statement = match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => expr,
            actual => panic!("expression statement expected, but got {actual}"),
        };

        let integer_literal = match &expression_statement.expression.as_ref() {
            Expression::IntegerLiteral(int) => int,
            actual => panic!("integer literal expression expected, but got {actual}"),
        };

        assert_eq!(integer_literal.token, Token::Int(String::from("5")));
        assert_eq!(integer_literal.value, 5);
    }

    #[test]
    fn prefix_expression_test_num() {
        let expected_expressions = vec![
            (
                "!5;",
                Token::Bang,
                Expression::IntegerLiteral(IntegerLiteral {
                    token: Token::Int(String::from("5")),
                    value: 5,
                }),
            ),
            (
                "-15;",
                Token::Minus,
                Expression::IntegerLiteral(IntegerLiteral {
                    token: Token::Int(String::from("15")),
                    value: 15,
                }),
            ),
            (
                "!true;",
                Token::Bang,
                Expression::Boolean(Boolean {
                    token: Token::True,
                    value: true,
                }),
            ),
            (
                "!false;",
                Token::Bang,
                Expression::Boolean(Boolean {
                    token: Token::False,
                    value: false,
                }),
            ),
        ];

        for (input, expected_token, expected_expr) in expected_expressions {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert_eq!(statements.len(), 1);

            let expression_statement = match statements.first().unwrap().as_ref() {
                Statement::Expression(expr) => expr,
                actual => panic!("expression statement expected, but got {actual}"),
            };

            let prefix_expression = match &expression_statement.expression.as_ref() {
                Expression::Prefix(prefix) => prefix,
                actual => panic!("prefix expression expected, but got {actual}"),
            };

            assert_eq!(prefix_expression.token, expected_token);

            match (prefix_expression.right.clone().as_ref(), expected_expr) {
                (Expression::IntegerLiteral(int), Expression::IntegerLiteral(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Expression::Boolean(bool), Expression::Boolean(exp)) => {
                    assert_eq!(bool.value, exp.value)
                }
                (actual, exp) => {
                    panic!("integer literal or boolean expected, but got {actual} {exp}")
                }
            };
        }
    }

    #[test]
    fn infix_expression_test_num() {
        let expected_expressions = vec![
            (
                "5 + 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Plus,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 - 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Minus,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 * 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Asterisk,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 / 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Slash,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 > 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Gt,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 < 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Lt,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 == 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Eq,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "5 != 5;",
                Expression::Infix(InfixExpression {
                    token: Token::Ne,
                    left: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                    right: Rc::new(Expression::IntegerLiteral(IntegerLiteral {
                        token: Token::Int(String::from("5")),
                        value: 5,
                    })),
                }),
            ),
            (
                "true == true",
                Expression::Infix(InfixExpression {
                    token: Token::Eq,
                    left: Rc::new(Expression::Boolean(Boolean {
                        token: Token::True,
                        value: true,
                    })),
                    right: Rc::new(Expression::Boolean(Boolean {
                        token: Token::True,
                        value: true,
                    })),
                }),
            ),
            (
                "true != false",
                Expression::Infix(InfixExpression {
                    token: Token::Ne,
                    left: Rc::new(Expression::Boolean(Boolean {
                        token: Token::True,
                        value: true,
                    })),
                    right: Rc::new(Expression::Boolean(Boolean {
                        token: Token::False,
                        value: false,
                    })),
                }),
            ),
            (
                "false == false",
                Expression::Infix(InfixExpression {
                    token: Token::Eq,
                    left: Rc::new(Expression::Boolean(Boolean {
                        token: Token::False,
                        value: false,
                    })),
                    right: Rc::new(Expression::Boolean(Boolean {
                        token: Token::False,
                        value: false,
                    })),
                }),
            ),
        ];

        for (input, expected_expr) in expected_expressions {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert_eq!(statements.len(), 1);

            let expression_statement = match statements.first().unwrap().as_ref() {
                Statement::Expression(expr) => expr,
                actual => panic!("expression statement expected, but got {actual}"),
            };

            let (infix_expression, exp_infix) =
                match (expression_statement.expression.as_ref(), expected_expr) {
                    (Expression::Infix(infix), Expression::Infix(exp)) => (infix, exp),
                    (actual, exp) => panic!("infix expression expected, but got {actual} {exp}"),
                };

            assert_eq!(infix_expression.token, exp_infix.token);

            match (infix_expression.left.as_ref(), exp_infix.left.as_ref()) {
                (Expression::IntegerLiteral(int), Expression::IntegerLiteral(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Expression::Boolean(bool), Expression::Boolean(exp)) => {
                    assert_eq!(bool.value, exp.value)
                }
                (actual, exp) => {
                    panic!("integer literal expression expected, but got {actual} {exp}")
                }
            };
            match (infix_expression.right.as_ref(), exp_infix.right.as_ref()) {
                (Expression::IntegerLiteral(int), Expression::IntegerLiteral(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Expression::Boolean(bool), Expression::Boolean(exp)) => {
                    assert_eq!(bool.value, exp.value)
                }
                (actual, exp) => {
                    panic!("integer literal expression expected, but got {actual} {exp}")
                }
            };
        }
    }

    #[test]
    fn operator_precedence_test() {
        let expected_expressions = vec![
            ("-a * b", "((-a) * b)"),
            ("!-a", "(!(-a))"),
            ("a + b + c", "((a + b) + c)"),
            ("a + b - c", "((a + b) - c)"),
            ("a * b * c", "((a * b) * c)"),
            ("a * b / c", "((a * b) / c)"),
            ("a + b / c", "(a + (b / c))"),
            ("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
            ("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
            ("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
            ("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            (
                "3 + 4 * 5 == 3 * 1 + 4 * 5",
                "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))",
            ),
            ("true", "true"),
            ("false", "false"),
            ("3 > 5 == false", "((3 > 5) == false)"),
            ("3 < 5 == true", "((3 < 5) == true)"),
            ("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
            ("(5 + 5) * 2", "((5 + 5) * 2)"),
            ("2 / (5 + 5)", "(2 / (5 + 5))"),
            ("-(5 + 5)", "(-(5 + 5))"),
            ("!(true == true)", "(!(true == true))"),
            ("a + add(b * c) + d", "((a + add((b * c))) + d)"),
            (
                "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
                "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))",
            ),
            (
                "add(a + b + c * d / f + g)",
                "add((((a + b) + ((c * d) / f)) + g))",
            ),
            (
                "a * [1, 2, 3, 4][b * c] * d",
                "((a * ([1, 2, 3, 4][(b * c)])) * d)",
            ),
            (
                "add(a * b[2], b[1], 2 * [1, 2][1])",
                "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))",
            ),
        ];

        for (input, expected) in expected_expressions {
            let program = parse_input(input);
            assert_eq!(program.to_string(), expected);
        }
    }

    #[test]
    fn if_expression_test() {
        let expected = vec![
            ("if (x < y) { x }", false),
            ("if (x < y) { x } else { y }", true),
        ];

        for (input, has_alternative_statement) in expected {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert_eq!(statements.len(), 1);

            let expression_statement = match statements.first().unwrap().as_ref() {
                Statement::Expression(expr) => expr,
                actual => panic!("expression statement expected, but got {actual}"),
            };

            let if_expression = match expression_statement.expression.as_ref() {
                Expression::If(if_expr) => if_expr,
                actual => panic!("if expression expected, but got {actual}"),
            };

            let infix_expression = match if_expression.condition.as_ref() {
                Expression::Infix(infix) => infix,
                actual => panic!("infix expression expected, but got {actual}"),
            };

            assert_eq!(infix_expression.token, Token::Lt);

            match (
                infix_expression.left.as_ref(),
                infix_expression.right.as_ref(),
            ) {
                (Expression::Identifier(ident_left), Expression::Identifier(ident_right)) => {
                    assert_eq!(ident_left.token, Token::Ident(String::from("x")));
                    assert_eq!(ident_right.token, Token::Ident(String::from("y")));
                }
                (actual_left, actual_right) => {
                    panic!("identifiers expected, bug got {actual_left} {actual_right}")
                }
            }

            let block_statement = match if_expression.consequence.as_ref() {
                Statement::Block(block) => block,
                actual => panic!("block statement expected, bug got {actual}"),
            };

            assert_eq!(block_statement.statements.len(), 1);

            match block_statement.statements.first().unwrap().as_ref() {
                Statement::Expression(statement) => match &statement.expression.as_ref() {
                    Expression::Identifier(ident) => {
                        assert_eq!(ident.token, Token::Ident(String::from("x")))
                    }
                    actual => panic!("identifier expected, but got {actual}"),
                },
                actual => panic!("expression statement expected, bug got {actual}"),
            };

            if has_alternative_statement {
                let block_statement = match if_expression.alternative.as_ref().unwrap().as_ref() {
                    Statement::Block(block) => block,
                    actual => panic!("block statement expected, bug got {actual}"),
                };

                match block_statement.statements.first().unwrap().as_ref() {
                    Statement::Expression(statement) => match &statement.expression.as_ref() {
                        Expression::Identifier(ident) => {
                            assert_eq!(ident.token, Token::Ident(String::from("y")))
                        }
                        actual => panic!("identifier expected, but got {actual}"),
                    },
                    actual => panic!("expression statement expected, bug got {actual}"),
                };
            }
        }
    }

    #[test]
    fn function_literal_test() {
        let input = "fn(x, y) { x + y; }";

        let program = parse_input(input);

        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };

        assert_eq!(statements.len(), 1);

        let function_literal = match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::FunctionLiteral(func) => func,
                actual => panic!("function literal expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        };

        assert_eq!(function_literal.parameters.len(), 2);

        assert_eq!(
            function_literal.parameters.get(0).unwrap().token,
            Token::Ident(String::from("x"))
        );
        assert_eq!(
            function_literal.parameters.get(1).unwrap().token,
            Token::Ident(String::from("y"))
        );

        let block_statement = match function_literal.body.as_ref() {
            Statement::Block(block) => block,
            actual => panic!("block statement expected, but got {actual}"),
        };

        assert_eq!(block_statement.statements.len(), 1);

        let infix_expression = match block_statement.statements.first().unwrap().as_ref() {
            Statement::Expression(statement) => match &statement.expression.as_ref() {
                Expression::Infix(infix) => infix,
                actual => panic!("infix expression expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        };

        assert_eq!(infix_expression.token, Token::Plus);

        match (
            infix_expression.left.as_ref(),
            infix_expression.right.as_ref(),
        ) {
            (Expression::Identifier(left), Expression::Identifier(right)) => {
                assert_eq!(left.token, Token::Ident(String::from("x")));
                assert_eq!(right.token, Token::Ident(String::from("y")));
            }
            (actual_left, actual_right) => {
                panic!("expression statement expected, but got {actual_left} {actual_right}")
            }
        };
    }

    #[test]
    fn function_literal_test_corner_cases() {
        let expected = vec![
            ("fn() {};", vec![]),
            ("fn(x) {};", vec![Token::Ident(String::from("x"))]),
            (
                "fn(x, y, z) {};",
                vec![
                    Token::Ident(String::from("x")),
                    Token::Ident(String::from("y")),
                    Token::Ident(String::from("z")),
                ],
            ),
        ];

        for (input, params) in expected {
            let program = parse_input(input);

            let statements = match program {
                Program::Statements(statements) => statements,
                actual => panic!("statements expected, but got {actual}"),
            };

            assert_eq!(statements.len(), 1);

            let function_literal = match statements.first().unwrap().as_ref() {
                Statement::Expression(expr) => match &expr.expression.as_ref() {
                    Expression::FunctionLiteral(func) => func,
                    actual => panic!("function literal expected, but got {actual}"),
                },
                actual => panic!("expression statement expected, but got {actual}"),
            };

            assert_eq!(function_literal.parameters.len(), params.len());

            for (idx, param) in params.iter().enumerate() {
                assert_eq!(&function_literal.parameters.get(idx).unwrap().token, param);
            }
        }
    }

    #[test]
    fn call_expression_test() {
        let input = "add(1, 2 * 3, 4 + 5);";

        let program = parse_input(input);

        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        let call_expression = match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::Call(call) => call,
                actual => panic!("call expression expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        };
        assert_eq!(call_expression.arguments.len(), 3);

        let identifier = match call_expression.function.as_ref() {
            Expression::Identifier(ident) => ident,
            actual => panic!("identifier expected, but got {actual}"),
        };
        assert_eq!(identifier.token, Token::Ident(String::from("add")));

        match &call_expression
            .arguments
            .iter()
            .map(|arg| arg.as_ref())
            .collect::<Vec<_>>()[..]
        {
            [Expression::IntegerLiteral(int), Expression::Infix(first_infix), Expression::Infix(second_infix)] =>
            {
                assert_eq!(int.value, 1);
                assert_eq!(first_infix.token, Token::Asterisk);

                match (first_infix.left.as_ref(), first_infix.right.as_ref()) {
                    (Expression::IntegerLiteral(left), Expression::IntegerLiteral(right)) => {
                        assert_eq!(left.value, 2);
                        assert_eq!(right.value, 3);
                    }
                    (actual_left, actual_right) => {
                        panic!("integer literals expected, bug got {actual_left} {actual_right}")
                    }
                }

                assert_eq!(second_infix.token, Token::Plus);

                match (second_infix.left.as_ref(), second_infix.right.as_ref()) {
                    (Expression::IntegerLiteral(left), Expression::IntegerLiteral(right)) => {
                        assert_eq!(left.value, 4);
                        assert_eq!(right.value, 5);
                    }
                    (actual_left, actual_right) => {
                        panic!("integer literals expected, bug got {actual_left} {actual_right}")
                    }
                }
            }
            _ => panic!(
                "integer literal and two infix expressions expected, got {:?}",
                call_expression.arguments
            ),
        };
    }

    #[test]
    fn string_literal_test() {
        let input = "\"hello world!\"";

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::StringLiteral(string) => {
                    assert_eq!(string.token.to_string(), "hello world!")
                }
                actual => panic!("string literal expected, got {actual}"),
            },
            actual => panic!("expression statement expected, got {actual}"),
        }
    }

    #[test]
    fn array_literal_test() {
        let input = "[1, 2 * 2, 3 + 3]";

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::ArrayLiteral(array) => {
                    assert_eq!(array.elements.len(), 3);

                    match array.elements.get(0).unwrap().as_ref() {
                        Expression::IntegerLiteral(int) => assert_eq!(int.value, 1),
                        actual => panic!("integer literal expected, but got {actual}"),
                    }

                    match array.elements.get(1).unwrap().as_ref() {
                        Expression::Infix(infix) => {
                            assert_eq!(infix.token, Token::Asterisk);

                            match (infix.left.as_ref(), infix.right.as_ref()) {
                                (
                                    Expression::IntegerLiteral(int_left),
                                    Expression::IntegerLiteral(int_right),
                                ) => {
                                    assert_eq!(int_left.value, 2);
                                    assert_eq!(int_right.value, 2);
                                }
                                (actual_left, actual_right) => panic!("integer literals expected, but got {actual_left} and {actual_right}"),
                            }
                        }
                        actual => panic!("infix expression expected, got {actual}"),
                    }

                    match array.elements.get(2).unwrap().as_ref() {
                        Expression::Infix(infix) => {
                            assert_eq!(infix.token, Token::Plus);

                            match (infix.left.as_ref(), infix.right.as_ref()) {
                                (
                                    Expression::IntegerLiteral(int_left),
                                    Expression::IntegerLiteral(int_right),
                                ) => {
                                    assert_eq!(int_left.value, 3);
                                    assert_eq!(int_right.value, 3);
                                }
                                (actual_left, actual_right) => panic!("integer literals expected, but got {actual_left} and {actual_right}"),
                            }
                        }
                        actual => panic!("infix expression expected, got {actual}"),
                    }
                }
                actual => panic!("array literal expected, got {actual}"),
            },
            actual => panic!("expression statement expected, got {actual}"),
        }
    }

    #[test]
    fn index_expression_test() {
        let input = "myArray[1 + 1]";

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::IndexExpression(idx_expr) => match (idx_expr.left.as_ref(), idx_expr.index.as_ref()) {
                    (Expression::Identifier(ident), Expression::Infix(infix)) => {
                        assert_eq!(ident.token.to_string(), "myArray");
                        assert_eq!(infix.token, Token::Plus);

                        match (infix.left.as_ref(), infix.right.as_ref()) {
                            (Expression::IntegerLiteral(int_left), Expression::IntegerLiteral(int_right)) => {
                                assert_eq!(int_left.value, 1);
                                assert_eq!(int_right.value, 1);
                            }
                            (actual_left, actual_right) => panic!("integer literals expected, but got {actual_left} and {actual_right}"),
                        }
                    }
                    (actual_left, actual_index) => panic!("identifier and infix expressions expected, got {actual_left} and {actual_index}"),
                },
                actual => panic!("index expression expected, got {actual}"),
            },
            actual => panic!("expression statement expected, got {actual}"),
        }
    }

    #[test]
    fn hash_literal_test() {
        let input = r#"{"one": 1, "two": 2, "three": 3}"#;
        let expected = vec![("one", 1), ("three", 3), ("two", 2)];

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::HashLiteral(hash_literal) => {
                    assert_eq!(hash_literal.pairs.len(), 3);

                    let mut actual_result = hash_literal.pairs.iter().map(|(key, value)| {
                        match (key.as_ref(), value.as_ref()) {
                            (
                                Expression::StringLiteral(string),
                                Expression::IntegerLiteral(int),
                            ) => {
                                (string.to_string(), int.value)
                            }
                            (actual_key, actaul_value) => panic!("string and integer expected, but got {actual_key} and {actaul_value}"),
                        }
                    }).collect::<Vec<_>>();

                    actual_result.sort_by(|(a, _), (b, _)| a.cmp(b));

                    for (&(exp_key, exp_value), (key, value)) in expected.iter().zip(actual_result)
                    {
                        assert_eq!(key.as_str(), exp_key);
                        assert_eq!(value, exp_value);
                    }
                }
                actual => panic!("hash literal expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        }
    }

    #[test]
    fn empty_hash_literal_test() {
        let input = "{}";

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::HashLiteral(hash_literal) => {
                    assert_eq!(hash_literal.pairs.len(), 0);
                }
                actual => panic!("hash literal expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        }
    }

    #[test]
    fn complex_hash_literal_test() {
        let input = r#"{"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}"#;
        let expected = vec![
            ("one", "(0 + 1)"),
            ("three", "(15 / 5)"),
            ("two", "(10 - 8)"),
        ];

        let program = parse_input(input);
        let statements = match program {
            Program::Statements(statements) => statements,
            actual => panic!("statements expected, but got {actual}"),
        };
        assert_eq!(statements.len(), 1);

        match statements.first().unwrap().as_ref() {
            Statement::Expression(expr) => match &expr.expression.as_ref() {
                Expression::HashLiteral(hash_literal) => {
                    assert_eq!(hash_literal.pairs.len(), 3);

                    let mut actual_result = hash_literal.pairs.iter().map(|(key, value)| {
                        match (key.as_ref(), value.as_ref()) {
                            (
                                Expression::StringLiteral(string1),
                                Expression::Infix(infix),
                            ) => {
                                (string1.to_string(), infix.to_string())
                            }
                            (actual_key, actaul_value) => panic!("string and integer expected, but got {actual_key} and {actaul_value}"),
                        }
                    }).collect::<Vec<_>>();

                    actual_result.sort_by(|(a, _), (b, _)| a.cmp(b));

                    for (&(exp_key, exp_value), (key, value)) in expected.iter().zip(actual_result)
                    {
                        assert_eq!(key.as_str(), exp_key);
                        assert_eq!(value, exp_value);
                    }
                }
                actual => panic!("hash literal expected, but got {actual}"),
            },
            actual => panic!("expression statement expected, but got {actual}"),
        }
    }
}
