use super::super::error::InterpreterResult;
use super::ast::{
    BlockStatement, Boolean, CallExpression, Expression, FunctionLiteral, Identifier, IfExpression,
    InfixExpression, IntegerLiteral, LetStatement, PrefixExpression, Program, ReturnStatement,
    Statement,
};
use crate::lexer::{lexer::Lexer, token::Token};
use crate::parser::ast::{ExpressionStatement, ExpressionType};

#[derive(Debug)]
pub struct Parser {
    lexer: Lexer,
    cur_token: Option<Token>,
    peek_token: Option<Token>,
}

type ParsePrefixFn = fn(&mut Parser) -> InterpreterResult<Box<dyn Expression>>;
type ParseInfixFn = fn(&mut Parser, Box<dyn Expression>) -> InterpreterResult<Box<dyn Expression>>;

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

    fn parse_block_statement(&mut self) -> InterpreterResult<BlockStatement> {
        let token = self.cur_token.clone().unwrap();
        let mut statements = vec![];

        self.next_token();

        while self.cur_token.as_ref().is_some_and(|t| t != &Token::Rbrace) {
            statements.push(self.parse_statement()?);
            self.next_token();
        }

        Ok(BlockStatement { token, statements })
    }

    fn parse_expression(&mut self, precedence: usize) -> InterpreterResult<Box<dyn Expression>> {
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
                _ => todo!(),
            },
            None => Err(String::from(
                "unable to parse expression, unknown prefix expression type",
            )),
        }
    }

    fn parse_identifier(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
        Ok(Box::new(Identifier {
            token: parser.cur_token.clone().unwrap(),
        }))
    }

    fn parse_integer_literal(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
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

        Ok(Box::new(IntegerLiteral { token, value }))
    }

    fn parse_prefix_expression(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
        let token = parser.cur_token.clone().unwrap();
        parser.next_token();
        let expression = parser.parse_expression(ExpressionType::Prefix as usize)?;

        Ok(Box::new(PrefixExpression {
            token,
            right: expression,
        }))
    }

    fn parse_infix_expression(
        parser: &mut Parser,
        left: Box<dyn Expression>,
    ) -> InterpreterResult<Box<dyn Expression>> {
        let cur_token = parser.cur_token.clone();
        let cur_precedence = get_precedence(&cur_token);

        parser.next_token();
        let right = parser.parse_expression(cur_precedence)?;

        Ok(Box::new(InfixExpression {
            token: cur_token.unwrap(),
            left,
            right,
        }))
    }

    fn parse_boolean(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
        let cur_token = parser.cur_token.clone().unwrap();
        let is_true = cur_token == Token::True;

        Ok(Box::new(Boolean {
            value: is_true,
            token: cur_token,
        }))
    }

    fn parse_grouped_expression(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
        parser.next_token();
        let expr = parser.parse_expression(ExpressionType::Lowest as usize)?;

        if !parser.expect_peek(Token::Rparen) {
            return Err(String::from(
                "unable to parse grouped expression, couldn't find closing parentheses",
            ));
        }

        Ok(expr)
    }

    fn parse_if_expression(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
        let token = parser.cur_token.clone().unwrap();

        if !parser.expect_peek(Token::Lparen) {
            return Err(String::from(
                "unable to parse if expression, couldn't find opening parentheses",
            ));
        }

        parser.next_token();
        let condition = parser.parse_expression(ExpressionType::Lowest as usize)?;

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

        let consequence = parser.parse_block_statement()?;

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

            alternative = Some(parser.parse_block_statement()?);
        }

        Ok(Box::new(IfExpression {
            token,
            condition,
            consequence,
            alternative,
        }))
    }

    fn parse_function_literal(parser: &mut Parser) -> InterpreterResult<Box<dyn Expression>> {
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

        let body = parser.parse_block_statement()?;

        Ok(Box::new(FunctionLiteral {
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
        function: Box<dyn Expression>,
    ) -> InterpreterResult<Box<dyn Expression>> {
        let token = parser.cur_token.clone().unwrap();
        let arguments = parser.parse_call_arguments()?;

        Ok(Box::new(CallExpression {
            token,
            arguments,
            function,
        }))
    }

    fn parse_call_arguments(&mut self) -> InterpreterResult<Vec<Box<dyn Expression>>> {
        let mut arguments = vec![];

        if self
            .peek_token
            .as_ref()
            .is_some_and(|t| t == &Token::Rparen)
        {
            self.next_token();
            return Ok(arguments);
        }

        self.next_token();
        arguments.push(self.parse_expression(ExpressionType::Lowest as usize)?);

        while self.peek_token.as_ref().is_some_and(|t| t == &Token::Comma) {
            self.next_token();
            self.next_token();

            arguments.push(self.parse_expression(ExpressionType::Lowest as usize)?);
        }

        if !self.expect_peek(Token::Rparen) {
            return Err(String::from(
                "unable to parse call arguments, couldn't find closing parentheses",
            ));
        }

        Ok(arguments)
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
            _ => ExpressionType::Lowest,
        },
        None => ExpressionType::Lowest,
    };

    expr_type as usize
}

#[cfg(test)]
mod tests {
    use super::Parser;
    use crate::{
        lexer::{lexer::Lexer, token::Token},
        parser::ast::{
            Boolean, CallExpression, ExpressionStatement, FunctionLiteral, Identifier,
            IfExpression, InfixExpression, IntegerLiteral, LetStatement, Node, PrefixExpression,
            Program, ReturnStatement,
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

            assert_eq!(let_statement.token, Token::Let);
            assert_eq!(&let_statement.name.token, expected_token);
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

    #[test]
    fn integer_literal_expression_test() {
        let input = "5;";
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

        let integer_literal = expression_statement
            .expression
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal expression");

        assert_eq!(integer_literal.token, Token::Int(String::from("5")));
        assert_eq!(integer_literal.value, 5);
    }

    #[test]
    fn prefix_expression_test_num() {
        let expected_expressions = vec![("!5;", Token::Bang, 5), ("-15;", Token::Minus, 15)];

        for (input, expected_token, expected_number) in expected_expressions {
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

            let prefix_expression = expression_statement
                .expression
                .as_any()
                .downcast_ref::<PrefixExpression>()
                .expect("expected prefix expression");

            assert_eq!(prefix_expression.token, expected_token);

            let integer_literal = prefix_expression
                .right
                .as_any()
                .downcast_ref::<IntegerLiteral>()
                .expect("expected integer literal expression");

            assert_eq!(integer_literal.value, expected_number);
        }
    }

    #[test]
    fn prefix_expression_test_boolean() {
        let expected_expressions = vec![
            ("!true;", Token::Bang, true),
            ("!false;", Token::Bang, false),
        ];

        for (input, expected_token, expected_number) in expected_expressions {
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

            let prefix_expression = expression_statement
                .expression
                .as_any()
                .downcast_ref::<PrefixExpression>()
                .expect("expected prefix expression");

            assert_eq!(prefix_expression.token, expected_token);

            let integer_literal = prefix_expression
                .right
                .as_any()
                .downcast_ref::<Boolean>()
                .expect("expected integer literal expression");

            assert_eq!(integer_literal.value, expected_number);
        }
    }

    #[test]
    fn infix_expression_test_num() {
        let expected_expressions = vec![
            ("5 + 5;", 5, Token::Plus, 5),
            ("5 - 5;", 5, Token::Minus, 5),
            ("5 * 5;", 5, Token::Asterisk, 5),
            ("5 / 5;", 5, Token::Slash, 5),
            ("5 > 5;", 5, Token::Gt, 5),
            ("5 < 5;", 5, Token::Lt, 5),
            ("5 == 5;", 5, Token::Eq, 5),
            ("5 != 5;", 5, Token::Ne, 5),
        ];

        for (input, left, expected_token, right) in expected_expressions {
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

            let infix_expression = expression_statement
                .expression
                .as_any()
                .downcast_ref::<InfixExpression>()
                .expect("expected infix expression");

            assert_eq!(infix_expression.token, expected_token);

            let left_integer_literal = infix_expression
                .left
                .as_any()
                .downcast_ref::<IntegerLiteral>()
                .expect("expected integer literal expression");
            let right_integer_literal = infix_expression
                .right
                .as_any()
                .downcast_ref::<IntegerLiteral>()
                .expect("expected integer literal expression");

            assert_eq!(left_integer_literal.value, left);
            assert_eq!(right_integer_literal.value, right);
        }
    }

    #[test]
    fn infix_expression_test_boolean() {
        let expected_expressions = vec![
            ("true == true", true, Token::Eq, true),
            ("true != false", true, Token::Ne, false),
            ("false == false", false, Token::Eq, false),
        ];

        for (input, left, expected_token, right) in expected_expressions {
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

            let infix_expression = expression_statement
                .expression
                .as_any()
                .downcast_ref::<InfixExpression>()
                .expect("expected infix expression");

            assert_eq!(infix_expression.token, expected_token);

            let left_integer_literal = infix_expression
                .left
                .as_any()
                .downcast_ref::<Boolean>()
                .expect("expected integer literal expression");
            let right_integer_literal = infix_expression
                .right
                .as_any()
                .downcast_ref::<Boolean>()
                .expect("expected integer literal expression");

            assert_eq!(left_integer_literal.value, left);
            assert_eq!(right_integer_literal.value, right);
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
        ];

        for (input, expected) in expected_expressions {
            let lexer = Lexer::new(String::from(input));
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                println!("{err}");
            }

            assert!(program.is_ok());
            let program = program.unwrap();

            assert_eq!(program.pretty_print(), expected);
        }
    }

    #[test]
    fn if_expression_test() {
        let expected = vec![
            ("if (x < y) { x }", false),
            ("if (x < y) { x } else { y }", true),
        ];

        for (input, has_alternative_statement) in expected {
            let lexer = Lexer::new(String::from(input));
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                println!("{err}");
            }

            assert!(program.is_ok());
            let program = program.unwrap();

            let expression_statement = program
                .statements
                .first()
                .unwrap()
                .as_any()
                .downcast_ref::<ExpressionStatement>()
                .expect("expected expression statement");

            let if_expression = expression_statement
                .expression
                .as_any()
                .downcast_ref::<IfExpression>()
                .expect("expected if expression");

            let infix_expression = if_expression
                .condition
                .as_any()
                .downcast_ref::<InfixExpression>()
                .expect("expected infix expression");

            assert_eq!(infix_expression.token, Token::Lt);

            let left = infix_expression
                .left
                .as_any()
                .downcast_ref::<Identifier>()
                .expect("expected identifier");
            let right = infix_expression
                .right
                .as_any()
                .downcast_ref::<Identifier>()
                .expect("expected identifier");

            assert_eq!(left.token, Token::Ident(String::from("x")));
            assert_eq!(right.token, Token::Ident(String::from("y")));

            assert_eq!(if_expression.consequence.statements.len(), 1);

            let consequence = if_expression
                .consequence
                .statements
                .first()
                .unwrap()
                .as_any()
                .downcast_ref::<ExpressionStatement>()
                .expect("expected expression statement");

            let consequence = consequence
                .expression
                .as_any()
                .downcast_ref::<Identifier>()
                .expect("expected identifier");

            assert_eq!(consequence.token, Token::Ident(String::from("x")));

            if has_alternative_statement {
                let alternative = if_expression
                    .alternative
                    .as_ref()
                    .unwrap()
                    .statements
                    .first()
                    .unwrap()
                    .as_any()
                    .downcast_ref::<ExpressionStatement>()
                    .expect("expected expression statement");

                let alternative = alternative
                    .expression
                    .as_any()
                    .downcast_ref::<Identifier>()
                    .expect("expected identifier");

                assert_eq!(alternative.token, Token::Ident(String::from("y")));
            }
        }
    }

    #[test]
    fn function_literal_test() {
        let input = "fn(x, y) { x + y; }";

        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        assert_eq!(program.statements.len(), 1);

        let expression_statement = program
            .statements
            .first()
            .unwrap()
            .as_any()
            .downcast_ref::<ExpressionStatement>()
            .expect("expected expression statement");

        let function_literal = expression_statement
            .expression
            .as_any()
            .downcast_ref::<FunctionLiteral>()
            .expect("expected function literal");

        assert_eq!(function_literal.parameters.len(), 2);

        assert_eq!(
            function_literal.parameters.get(0).unwrap().token,
            Token::Ident(String::from("x"))
        );
        assert_eq!(
            function_literal.parameters.get(1).unwrap().token,
            Token::Ident(String::from("y"))
        );

        assert_eq!(function_literal.body.statements.len(), 1);

        let expression_statement = function_literal
            .body
            .statements
            .first()
            .unwrap()
            .as_any()
            .downcast_ref::<ExpressionStatement>()
            .expect("expected expression statement");

        let infix_expression = expression_statement
            .expression
            .as_any()
            .downcast_ref::<InfixExpression>()
            .expect("expected infix expression");

        assert_eq!(infix_expression.token, Token::Plus);

        let left = infix_expression
            .left
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("expected identifier");
        let right = infix_expression
            .right
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("expected identifier");

        assert_eq!(left.token, Token::Ident(String::from("x")));
        assert_eq!(right.token, Token::Ident(String::from("y")));
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
            let lexer = Lexer::new(String::from(input));
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                println!("{err}");
            }

            assert!(program.is_ok());
            let program = program.unwrap();

            assert_eq!(program.statements.len(), 1);

            let expression_statement = program
                .statements
                .first()
                .unwrap()
                .as_any()
                .downcast_ref::<ExpressionStatement>()
                .expect("expected expression statement");

            let function_literal = expression_statement
                .expression
                .as_any()
                .downcast_ref::<FunctionLiteral>()
                .expect("expected function literal");

            assert_eq!(function_literal.parameters.len(), params.len());

            for (idx, param) in params.iter().enumerate() {
                assert_eq!(&function_literal.parameters.get(idx).unwrap().token, param);
            }
        }
    }

    #[test]
    fn call_expression_test() {
        let input = "add(1, 2 * 3, 4 + 5);";

        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        assert_eq!(program.statements.len(), 1);

        let expression_statement = program
            .statements
            .first()
            .unwrap()
            .as_any()
            .downcast_ref::<ExpressionStatement>()
            .expect("expected expression statement");

        let call_expression = expression_statement
            .expression
            .as_any()
            .downcast_ref::<CallExpression>()
            .expect("expected call expression");

        let identifier = call_expression
            .function
            .as_any()
            .downcast_ref::<Identifier>()
            .expect("expected identifier");

        assert_eq!(identifier.token, Token::Ident(String::from("add")));
        assert_eq!(call_expression.arguments.len(), 3);

        let int_literal = call_expression
            .arguments
            .get(0)
            .unwrap()
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal");

        assert_eq!(int_literal.value, 1);

        let first_infix_arg = call_expression
            .arguments
            .get(1)
            .unwrap()
            .as_any()
            .downcast_ref::<InfixExpression>()
            .expect("expected infix expression");

        let left = first_infix_arg
            .left
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal");

        let right = first_infix_arg
            .right
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal");

        assert_eq!(left.value, 2);
        assert_eq!(right.value, 3);
        assert_eq!(first_infix_arg.token, Token::Asterisk);

        let second_infix_arg = call_expression
            .arguments
            .get(2)
            .unwrap()
            .as_any()
            .downcast_ref::<InfixExpression>()
            .expect("expected infix expression");

        let left = second_infix_arg
            .left
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal");

        let right = second_infix_arg
            .right
            .as_any()
            .downcast_ref::<IntegerLiteral>()
            .expect("expected integer literal");

        assert_eq!(left.value, 4);
        assert_eq!(right.value, 5);
        assert_eq!(second_infix_arg.token, Token::Plus);
    }
}
