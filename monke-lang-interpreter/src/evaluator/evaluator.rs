use crate::{
    lexer::token::Token,
    parser::ast::{Expression, Program, Statement},
    result::InterpreterResult,
};

use super::{
    environment::Environment,
    types::{Boolean, Integer, Null, Object, Return},
};

pub fn eval(program: Program, env: &mut Environment) -> InterpreterResult<Object> {
    match program {
        Program::Statement(statement) => match statement {
            Statement::Expression(expr) => eval(expr.expression.into(), env),
            Statement::Block(block) => eval_block_statement(block, env),
            Statement::Return(return_statement) => Ok(Object::Return(Return {
                value: Box::new(eval(return_statement.return_value.into(), env)?),
            })),
            Statement::Let(let_statement) => {
                let value = eval(let_statement.value.into(), env)?;

                let value_key = match let_statement.name.token {
                    Token::Ident(key) => key,
                    _ => return Err(String::from("somehow Palpatine returned")),
                };

                Ok(env.set(value_key, value))
            }
        },
        Program::Statements(statements) => eval_program(statements, env),
        Program::Expression(expr) => match expr {
            Expression::IntegerLiteral(int) => Ok(Object::Integer(Integer { value: int.value })),
            Expression::Boolean(bool) => Ok(Object::Boolean(Boolean { value: bool.value })),
            Expression::Prefix(prefix) => {
                let right = eval((*prefix.right).into(), env)?;
                eval_prefix_expression(prefix.token, right)
            }
            Expression::Infix(infix) => {
                let left = eval((*infix.left).into(), env)?;
                let right = eval((*infix.right).into(), env)?;

                eval_infix_expression(infix.token, left, right)
            }
            Expression::If(if_expr) => eval_if_expression(if_expr, env),
            Expression::Identifier(ident) => {
                let value_key = match ident.token {
                    Token::Ident(key) => key,
                    _ => return Err(String::from("somehow Palpatine returned")),
                };

                match env.get(&value_key) {
                    Some(obj) => Ok(obj),
                    None => {
                        return Err(format!(
                            "unable to evaluate identifier, identifier \"{value_key}\" not found"
                        ))
                    }
                }
            }
            _ => todo!(),
        },
        Program::Expressions(_) => todo!(),
    }
}

fn eval_block_statement(
    block: crate::parser::ast::BlockStatement,
    env: &mut Environment,
) -> InterpreterResult<Object> {
    let mut result = Object::Null(Null {});

    for statement in block.statements {
        result = eval(statement.into(), env)?;

        if let Object::Return(_) = result {
            return Ok(result);
        }
    }

    Ok(result)
}

fn eval_prefix_expression(token: Token, right: Object) -> InterpreterResult<Object> {
    match token {
        Token::Bang => match right {
            Object::Boolean(bool) => Ok(Object::Boolean(Boolean { value: !bool.value })),
            Object::Null(_) => Ok(Object::Boolean(Boolean { value: true })),
            _ => Ok(Object::Boolean(Boolean { value: false })),
        },
        Token::Minus => match right {
            Object::Integer(int) => Ok(Object::Integer(Integer { value: -int.value })),
            expr => Err(format!(
                "unable to evaluate prefix expression, Integer number must follow Minus token, but got \"{expr}\""
            )),
        },
        t => Err(format!(
            "unable to evaluate prefix expression, ! or - tokens expected, but got \"{t}\"",
        )),
    }
}

fn eval_infix_expression(token: Token, left: Object, right: Object) -> InterpreterResult<Object> {
    match (left, right) {
        (Object::Integer(int_left), Object::Integer(int_right)) => match token {
            Token::Plus => Ok(Object::Integer(Integer {
                value: int_left.value + int_right.value,
            })),
            Token::Minus => Ok(Object::Integer(Integer {
                value: int_left.value - int_right.value,
            })),
            Token::Asterisk => Ok(Object::Integer(Integer {
                value: int_left.value * int_right.value,
            })),
            Token::Slash => Ok(Object::Integer(Integer {
                value: int_left.value / int_right.value,
            })),
            Token::Lt => Ok(Object::Boolean(Boolean {
                value: int_left.value < int_right.value,
            })),
            Token::Gt => Ok(Object::Boolean(Boolean {
                value: int_left.value > int_right.value,
            })),
            Token::Eq => Ok(Object::Boolean(Boolean {
                value: int_left.value == int_right.value,
            })),
            Token::Ne => Ok(Object::Boolean(Boolean {
                value: int_left.value != int_right.value,
            })),
            t => Err(format!(
                "unable to evaluate infix expression; +,-,*,/,<,>,==,!= Tokens expected, but got \"{t}\""
            )),
        },
        (Object::Boolean(bool_left),Object::Boolean(bool_right)) => match token {
            Token::Eq => Ok(Object::Boolean(Boolean { value: bool_left.value == bool_right.value })),
            Token::Ne=> Ok(Object::Boolean(Boolean { value: bool_left.value != bool_right.value })),
            t => Err(format!(
                "unable to evaluate infix expression; == or != Tokens expected, but got \"{t}\""
            )),
        }
        (left, right) => Err(format!(
            "unable to evaluate infix expression, Integer numbers expected, but got \"{left}\" \"{right}\""
        )),
    }
}

fn eval_if_expression(
    if_expr: crate::parser::ast::IfExpression,
    env: &mut Environment,
) -> InterpreterResult<Object> {
    let is_truthy = match eval((*if_expr.condition).into(), env)? {
        Object::Boolean(bool) => bool.value,
        Object::Null(_) => false,
        _ => true,
    };

    match is_truthy {
        true => Ok(eval(Statement::Block(if_expr.consequence).into(), env)?),
        false => match if_expr.alternative {
            Some(alt) => Ok(eval(Statement::Block(alt).into(), env)?),
            None => Ok(Object::Null(Null {})),
        },
    }
}

fn eval_program(statements: Vec<Statement>, env: &mut Environment) -> InterpreterResult<Object> {
    let mut result = Object::Null(Null {});

    for statement in statements {
        result = eval(statement.into(), env)?;

        if let Object::Return(return_statement) = &result {
            return Ok(*return_statement.value.clone());
        }
    }

    Ok(result)
}

#[cfg(test)]
mod test {
    use crate::{
        evaluator::{
            environment::Environment,
            evaluator::eval,
            types::{Integer, Null, Object},
        },
        lexer::lexer::Lexer,
        parser::parser::Parser,
    };

    fn evaluate_input(input: String) -> Object {
        let lexer = Lexer::new(String::from(input));
        let mut parser = Parser::new(lexer);

        let program = parser.parse_program();

        if let Err(err) = &program {
            println!("{err}");
        }

        assert!(program.is_ok());
        let program = program.unwrap();

        let mut env = Environment::new();
        let result = eval(program, &mut env);

        if let Err(err) = &result {
            println!("{err}");
        }

        assert!(result.is_ok());

        result.unwrap()
    }

    #[test]
    fn integer_expression_evaluation_test() {
        let expected = vec![
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Integer(int) => assert_eq!(int.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn boolean_expression_evaluation_test() {
        let expected = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 < 1", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 != 1", false),
            ("1 == 2", false),
            ("1 != 2", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Boolean(bool) => assert_eq!(bool.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn bang_operator_evaluation_test() {
        let expected = vec![
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Boolean(bool) => assert_eq!(bool.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn if_else_evaluation_test() {
        let expected = vec![
            ("if (true) { 10 }", Object::Integer(Integer { value: 10 })),
            ("if (false) { 10 }", Object::Null(Null {})),
            ("if (1) { 10 }", Object::Integer(Integer { value: 10 })),
            ("if (1 < 2) { 10 }", Object::Integer(Integer { value: 10 })),
            ("if (1 > 2) { 10 }", Object::Null(Null {})),
            (
                "if (1 > 2) { 10 } else { 20 }",
                Object::Integer(Integer { value: 20 }),
            ),
            (
                "if (1 < 2) { 10 } else { 20 }",
                Object::Integer(Integer { value: 10 }),
            ),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match (result, expected_result) {
                (Object::Integer(int), Object::Integer(exp)) => {
                    assert_eq!(int.value, exp.value)
                }
                (Object::Null(_), Object::Null(_)) => (),
                (actual, exp) => panic!("integers or nulls expected, but got {actual} and {exp}"),
            }
        }
    }

    #[test]
    fn return_evaluation_test() {
        let expected = vec![
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            (
                r#"
if (10 > 1) {
    if (10 > 1) {
        return 10;
    }

    return 1;
}
"#,
                10,
            ),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Integer(int) => {
                    assert_eq!(int.value, expected_result)
                }
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn let_statement_evaluation_test() {
        let expected = vec![
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Integer(int) => {
                    assert_eq!(int.value, expected_result)
                }
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }
}
