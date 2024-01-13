use crate::parser::ast::{Expression, Program, Statement};

use super::types::{Integer, Null, Object};

pub fn eval(program: Program) -> Object {
    match program {
        Program::Statement(statement) => match statement {
            Statement::Expression(expr) => eval(expr.expression.into()),
            _ => todo!(),
        },
        Program::Statements(statements) => eval_statements(statements),
        Program::Expression(expr) => match expr {
            Expression::IntegerLiteral(int) => Object::Integer(Integer { value: int.value }),
            _ => todo!(),
        },
        Program::Expressions(_) => todo!(),
    }
}

fn eval_statements(statements: Vec<Statement>) -> Object {
    let mut result = Object::Null(Null {});

    for statement in statements {
        result = eval(statement.into());
    }

    result
}

#[cfg(test)]
mod test {
    use crate::{
        evaluator::{evaluator::eval, types::Object},
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

        eval(program)
    }

    #[test]
    fn integer_expression_evaluation_test() {
        let expected = vec![("5", 5), ("10", 10)];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            match result {
                Object::Integer(int) => assert_eq!(int.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }
}
