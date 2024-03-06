use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    lexer::token::Token,
    parser::ast::{
        CallExpression, Expression, HashLiteral, IfExpression, IndexExpression, InfixExpression,
        Program, Statement,
    },
    result::InterpreterResult,
};

use super::{
    environment::{Environment, OuterEnvWrapper},
    types::{
        Array, Boolean, BuiltinFunction, Function, HashTable, Integer, Null, Object, Return, Str,
    },
};

#[derive(Debug)]
enum AstTraverse {
    Node(Rc<RefCell<AstTraverseNode>>),
    #[allow(dead_code)]
    None,
}

#[derive(Debug)]
struct AstTraverseNode {
    parent_node: Option<AstTraverse>,
    node: Program,
    evaluated_children: Vec<Object>,
}

impl AstTraverse {
    fn new(node: Program, parent_node: Option<AstTraverse>) -> Self {
        AstTraverse::Node(Rc::new(RefCell::new(AstTraverseNode {
            evaluated_children: vec![],
            node,
            parent_node,
        })))
    }

    fn as_node(&self) -> Option<&Rc<RefCell<AstTraverseNode>>> {
        match self {
            AstTraverse::Node(node) => Some(node),
            AstTraverse::None => None,
        }
    }
}

pub fn eval(program: Program, env: &Rc<RefCell<Environment>>) -> InterpreterResult<Object> {
    let mut nodes_stack = vec![AstTraverse::new(program, None)];
    let mut env_stack = vec![Rc::clone(env)];

    loop {
        match nodes_stack.pop().unwrap() {
            AstTraverse::Node(cur_node) => {
                let evaluated_node = eval_ast_node(&cur_node, &mut nodes_stack, &mut env_stack)?;

                match evaluated_node {
                    Some(obj) => {
                        if nodes_stack.len() == 0 {
                            return Ok(obj);
                        }

                        match cur_node.borrow_mut().parent_node.as_ref() {
                            Some(parent_node) => match parent_node {
                                AstTraverse::Node(node) => {
                                    node.borrow_mut().evaluated_children.push(obj);
                                }
                                AstTraverse::None => return Ok(obj),
                            },
                            None => (),
                        }
                    }
                    None => (),
                }
            }
            AstTraverse::None => Err(String::from(""))?,
        };
    }
}

fn eval_ast_node(
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
    env_stack: &mut Vec<Rc<RefCell<Environment>>>,
) -> InterpreterResult<Option<Object>> {
    let env = env_stack.last().unwrap();

    match &cur_node.as_ref().borrow().node {
        Program::Statement(statement) => match statement.as_ref() {
            Statement::Expression(expr) => match cur_node.borrow().evaluated_children.last() {
                Some(expr) => Ok(Some(expr.clone())),
                None => {
                    add_current_and_new_nodes_to_stack(
                        Rc::clone(&expr.expression).into(),
                        cur_node,
                        nodes_stack,
                    );
                    Ok(None)
                }
            },
            Statement::Block(block) => Ok(eval_program(
                &block.statements,
                cur_node,
                nodes_stack,
                false,
            )),
            Statement::Return(return_statement) => {
                match cur_node.borrow().evaluated_children.last() {
                    Some(return_value) => Ok(Some(Object::Return(Return {
                        value: Box::new(return_value.clone()),
                    }))),
                    None => {
                        add_current_and_new_nodes_to_stack(
                            Rc::clone(&return_statement.return_value).into(),
                            cur_node,
                            nodes_stack,
                        );

                        Ok(None)
                    }
                }
            }
            Statement::Let(let_statement) => match cur_node.borrow().evaluated_children.last() {
                Some(let_value) => {
                    let value_key = let_statement.name.token.to_string();
                    let value = env.borrow_mut().set(value_key, let_value.clone());
                    Ok(Some(value))
                }
                None => {
                    add_current_and_new_nodes_to_stack(
                        Rc::clone(&let_statement.value).into(),
                        cur_node,
                        nodes_stack,
                    );

                    Ok(None)
                }
            },
        },
        Program::Statements(statements) => {
            Ok(eval_program(statements, cur_node, nodes_stack, true))
        }
        Program::Expression(expr) => match expr.as_ref() {
            Expression::IntegerLiteral(int) => {
                Ok(Some(Object::Integer(Integer { value: int.value })))
            }
            Expression::Boolean(bool) => Ok(Some(Object::Boolean(Boolean { value: bool.value }))),
            Expression::Prefix(prefix) => match cur_node.borrow().evaluated_children.last() {
                Some(right) => Ok(Some(eval_prefix_expression(&prefix.token, right)?)),
                None => {
                    add_current_and_new_nodes_to_stack(
                        Rc::clone(&prefix.right).into(),
                        cur_node,
                        nodes_stack,
                    );

                    Ok(None)
                }
            },
            Expression::Infix(infix) => eval_infix_expression(infix, cur_node, nodes_stack),
            Expression::If(if_expr) => Ok(eval_if_expression(if_expr, cur_node, nodes_stack)),
            Expression::Identifier(ident) => {
                let value_key = ident.token.to_string();

                match env.borrow().get(&value_key) {
                    Some(obj) => Ok(Some(obj)),
                    None => match get_builtin_function(&value_key) {
                        Some(builtin) => Ok(Some(builtin)),
                        None => Err(format!(
                            "unable to evaluate identifier, identifier \"{value_key}\" not found"
                        ))?,
                    },
                }
            }
            Expression::FunctionLiteral(func) => Ok(Some(Object::Function(Function {
                parameters: func.parameters.clone(),
                body: func.body.clone(),
                env: OuterEnvWrapper(env.clone()),
            }))),
            Expression::Call(call) => apply_function(call, cur_node, nodes_stack, env_stack),
            Expression::StringLiteral(string) => Ok(Some(Object::String(Str {
                value: string.token.to_string(),
            }))),
            Expression::ArrayLiteral(array) => match cur_node.borrow().evaluated_children.len() {
                l if l < array.elements.len() => {
                    add_current_and_new_nodes_to_stack(
                        Rc::clone(&array.elements.get(l).unwrap()).into(),
                        cur_node,
                        nodes_stack,
                    );

                    Ok(None)
                }
                _ => Ok(Some(Object::Array(Array {
                    elements: cur_node.borrow().evaluated_children.clone(),
                }))),
            },
            Expression::IndexExpression(index_expr) => {
                eval_index_expression(index_expr, cur_node, nodes_stack)
            }
            Expression::HashLiteral(hash_literal) => {
                eval_hash_literal(hash_literal, cur_node, nodes_stack)
            }
        },
    }
}

fn eval_hash_literal(
    hash_literal: &HashLiteral,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
) -> InterpreterResult<Option<Object>> {
    match cur_node.borrow().evaluated_children.len() {
        l if l < 2 * hash_literal.pairs.len() && l & 0x1 == 0 => {
            let (key, _) = hash_literal
                .pairs
                .iter()
                .enumerate()
                .find(|(idx, _)| *idx == l / 2)
                .unwrap()
                .1;

            add_current_and_new_nodes_to_stack(Rc::clone(key).into(), cur_node, nodes_stack);

            Ok(None)
        }
        l if l < 2 * hash_literal.pairs.len() && l & 0x1 == 1 => {
            match cur_node.borrow().evaluated_children.last().unwrap() {
                Object::String(_) | Object::Integer(_) | Object::Boolean(_) => (),
                actual => return Err(format!("unable to evaluate hash literal; only Integer, String or Boolean could be used as key, but got \"{actual}\"")),
            }

            let (_, value) = hash_literal
                .pairs
                .iter()
                .enumerate()
                .find(|(idx, _)| *idx == l / 2)
                .unwrap()
                .1;

            add_current_and_new_nodes_to_stack(Rc::clone(value).into(), cur_node, nodes_stack);

            Ok(None)
        }
        _ => {
            let mut pairs: HashMap<Object, Object> = HashMap::new();
            let pairs_num = cur_node.borrow().evaluated_children.len() / 2;

            for i in 0..pairs_num {
                let key = cur_node
                    .borrow()
                    .evaluated_children
                    .get(2 * i)
                    .unwrap()
                    .clone();
                let value = cur_node
                    .borrow()
                    .evaluated_children
                    .get(2 * i + 1)
                    .unwrap()
                    .clone();

                pairs.insert(key, value);
            }

            Ok(Some(Object::HashTable(HashTable { pairs })))
        }
    }
}

fn eval_index_expression(
    index_expr: &IndexExpression,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
) -> InterpreterResult<Option<Object>> {
    match cur_node.borrow().evaluated_children.len() {
        0 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&index_expr.left).into(),
                cur_node,
                nodes_stack,
            );

            Ok(None)
        }
        1 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&index_expr.index).into(),
                cur_node,
                nodes_stack,
            );

            Ok(None)
        }
        _ => {
            let left = cur_node
                .borrow()
                .evaluated_children
                .get(0)
                .ok_or(String::from(
                    "internal error while evaluating index expression",
                ))?
                .clone();
            let index = cur_node
                .borrow()
                .evaluated_children
                .get(1)
                .ok_or(String::from(
                    "internal error while evaluating index expression",
                ))?
                .clone();

            match (left, index) {
                (Object::Array(array), Object::Integer(idx)) => {
                    let max_idx = array.elements.len() - 1;

                    if idx.value < 0 || idx.value as usize > max_idx {
                        return Ok(Some(Object::Null(Null {})));
                    }

                    Ok(Some(
                        array.elements.get(idx.value as usize).cloned().unwrap(),
                    ))
                }
                (Object::HashTable(hash_table), idx) => {
                    match idx {
                    Object::String(_) | Object::Integer(_) | Object::Boolean(_) => (),
                    actual => return Err(format!("unable to index hash table; only Integer, String or Boolean could be used as key, but got \"{actual}\"")), };

                    Ok(Some(
                        hash_table
                            .pairs
                            .get(&idx)
                            .unwrap_or(&Object::Null(Null {}))
                            .clone(),
                    ))
                }
                (actual_left, actual_index) => Err(format!(
                    "index operator not supported for \"{actual_left}\" and \"{actual_index}\""
                ))?,
            }
        }
    }
}

fn eval_infix_expression(
    infix: &InfixExpression,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
) -> InterpreterResult<Option<Object>> {
    match cur_node.borrow().evaluated_children.len() {
        0 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&infix.left).into(),
                cur_node,
                nodes_stack,
            );
            Ok(None)
        }
        1 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&infix.right).into(),
                cur_node,
                nodes_stack,
            );
            Ok(None)
        }
        _ => {
            let left = cur_node
                .borrow()
                .evaluated_children
                .get(0)
                .ok_or(String::from(
                    "internal error while evaluating infix expression",
                ))?
                .clone();
            let right = cur_node
                .borrow()
                .evaluated_children
                .get(1)
                .ok_or(String::from(
                    "internal error while evaluating infix expression",
                ))?
                .clone();
            Ok(Some(calculate_infix_expression(&infix.token, left, right)?))
        }
    }
}

fn apply_function(
    call: &CallExpression,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
    env_stack: &mut Vec<Rc<RefCell<Environment>>>,
) -> InterpreterResult<Option<Object>> {
    match cur_node.borrow().evaluated_children.len() {
        0 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&call.function).into(),
                cur_node,
                nodes_stack,
            );
            Ok(None)
        }
        l if l <= call.arguments.len() => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&call.arguments.get(l - 1).unwrap()).into(),
                cur_node,
                nodes_stack,
            );

            Ok(None)
        }
        l if l == call.arguments.len() + 1 => {
            let function = cur_node
                .borrow()
                .evaluated_children
                .first()
                .ok_or(String::from(""))?
                .clone();
            let args = cur_node
                .borrow()
                .evaluated_children
                .get(1..)
                .map_or(vec![], |args| args.iter().cloned().collect());

            match function {
                Object::Function(func) => {
                    env_stack.push(extend_function_environment(func.clone(), args));
                    add_current_and_new_nodes_to_stack(
                        Rc::clone(&func.body).into(),
                        cur_node,
                        nodes_stack,
                    );

                    Ok(None)
                }
                Object::Builtin(builtin) => Ok(Some(builtin.0(args)?)),
                actual => Err(format!(
                    "unable to evaluate function call, function excpected, but got \"{actual}\""
                )),
            }
        }
        _ => {
            env_stack.pop();
            let evaluated = cur_node.borrow().evaluated_children.last().unwrap().clone();

            match evaluated {
                Object::Return(return_obj) => Ok(Some(*return_obj.value)),
                _ => Ok(Some(evaluated)),
            }
        }
    }
}

fn extend_function_environment(func: Function, args: Vec<Object>) -> Rc<RefCell<Environment>> {
    let mut env = Environment::new_outer(func.env.0);

    for (idx, param) in func.parameters.iter().enumerate() {
        env.set(param.token.to_string(), args.get(idx).unwrap().clone());
    }

    Rc::new(RefCell::new(env))
}

fn eval_prefix_expression(token: &Token, right: &Object) -> InterpreterResult<Object> {
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

fn calculate_infix_expression(
    token: &Token,
    left: Object,
    right: Object,
) -> InterpreterResult<Object> {
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
                "unable to evaluate infix expression for Integers; +,-,*,/,<,>,==,!= Tokens expected, but got \"{t}\""
            )),
        },
        (Object::Boolean(bool_left),Object::Boolean(bool_right)) => match token {
            Token::Eq => Ok(Object::Boolean(Boolean { value: bool_left.value == bool_right.value })),
            Token::Ne=> Ok(Object::Boolean(Boolean { value: bool_left.value != bool_right.value })),
            t => Err(format!(
                "unable to evaluate infix expression for Booleans; == or != Tokens expected, but got \"{t}\""
            )),
        },
        (Object::String(string_left), Object::String(string_right)) => match token {
            Token::Plus => Ok(Object::String(Str { value: format!("{string_left}{string_right}") })),
            t => Err(format!("unable to evaluate infix expression for Strings; + Token expected, but got \"{t}\""))
        }
        (left, right) => Err(format!(
            "unable to evaluate infix expression; Integers, Booleans or Strings expected, but got \"{left}\" \"{right}\""
        )),
    }
}

fn eval_if_expression(
    if_expr: &IfExpression,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
) -> Option<Object> {
    match cur_node.borrow().evaluated_children.len() {
        0 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(&if_expr.condition).into(),
                cur_node,
                nodes_stack,
            );

            None
        }
        1 => {
            if let Some(Object::Null(_)) = nodes_stack
                .last()
                .unwrap()
                .as_node()
                .unwrap()
                .borrow()
                .evaluated_children
                .last()
            {
                return None;
            }

            let is_truthy = match cur_node.borrow().evaluated_children.last().unwrap() {
                Object::Boolean(bool) => bool.value,
                _ => true,
            };

            match is_truthy {
                true => {
                    add_current_and_new_nodes_to_stack(
                        if_expr.consequence.clone().into(),
                        cur_node,
                        nodes_stack,
                    );

                    None
                }
                false => match &if_expr.alternative {
                    Some(alt) => {
                        add_current_and_new_nodes_to_stack(
                            alt.clone().into(),
                            cur_node,
                            nodes_stack,
                        );

                        None
                    }
                    None => Some(Object::Null(Null {})),
                },
            }
        }
        _ => Some(cur_node.borrow().evaluated_children.last().unwrap().clone()),
    }
}

fn eval_program(
    statements: &Vec<Rc<Statement>>,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
    unwrap_return: bool,
) -> Option<Object> {
    if statements.len() == 0 {
        return None;
    }

    match cur_node.borrow().evaluated_children.len() {
        l if l == 0 => {
            add_current_and_new_nodes_to_stack(
                Rc::clone(statements.first().unwrap()).into(),
                cur_node,
                nodes_stack,
            );

            None
        }
        l => {
            if let Object::Return(return_statement) =
                cur_node.borrow().evaluated_children.last().unwrap()
            {
                return match unwrap_return {
                    true => Some(*return_statement.value.clone()),
                    false => Some(cur_node.borrow().evaluated_children.last().unwrap().clone()),
                };
            }

            if l != statements.len() {
                add_current_and_new_nodes_to_stack(
                    Rc::clone(statements.get(l).unwrap()).into(),
                    cur_node,
                    nodes_stack,
                );
            }

            Some(cur_node.borrow().evaluated_children.last().unwrap().clone())
        }
    }
}

fn add_current_and_new_nodes_to_stack(
    program: Program,
    cur_node: &Rc<RefCell<AstTraverseNode>>,
    nodes_stack: &mut Vec<AstTraverse>,
) {
    nodes_stack.push(AstTraverse::Node(Rc::clone(&cur_node)));
    nodes_stack.push(AstTraverse::new(
        program,
        Some(AstTraverse::Node(Rc::clone(cur_node))),
    ));
}

fn get_builtin_function(fn_name: &str) -> Option<Object> {
    match fn_name {
        "len" => Some(Object::Builtin(BuiltinFunction(len_builtin))),
        "first" => Some(Object::Builtin(BuiltinFunction(first_builtin))),
        "last" => Some(Object::Builtin(BuiltinFunction(last_builtin))),
        "rest" => Some(Object::Builtin(BuiltinFunction(rest_builtin))),
        "push" => Some(Object::Builtin(BuiltinFunction(push_builtin))),
        "puts" => Some(Object::Builtin(BuiltinFunction(puts_builtin))),
        _ => None,
    }
}

fn len_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    if args.len() != 1 {
        return Err(format!(
            "wrong number of arguments for len function, 1 argument expected, but got {}",
            args.len()
        ));
    }

    match args.first().unwrap() {
        Object::String(string) => Ok(Object::Integer(Integer {
            value: string.value.len() as i64,
        })),
        Object::Array(array) => Ok(Object::Integer(Integer {
            value: array.elements.len() as i64,
        })),
        actual => Err(format!(
            "argument to len function is not supported, String expected, but got {actual}"
        )),
    }
}

fn first_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    if args.len() != 1 {
        return Err(format!(
            "wrong number of arguments for first function, 1 argument expected, but got {}",
            args.len()
        ));
    }

    match args.first().unwrap() {
        Object::Array(array) => match array.elements.len() {
            0 => Ok(Object::Null(Null {})),
            _ => Ok(array.elements.get(0).cloned().unwrap()),
        },
        actual => Err(format!(
            "argument to first function is not supported, Array expected, but got {actual}"
        )),
    }
}

fn last_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    if args.len() != 1 {
        return Err(format!(
            "wrong number of arguments for last function, 1 argument expected, but got {}",
            args.len()
        ));
    }

    match args.first().unwrap() {
        Object::Array(array) => match array.elements.len() {
            0 => Ok(Object::Null(Null {})),
            _ => Ok(array
                .elements
                .get(array.elements.len() - 1)
                .cloned()
                .unwrap()),
        },
        actual => Err(format!(
            "argument to last function is not supported, Array expected, but got {actual}"
        )),
    }
}

fn rest_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    if args.len() != 1 {
        return Err(format!(
            "wrong number of arguments for rest function, 1 argument expected, but got {}",
            args.len()
        ));
    }

    match args.first().unwrap() {
        Object::Array(array) => match array.elements.len() {
            0 => Ok(Object::Null(Null {})),
            _ => Ok(Object::Array(Array {
                elements: array.elements[1..].to_vec(),
            })),
        },
        actual => Err(format!(
            "argument to rest function is not supported, Array expected, but got {actual}"
        )),
    }
}

fn push_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    if args.len() != 2 {
        return Err(format!(
            "wrong number of arguments for push function, 2 argument expected, but got {}",
            args.len()
        ));
    }

    match args.first().unwrap() {
        Object::Array(array) => {
            let mut new_elements = array.elements.clone();
            new_elements.push(args.get(1).cloned().unwrap());

            Ok(Object::Array(Array {
                elements: new_elements,
            }))
        }
        actual => Err(format!(
            "argument to push function is not supported, Array expected, but got {actual}"
        )),
    }
}

fn puts_builtin(args: Vec<Object>) -> InterpreterResult<Object> {
    for arg in args {
        println!("{arg}");
    }

    Ok(Object::Null(Null {}))
}

#[cfg(test)]
mod test {
    use std::{cell::RefCell, rc::Rc};

    use crate::{
        evaluator::{
            environment::Environment,
            evaluator::eval,
            types::{Boolean, Integer, Null, Object, Str},
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

        let env = Environment::new();
        let result = eval(program, &Rc::new(RefCell::new(env)));

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
                (Object::Integer(int), Object::Integer(exp)) => assert_eq!(int.value, exp.value),
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
                Object::Integer(int) => assert_eq!(int.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn function_evaluation_test() {
        let input = "fn(x) { x + 2; };";

        let result = evaluate_input(input.to_string());

        match result {
            Object::Function(func) => {
                assert_eq!(func.parameters.len(), 1);
                assert_eq!(func.parameters.first().unwrap().to_string(), "x");
                assert_eq!(func.body.to_string(), "(x + 2)");
            }
            actual => panic!("function expected, but got {actual}"),
        }
    }

    #[test]
    fn function_application_evaluation_test() {
        let expected = vec![
            ("let identity = fn(x) { x; }; identity(5);", 5),
            ("let identity = fn(x) { return x; }; identity(5);", 5),
            ("let double = fn(x) { x * 2; }; double(5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            ("fn(x) { x; }(5)", 5),
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
    fn closure_test() {
        let input = r#"
let newAdder = fn(x) {
    fn(y) { x + y };
};
let addTwo = newAdder(2);
addTwo(2);"#;

        let result = evaluate_input(input.to_string());

        match result {
            Object::Integer(int) => assert_eq!(int.value, 4),
            actual => panic!("integer expected, but got {actual}"),
        }
    }

    #[test]
    fn string_literal_evaluation_test() {
        let input = r#""Hello World!""#;

        let result = evaluate_input(input.to_string());

        match result {
            Object::String(string) => assert_eq!(string.value, "Hello World!"),
            actual => panic!("string expected, but got {actual}"),
        }
    }

    #[test]
    fn string_concatination_evaluation_test() {
        let input = r#""Hello" + " " + "World!""#;

        let result = evaluate_input(input.to_string());

        match result {
            Object::String(string) => assert_eq!(string.value, "Hello World!"),
            actual => panic!("string expected, but got {actual}"),
        }
    }

    #[test]
    fn builtin_evaluation_test() {
        let expected = vec![
            ("len(\"\")", 0),
            ("len(\"four\")", 4),
            ("len(\"hello world\")", 11),
            ("len([1, 4, 9, 5])", 4),
            ("first([1, 4, 9, 5])", 1),
            ("last([1, 4, 9, 5])", 5),
        ];

        for (input, expected_result) in expected {
            println!("here");
            let result = evaluate_input(input.to_string());

            match result {
                Object::Integer(int) => assert_eq!(int.value, expected_result),
                actual => panic!("integer expected, but got {actual}"),
            }
        }
    }

    #[test]
    fn array_evaluation_test() {
        let input = "[1, 2 * 2, 3 + 3]";

        let result = evaluate_input(input.to_string());

        match result {
            Object::Array(array) => {
                assert_eq!(array.elements.len(), 3);

                match (
                    array.elements.get(0).unwrap(),
                    array.elements.get(1).unwrap(),
                    array.elements.get(2).unwrap(),
                ) {
                    (Object::Integer(int1), Object::Integer(int2), Object::Integer(int3)) => {
                        assert_eq!(int1.value, 1);
                        assert_eq!(int2.value, 4);
                        assert_eq!(int3.value, 6);
                    }
                    (actual1, actual2, actual3) => {
                        panic!("integers expected, but got {actual1}, {actual2}, {actual3}")
                    }
                }
            }
            actual => panic!("array expected, but got {actual}"),
        }
    }

    #[test]
    fn array_index_expression_test() {
        let expected = vec![
            ("[1, 2, 3][0]", 1),
            ("[1, 2, 3][1]", 2),
            ("[1, 2, 3][2]", 3),
            ("let i = 0; [1][i];", 1),
            ("[1, 2, 3][1 + 1];", 3),
            ("let myArray = [1, 2, 3]; myArray[2];", 3),
            (
                "let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];",
                6,
            ),
            ("let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i]", 2),
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
    fn array_builtins_test() {
        let expected = vec![
            (
                r#"
let map = fn(arr, f) {
    let iter = fn(arr, accumulated) {
        if (len(arr) == 0) {
            accumulated
        } else {
            iter(rest(arr), push(accumulated, f(first(arr))));
        }
    };

    iter(arr, []);
};

let a = [1, 2, 3, 4];
let double = fn(x) { x * 2 };
map(a, double);
    "#,
                "[2, 4, 6, 8]",
            ),
            (
                r#"
let reduce = fn(arr, initial, f) {
    let iter = fn(arr, result) {
        if (len(arr) == 0) {
            result
        } else {
            iter(rest(arr), f(result, first(arr)));
        }
    };
    iter(arr, initial);
};

let sum = fn(arr) {
    reduce(arr, 0, fn(initial, el) { initial + el });
};
sum([1, 2, 3, 4, 5]);
    "#,
                "15",
            ),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());

            assert_eq!(result.to_string(), expected_result);
        }
    }

    #[test]
    fn hash_literals_evaluation_test() {
        let input = r#"let two = "two";
{
    "one": 10 - 9,
    two: 1 + 1,
    "thr" + "ee": 6 / 2,
    4: 4,
    true: 5,
    false: 6
}"#;

        let expected = vec![
            (
                Object::String(Str {
                    value: String::from("one"),
                }),
                1,
            ),
            (
                Object::String(Str {
                    value: String::from("two"),
                }),
                2,
            ),
            (
                Object::String(Str {
                    value: String::from("three"),
                }),
                3,
            ),
            (Object::Integer(Integer { value: 4 }), 4),
            (Object::Boolean(Boolean { value: true }), 5),
            (Object::Boolean(Boolean { value: false }), 6),
        ];

        let result = evaluate_input(input.to_string());

        match result {
            Object::HashTable(hash) => {
                assert_eq!(hash.pairs.len(), 6);

                for (key, expected_value) in expected {
                    let result_value = hash.pairs.get(&key);
                    assert!(result_value.is_some());

                    match result_value.unwrap() {
                        Object::Integer(int) => assert_eq!(int.value, expected_value),
                        actual => panic!("integer expected, but got {actual}"),
                    }
                }
            }
            actual => panic!("hash map expected, but got {actual}"),
        }
    }

    #[test]
    fn hash_indexing_evaluation_test() {
        let expected = vec![
            (r#"{"foo": 5}["foo"]"#, "5"),
            (r#"{"foo": 5}["bar"]"#, "null"),
            (r#"let key = "foo"; {"foo": 5}[key]"#, "5"),
            (r#"{}["foo"]"#, "null"),
            (r#"{5: 5}[5]"#, "5"),
            (r#"{true: 5}[true]"#, "5"),
            (r#"{false: 5}[false]"#, "5"),
        ];

        for (input, expected_result) in expected {
            let result = evaluate_input(input.to_string());
            assert_eq!(result.to_string().as_str(), expected_result);
        }
    }

    #[test]
    fn stack_overflow_test() {
        let input = r#"
let counter = fn(x) {
    if (x > 1000) {
        return true;
    } else {
        let foobar = 9999;
        counter(x + 1);
    }
};
counter(0);
"#;

        _ = evaluate_input(input.to_string());
    }
}
