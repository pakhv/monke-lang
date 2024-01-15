use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::parser::ast::{BlockStatement, Identifier};

use super::environment::Environment;

#[derive(Debug, Clone)]
pub enum Object {
    Integer(Integer),
    Boolean(Boolean),
    Null(Null),
    Return(Return),
    Function(Function),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Integer(int) => write!(f, "{int}"),
            Object::Boolean(bool) => write!(f, "{bool}"),
            Object::Null(null) => write!(f, "{null}"),
            Object::Return(return_statement) => write!(f, "{return_statement}"),
            Object::Function(func) => write!(f, "{func}"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Integer {
    pub value: i64,
}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct Boolean {
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct Null {}

impl Display for Null {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "null")
    }
}

#[derive(Debug, Clone)]
pub struct Return {
    pub value: Box<Object>,
}

impl Display for Return {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
    pub env: Rc<RefCell<Environment>>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let params = self
            .parameters
            .iter()
            .map(|p| p.to_string())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        // rip indentation
        write!(f, "fn({params}) {{\n{}\n}}", self.body)
    }
}
