use crate::lexer::token::Token;
use std::{any::Any, fmt::Debug};

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Box<dyn Statement>>,
}

impl Node for Program {
    fn pretty_print(&self) -> String {
        let mut buffer = String::new();

        for statement in &self.statements {
            buffer.push_str(&statement.pretty_print());
        }

        buffer
    }
}

pub trait Node {
    fn pretty_print(&self) -> String;
}

pub trait Statement: Debug + Node {
    fn as_any(&self) -> &dyn Any;
}

pub trait Expression: Debug + Node {}

#[derive(Debug)]
pub struct Identifier {
    pub token: Token,
}

impl Expression for Identifier {}

impl Node for Identifier {
    fn pretty_print(&self) -> String {
        self.token.to_string()
    }
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: Token,
    pub name: Token,
    pub value: Box<dyn Expression>,
}

impl Statement for LetStatement {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for LetStatement {
    fn pretty_print(&self) -> String {
        let mut buffer = String::new();

        buffer.push_str(&format!(
            "{} {} = {};",
            &self.token.to_string(),
            &self.name.to_string(),
            &self.value.pretty_print()
        ));

        buffer
    }
}

#[derive(Debug)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Box<dyn Expression>,
}

impl Statement for ReturnStatement {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for ReturnStatement {
    fn pretty_print(&self) -> String {
        let mut buffer = String::new();

        buffer.push_str(&format!(
            "{} {};",
            &self.token.to_string(),
            &self.return_value.pretty_print()
        ));

        buffer
    }
}

#[derive(Debug)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Box<dyn Expression>,
}

impl Statement for ExpressionStatement {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for ExpressionStatement {
    fn pretty_print(&self) -> String {
        format!("{}", self.expression.pretty_print())
    }
}
