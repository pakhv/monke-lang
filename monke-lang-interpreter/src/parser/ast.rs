use std::{any::Any, fmt::Debug};

use crate::lexer::token::Token;

#[derive(Debug)]
pub struct Program {
    pub statements: Vec<Box<dyn Statement>>,
}

pub trait Statement: Debug {
    fn as_any(&self) -> &dyn Any;
}
#[derive(Debug)]
pub struct Expression {}

#[derive(Debug)]
pub struct LetStatement {
    pub token: Token,
    pub name: Token,
    pub value: Expression,
}

impl Statement for LetStatement {
    fn as_any(&self) -> &dyn Any {
        self
    }
}
