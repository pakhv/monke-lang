use crate::lexer::token::Token;
use std::{any::Any, fmt::Debug};

pub trait Node {
    fn pretty_print(&self) -> String;
}

pub trait Statement: Debug + Node {
    fn as_any(&self) -> &dyn Any;
}

pub trait Expression: Debug + Node {
    fn as_any(&self) -> &dyn Any;
}

pub enum ExpressionType {
    Lowest = 1,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // myFunction(X)
}

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

#[derive(Debug)]
pub struct Identifier {
    pub token: Token,
}

impl Expression for Identifier {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for Identifier {
    fn pretty_print(&self) -> String {
        self.token.to_string()
    }
}

#[derive(Debug)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl Expression for IntegerLiteral {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for IntegerLiteral {
    fn pretty_print(&self) -> String {
        self.token.to_string()
    }
}

#[derive(Debug)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: Box<dyn Expression>,
}

impl Expression for PrefixExpression {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for PrefixExpression {
    fn pretty_print(&self) -> String {
        format!("({}{})", self.token, self.right.pretty_print())
    }
}

#[derive(Debug)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<dyn Expression>,
    pub right: Box<dyn Expression>,
}

impl Expression for InfixExpression {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for InfixExpression {
    fn pretty_print(&self) -> String {
        format!(
            "({} {} {})",
            self.left.pretty_print(),
            self.token,
            self.right.pretty_print()
        )
    }
}

#[derive(Debug)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}

impl Expression for Boolean {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for Boolean {
    fn pretty_print(&self) -> String {
        self.value.to_string()
    }
}

#[derive(Debug)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<dyn Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl Expression for IfExpression {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for IfExpression {
    fn pretty_print(&self) -> String {
        let mut buffer = format!(
            "if {} {}",
            self.condition.pretty_print(),
            self.consequence.pretty_print()
        );

        if let Some(alt) = self.alternative.as_ref() {
            buffer.push_str(&format!("else {}", alt.pretty_print()));
        }

        buffer
    }
}

#[derive(Debug)]
pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Expression for FunctionLiteral {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for FunctionLiteral {
    fn pretty_print(&self) -> String {
        let mut buffer = self.token.to_string();

        let params = self
            .parameters
            .iter()
            .map(|p| p.pretty_print())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        buffer.push_str(&format!("({}){}", params, self.body.pretty_print()));

        buffer
    }
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
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
            &self.name.pretty_print(),
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

#[derive(Debug)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Box<dyn Statement>>,
}

impl Statement for BlockStatement {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl Node for BlockStatement {
    fn pretty_print(&self) -> String {
        let block = self
            .statements
            .iter()
            .map(|s| s.pretty_print())
            .reduce(|acc, cur| format!("{acc} {cur}"))
            .unwrap_or(String::from(""));

        format!("{{ {block} }}")
    }
}
