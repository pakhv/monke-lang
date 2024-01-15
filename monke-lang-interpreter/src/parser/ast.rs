use crate::lexer::token::Token;
use std::fmt::{Debug, Display};

pub enum ExpressionType {
    Lowest = 1,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // myFunction(X)
}

#[derive(Debug, Clone)]
pub enum Program {
    Statement(Statement),
    Statements(Vec<Statement>),
    Expression(Expression),
    Expressions(Vec<Expression>),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    Boolean(Boolean),
    If(IfExpression),
    FunctionLiteral(FunctionLiteral),
    Call(CallExpression),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
    Block(BlockStatement),
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Program::Statement(statement) => write!(f, "{statement}"),
            Program::Statements(statements) => {
                write!(
                    f,
                    "{}",
                    statements
                        .iter()
                        .map(|s| s.to_string())
                        .reduce(|acc, cur| format!("{acc}{cur}"))
                        .unwrap_or(String::new())
                )
            }
            Program::Expression(expression) => write!(f, "{expression}"),
            Program::Expressions(expressions) => {
                write!(
                    f,
                    "{}",
                    expressions
                        .iter()
                        .map(|e| e.to_string())
                        .reduce(|acc, cur| format!("{acc}{cur}"))
                        .unwrap_or(String::new())
                )
            }
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Identifier(ident) => write!(f, "{ident}"),
            Expression::IntegerLiteral(int) => write!(f, "{int}"),
            Expression::Prefix(prefix) => write!(f, "{prefix}"),
            Expression::Infix(infix) => write!(f, "{infix}"),
            Expression::Boolean(boolean) => write!(f, "{boolean}"),
            Expression::If(if_expr) => write!(f, "{if_expr}"),
            Expression::FunctionLiteral(func) => write!(f, "{func}"),
            Expression::Call(call) => write!(f, "{call}"),
        }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Let(let_statement) => write!(f, "{let_statement}"),
            Statement::Return(return_statement) => write!(f, "{return_statement}"),
            Statement::Expression(expr) => write!(f, "{expr}"),
            Statement::Block(block) => write!(f, "{block}"),
        }
    }
}

impl From<Expression> for Program {
    fn from(expression: Expression) -> Self {
        Program::Expression(expression)
    }
}

impl From<Vec<Expression>> for Program {
    fn from(expressions: Vec<Expression>) -> Self {
        Program::Expressions(expressions)
    }
}

impl From<Statement> for Program {
    fn from(statement: Statement) -> Self {
        Program::Statement(statement)
    }
}

impl From<Vec<Statement>> for Program {
    fn from(statements: Vec<Statement>) -> Self {
        Program::Statements(statements)
    }
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub token: Token,
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

#[derive(Debug, Clone)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl Display for IntegerLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

#[derive(Debug, Clone)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: Box<Expression>,
}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}{})", self.token, self.right)
    }
}

#[derive(Debug, Clone)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {} {})", self.left, self.token, self.right)
    }
}

#[derive(Debug, Clone)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

impl Display for IfExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = format!("if {} {}", self.condition, self.consequence);

        if let Some(alt) = self.alternative.as_ref() {
            buffer.push_str(&format!("else {}", alt));
        }

        write!(f, "{}", buffer)
    }
}

#[derive(Debug, Clone)]
pub struct FunctionLiteral {
    pub token: Token,
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

impl Display for FunctionLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut buffer = self.token.to_string();

        let params = self
            .parameters
            .iter()
            .map(|p| p.to_string())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        buffer.push_str(&format!("({}){}", params, self.body));

        write!(f, "{}", buffer)
    }
}

#[derive(Debug, Clone)]
pub struct CallExpression {
    pub token: Token,
    pub function: Box<Expression>,
    pub arguments: Vec<Expression>,
}

impl Display for CallExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let arguments = self
            .arguments
            .iter()
            .map(|a| a.to_string())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        write!(f, "{}({})", self.function, arguments)
    }
}

#[derive(Debug, Clone)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Expression,
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} = {};", &self.token, &self.name, &self.value)
    }
}

#[derive(Debug, Clone)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Expression,
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {};", &self.token, &self.return_value)
    }
}

#[derive(Debug, Clone)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Expression,
}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[derive(Debug, Clone)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Statement>,
}

impl Display for BlockStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let block = self
            .statements
            .iter()
            .map(|b| b.to_string())
            .reduce(|acc, cur| format!("{acc} {cur}"))
            .unwrap_or(String::new());

        write!(f, "{block}")
    }
}
