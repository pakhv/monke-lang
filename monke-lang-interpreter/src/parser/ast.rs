use crate::lexer::token::Token;
use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    rc::Rc,
};

pub enum ExpressionType {
    Lowest = 1,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Product,     // *
    Prefix,      // -X or !X
    Call,        // myFunction(X)
    Index,
}

#[derive(Debug, Clone)]
pub enum Program {
    Statement(Rc<Statement>),
    Statements(Vec<Rc<Statement>>),
    Expression(Rc<Expression>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expression {
    Identifier(Identifier),
    IntegerLiteral(IntegerLiteral),
    StringLiteral(StringLiteral),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    Boolean(Boolean),
    If(IfExpression),
    FunctionLiteral(FunctionLiteral),
    Call(CallExpression),
    ArrayLiteral(ArrayLiteral),
    IndexExpression(IndexExpression),
    HashLiteral(HashLiteral),
}

impl Expression {
    fn same_type(&self, other: &Self) -> bool {
        match (self, other) {
            (Expression::Identifier(_), Expression::Identifier(_)) => true,
            (Expression::IntegerLiteral(_), Expression::IntegerLiteral(_)) => true,
            (Expression::StringLiteral(_), Expression::StringLiteral(_)) => true,
            (Expression::Prefix(_), Expression::Prefix(_)) => true,
            (Expression::Infix(_), Expression::Infix(_)) => true,
            (Expression::Boolean(_), Expression::Boolean(_)) => true,
            (Expression::If(_), Expression::If(_)) => true,
            (Expression::FunctionLiteral(_), Expression::FunctionLiteral(_)) => true,
            (Expression::Call(_), Expression::Call(_)) => true,
            (Expression::ArrayLiteral(_), Expression::ArrayLiteral(_)) => true,
            (Expression::IndexExpression(_), Expression::IndexExpression(_)) => true,
            (Expression::HashLiteral(_), Expression::HashLiteral(_)) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
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
            Expression::StringLiteral(string) => write!(f, "{string}"),
            Expression::ArrayLiteral(array) => write!(f, "{array}"),
            Expression::IndexExpression(index_expr) => write!(f, "{index_expr}"),
            Expression::HashLiteral(hash_literal) => write!(f, "{hash_literal}"),
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

impl From<Rc<Expression>> for Program {
    fn from(expression: Rc<Expression>) -> Self {
        Program::Expression(Rc::clone(&expression))
    }
}

impl From<Rc<Statement>> for Program {
    fn from(statement: Rc<Statement>) -> Self {
        Program::Statement(Rc::clone(&statement))
    }
}

impl From<Vec<Rc<Statement>>> for Program {
    fn from(statements: Vec<Rc<Statement>>) -> Self {
        Program::Statements(statements)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Identifier {
    pub token: Token,
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct IntegerLiteral {
    pub token: Token,
    pub value: i64,
}

impl Display for IntegerLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct StringLiteral {
    pub token: Token,
}

impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct PrefixExpression {
    pub token: Token,
    pub right: Rc<Expression>,
}

impl Display for PrefixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}{})", self.token, self.right)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct InfixExpression {
    pub token: Token,
    pub left: Rc<Expression>,
    pub right: Rc<Expression>,
}

impl Display for InfixExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} {} {})", self.left, self.token, self.right)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Boolean {
    pub token: Token,
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct IfExpression {
    pub token: Token,
    pub condition: Rc<Expression>,
    pub consequence: Rc<BlockStatement>,
    pub alternative: Option<Rc<BlockStatement>>,
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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CallExpression {
    pub token: Token,
    pub function: Rc<Expression>,
    pub arguments: Vec<Rc<Expression>>,
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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ArrayLiteral {
    pub token: Token,
    pub elements: Vec<Rc<Expression>>,
}

impl Display for ArrayLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements = self
            .elements
            .iter()
            .map(|b| b.to_string())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        write!(f, "[{elements}]")
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct IndexExpression {
    pub token: Token,
    pub left: Rc<Expression>,
    pub index: Rc<Expression>,
}

impl Display for IndexExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}[{}])", self.left, self.index)
    }
}

#[derive(Debug, Clone, Eq)]
pub struct HashLiteral {
    pub token: Token,
    pub pairs: HashMap<Rc<Expression>, Rc<Expression>>,
}

impl Hash for HashLiteral {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.token.hash(state);
        let mut to_vec: Vec<_> = self
            .pairs
            .iter()
            .map(|(key, value)| (key.to_string(), value.to_string()))
            .collect();
        to_vec.sort_by(|(a, _), (b, _)| a.cmp(b));

        to_vec.hash(state);
    }
}

impl PartialEq for HashLiteral {
    fn eq(&self, other: &Self) -> bool {
        if self.token != other.token {
            return false;
        }

        let mut pairs_a: Vec<_> = self
            .pairs
            .iter()
            .map(|(key, value)| (key.to_string(), key, value))
            .collect();
        pairs_a.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

        let mut pairs_b: Vec<_> = self
            .pairs
            .iter()
            .map(|(key, value)| (key.to_string(), key, value))
            .collect();
        pairs_b.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

        for ((key_a, key_expr_a, value_expr_a), (key_b, key_expr_b, value_expr_b)) in
            pairs_a.iter().zip(pairs_b)
        {
            if key_a != &key_b
                || !key_expr_a.same_type(key_expr_b)
                || !value_expr_a.same_type(value_expr_b)
            {
                return false;
            }
        }

        true
    }
}

impl Display for HashLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements = self
            .pairs
            .iter()
            .map(|(key, value)| format!("{key}: {value}"))
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        write!(f, "{{ {} }}", elements)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Rc<Expression>,
}

impl Display for LetStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {} = {};", &self.token, &self.name, &self.value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ReturnStatement {
    pub token: Token,
    pub return_value: Rc<Expression>,
}

impl Display for ReturnStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {};", &self.token, &self.return_value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Rc<Expression>,
}

impl Display for ExpressionStatement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BlockStatement {
    pub token: Token,
    pub statements: Vec<Rc<Statement>>,
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
