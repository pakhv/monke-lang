use crate::evaluator::environment::OuterEnvWrapper;
use std::{collections::HashMap, fmt::Display, hash::Hash, rc::Rc};

use crate::{
    code::code::Instructions,
    parser::ast::{Identifier, Statement},
    result::MonkeyResult,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Object {
    Integer(Integer),
    Boolean(Boolean),
    Null(Null),
    Return(Return),
    Function(Function),
    String(Str),
    Builtin(BuiltinFunction),
    Array(Array),
    HashTable(HashTable),
    CompiledFunction(CompiledFunction),
    Closure(Closure),
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Object::Integer(int) => write!(f, "{int}"),
            Object::Boolean(bool) => write!(f, "{bool}"),
            Object::Null(null) => write!(f, "{null}"),
            Object::Return(return_statement) => write!(f, "{return_statement}"),
            Object::Function(func) => write!(f, "{func}"),
            Object::String(string) => write!(f, "{string}"),
            Object::Builtin(builtin) => write!(f, "{builtin}"),
            Object::Array(array) => write!(f, "{array}"),
            Object::HashTable(hash) => write!(f, "{hash}"),
            Object::CompiledFunction(compiled_function) => write!(f, "{compiled_function}"),
            Object::Closure(closure) => write!(f, "{closure}"),
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Integer {
    pub value: i64,
}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Boolean {
    pub value: bool,
}

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Null {}

impl Display for Null {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "null")
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Return {
    pub value: Box<Object>,
}

impl Display for Return {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value.to_string())
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Function {
    pub parameters: Vec<Identifier>,
    pub body: Rc<Statement>,
    pub env: OuterEnvWrapper,
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

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Str {
    pub value: String,
}

impl Display for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BuiltinFunction(pub fn(args: Vec<Object>) -> MonkeyResult<Object>);

impl Display for BuiltinFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "builtin function")
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Array {
    pub elements: Vec<Object>,
}

impl Display for Array {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let elements = self
            .elements
            .iter()
            .map(|p| p.to_string())
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        write!(f, "[{elements}]")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HashTable {
    pub pairs: HashMap<Object, Object>,
}

impl Display for HashTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let pairs = self
            .pairs
            .iter()
            .map(|(key, value)| format!("{key}: {value}"))
            .reduce(|acc, cur| format!("{acc}, {cur}"))
            .unwrap_or(String::new());

        write!(f, "{{ {pairs} }}")
    }
}

impl Hash for HashTable {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let pairs: Vec<_> = self
            .pairs
            .iter()
            .map(|(key, value)| format!("{key} {value}"))
            .collect();

        pairs.hash(state);
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CompiledFunction {
    pub instructions: Instructions,
    pub locals_num: usize,
    pub parameters_num: usize,
}

impl Display for CompiledFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CompiledFunction[{}]", self.instructions)
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct Closure {
    pub func: CompiledFunction,
    pub free: Vec<Object>,
}

impl Display for Closure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Closure[{}]", self.func)
    }
}
