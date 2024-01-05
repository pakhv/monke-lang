use std::{error::Error, fmt::Display};

#[derive(Debug)]
pub struct InterpreterError {
    pub message: String,
}

impl InterpreterError {
    pub fn new(message: String) -> Self {
        InterpreterError { message }
    }
}

impl Error for InterpreterError {}
impl Display for InterpreterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}
