use std::result;

pub type InterpreterError<T> = result::Result<T, String>;
