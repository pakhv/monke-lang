use crate::{
    result::MonkeyResult,
    types::{Array, BuiltinFunction, Integer, Null, Object},
};

const LEN_BUILTIN: &str = "len";
const FIRST_BUILTIN: &str = "first";
const LAST_BUILTIN: &str = "last";
const REST_BUILTIN: &str = "rest";
const PUSH_BUILTIN: &str = "push";
const PUTS_BUILTIN: &str = "puts";

pub const BUILTINS: [&str; 6] = [
    LEN_BUILTIN,
    PUTS_BUILTIN,
    FIRST_BUILTIN,
    LAST_BUILTIN,
    REST_BUILTIN,
    PUSH_BUILTIN,
];

pub fn get_builtin_function(fn_name: &str) -> Option<Object> {
    match fn_name {
        LEN_BUILTIN => Some(Object::Builtin(BuiltinFunction(len_builtin))),
        FIRST_BUILTIN => Some(Object::Builtin(BuiltinFunction(first_builtin))),
        LAST_BUILTIN => Some(Object::Builtin(BuiltinFunction(last_builtin))),
        REST_BUILTIN => Some(Object::Builtin(BuiltinFunction(rest_builtin))),
        PUSH_BUILTIN => Some(Object::Builtin(BuiltinFunction(push_builtin))),
        PUTS_BUILTIN => Some(Object::Builtin(BuiltinFunction(puts_builtin))),
        _ => None,
    }
}

fn len_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
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
            "argument to len function is not supported, String expected, but got \"{actual}\""
        )),
    }
}

fn first_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
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
            "argument to first function is not supported, Array expected, but got \"{actual}\""
        )),
    }
}

fn last_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
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
            "argument to last function is not supported, Array expected, but got \"{actual}\""
        )),
    }
}

fn rest_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
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
            "argument to rest function is not supported, Array expected, but got \"{actual}\""
        )),
    }
}

fn push_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
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
            "argument to push function is not supported, Array expected, but got \"{actual}\""
        )),
    }
}

fn puts_builtin(args: Vec<Object>) -> MonkeyResult<Object> {
    for arg in args {
        println!("{arg}");
    }

    Ok(Object::Null(Null {}))
}
