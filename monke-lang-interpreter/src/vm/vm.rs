use std::{collections::HashMap, usize};

use crate::{
    code::code::{read_u16, Instructions, OpCodeType},
    compiler::compiler::ByteCode,
    evaluator::types::{Array, Boolean, HashTable, Integer, Null, Object, Str},
    result::InterpreterResult,
};

const STACK_SIZE: usize = 2048;
const GLOBALS_SIZE: usize = 65536;

#[derive(Debug)]
pub struct Vm {
    constants: Vec<Object>,
    instructions: Instructions,
    stack: Vec<Object>,
    sp: usize,
    pub globals: Vec<Object>,
}

impl Vm {
    pub fn new(byte_code: ByteCode) -> Self {
        Vm {
            constants: byte_code.constants,
            instructions: byte_code.instructions,
            stack: vec![Object::Null(Null {}); STACK_SIZE],
            sp: 0,
            globals: vec![Object::Null(Null {}); GLOBALS_SIZE],
        }
    }

    pub fn new_with_global_store(byte_code: ByteCode, globals: Vec<Object>) -> Self {
        Vm {
            constants: byte_code.constants,
            instructions: byte_code.instructions,
            stack: vec![Object::Null(Null {}); STACK_SIZE],
            sp: 0,
            globals,
        }
    }

    pub fn stack_top(&self) -> Option<&Object> {
        self.stack.get(self.sp - 1)
    }

    pub fn run(&mut self) -> InterpreterResult<()> {
        let mut ip = 0;

        while ip < self.instructions.len() {
            let op: OpCodeType = (*self
                .instructions
                .get(ip)
                .ok_or(format!("couldn't parse byte code"))?)
            .try_into()?;

            match op {
                OpCodeType::Constant => {
                    let const_idx = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );
                    ip += 2;

                    self.push(
                        self.constants
                            .get(const_idx as usize)
                            .ok_or(format!("couldn't parse byte code"))?
                            .clone(),
                    )?;
                }
                op if op == OpCodeType::Add
                    || op == OpCodeType::Sub
                    || op == OpCodeType::Mul
                    || op == OpCodeType::Div =>
                {
                    self.execute_binary_operation(op)?;
                }
                OpCodeType::Pop => {
                    self.pop()?;
                }
                OpCodeType::True => {
                    self.push(Object::Boolean(Boolean { value: true }))?;
                }
                OpCodeType::False => {
                    self.push(Object::Boolean(Boolean { value: false }))?;
                }
                op if op == OpCodeType::GreaterThan
                    || op == OpCodeType::Equal
                    || op == OpCodeType::NotEqual =>
                {
                    self.execute_comparison(op)?;
                }
                OpCodeType::Bang => match self.pop()? {
                    Object::Boolean(bool) => {
                        self.push(Object::Boolean(Boolean { value: !bool.value }))?
                    }
                    Object::Null(_) => self.push(Object::Boolean(Boolean { value: true }))?,
                    _ => self.push(Object::Boolean(Boolean { value: false }))?,
                },
                OpCodeType::Minus => match self.pop()? {
                    Object::Integer(int) => {
                        self.push(Object::Integer(Integer { value: -int.value }))?
                    }
                    actual => Err(format!("unsupported type for negation, got {actual}"))?,
                },
                OpCodeType::Jump => {
                    let pos = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );

                    ip = (pos - 1) as usize;
                }
                OpCodeType::JumpNotTruthy => {
                    let pos = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );

                    ip += 2;
                    let condition = self.pop()?;

                    if !Self::is_truthy(condition) {
                        ip = (pos - 1) as usize;
                    }
                }
                OpCodeType::Null => self.push(Object::Null(Null {}))?,
                OpCodeType::SetGlobal => {
                    let pos = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );
                    ip += 2;

                    self.globals[pos as usize] = self.pop()?;
                }
                OpCodeType::GetGlobal => {
                    let pos = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );
                    ip += 2;

                    self.push(
                        self.globals
                            .get(pos as usize)
                            .ok_or(String::from("couldn't parse byte code"))?
                            .clone(),
                    )?;
                }
                OpCodeType::Array => {
                    let array_len = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );
                    ip += 2;

                    let array = self.build_array(self.sp - array_len as usize, self.sp)?;
                    self.push(array)?;
                }
                OpCodeType::Hash => {
                    let hash_len = read_u16(
                        self.instructions
                            .get(ip + 1..)
                            .ok_or(format!("couldn't parse byte code"))?,
                    );
                    ip += 2;

                    let hash = self.build_hash(hash_len as usize)?;
                    self.push(hash)?;
                }
                _ => todo!(),
            }

            ip += 1;
        }

        Ok(())
    }

    pub fn last_popped_stack_elem(&self) -> InterpreterResult<Object> {
        Ok(self
            .stack
            .get(self.sp)
            .ok_or(String::from(
                "couldn't pop from the stack, index is out of bounds",
            ))?
            .clone())
    }

    fn push(&mut self, object: Object) -> InterpreterResult<()> {
        if self.sp >= STACK_SIZE {
            return Err(String::from("stack overflow"));
        }

        self.stack[self.sp] = object;
        self.sp += 1;

        Ok(())
    }

    fn pop(&mut self) -> InterpreterResult<Object> {
        self.sp -= 1;

        Ok(self
            .stack
            .get(self.sp)
            .ok_or(String::from(
                "couldn't pop from the stack, index is out of bounds",
            ))?
            .clone())
    }

    fn execute_binary_operation(&mut self, op: OpCodeType) -> InterpreterResult<()> {
        let right = self.pop()?;
        let left = self.pop()?;

        match (left, right) {
            (Object::Integer(left_int), Object::Integer(right_int)) => match op {
                OpCodeType::Add => self.push(Object::Integer(Integer {
                    value: left_int.value + right_int.value,
                })),
                OpCodeType::Sub => self.push(Object::Integer(Integer {
                    value: left_int.value - right_int.value,
                })),
                OpCodeType::Mul => self.push(Object::Integer(Integer {
                    value: left_int.value * right_int.value,
                })),
                OpCodeType::Div => self.push(Object::Integer(Integer {
                    value: left_int.value / right_int.value,
                })),
                t => Err(format!(
                    "couldn't execute binary operation, wrong operation type - {t}"
                ))?,
            },
            (Object::String(left_str), Object::String(right_str)) => match op {
                OpCodeType::Add => self.push(Object::String(Str {
                    value: left_str.value + &right_str.value,
                })),
                t => Err(format!(
                    "couldn't execute binary operation, wrong operation type - {t}"
                ))?,
            },
            (obj1, obj2) => Err(format!(
                "couldn't execute binary operation: got \"{obj1}\" and \"{obj2}\""
            ))?,
        }
    }

    fn execute_comparison(&mut self, op: OpCodeType) -> InterpreterResult<()> {
        let right = self.pop()?;
        let left = self.pop()?;

        match (left, right) {
            (Object::Integer(int1), Object::Integer(int2)) => match op {
                OpCodeType::Equal => self.push(Object::Boolean(Boolean {
                    value: int1.value == int2.value,
                })),
                OpCodeType::NotEqual => self.push(Object::Boolean(Boolean {
                    value: int1.value != int2.value,
                })),
                OpCodeType::GreaterThan => self.push(Object::Boolean(Boolean {
                    value: int1.value > int2.value,
                })),
                op => Err(format!(
                    "couldn't compare two objects, got wrong operator {op}"
                )),
            },
            (Object::Boolean(bool1), Object::Boolean(bool2)) => match op {
                OpCodeType::Equal => self.push(Object::Boolean(Boolean {
                    value: bool1.value == bool2.value,
                })),
                OpCodeType::NotEqual => self.push(Object::Boolean(Boolean {
                    value: bool1.value != bool2.value,
                })),
                OpCodeType::GreaterThan => self.push(Object::Boolean(Boolean {
                    value: bool1.value > bool2.value,
                })),
                op => Err(format!(
                    "couldn't compare two objects, got wrong operator {op}"
                )),
            },
            (actual_left, actual_right) => Err(format!(
                "couldn't compare two objects, got {actual_left} and {actual_right}"
            )),
        }
    }

    fn is_truthy(condition: Object) -> bool {
        match condition {
            Object::Boolean(bool) => bool.value,
            Object::Null(_) => false,
            _ => true,
        }
    }

    fn build_array(&self, start_idx: usize, end_idx: usize) -> InterpreterResult<Object> {
        let elements = Vec::from(
            self.stack
                .get(start_idx..end_idx)
                .ok_or(String::from("couldn't build an array"))?,
        );

        Ok(Object::Array(Array { elements }))
    }

    fn build_hash(&self, hash_len: usize) -> InterpreterResult<Object> {
        let start_idx = self.sp - hash_len;
        let pair_count = hash_len / 2;

        let mut pairs = HashMap::new();

        for idx in 0..pair_count {
            let key = self
                .stack
                .get(start_idx + 2 * idx)
                .ok_or(String::from("couldn't build a hash"))?;
            let value = self
                .stack
                .get(start_idx + 2 * idx + 1)
                .ok_or(String::from("couldn't build a hash"))?;

            pairs.insert(key.clone(), value.clone());
        }

        Ok(Object::HashTable(HashTable { pairs }))
    }
}

#[cfg(test)]
mod tests {
    use core::panic;
    use std::collections::HashMap;

    use crate::{
        compiler::compiler::Compiler, evaluator::types::Object, lexer::lexer::Lexer,
        parser::parser::Parser,
    };

    use super::*;

    struct TestCase {
        input: String,
        expected: TestCaseResult,
    }

    #[derive(Debug)]
    enum TestCaseResult {
        Integer(i64),
        Boolean(bool),
        String(String),
        Array(Vec<TestCaseResult>),
        Hash(HashMap<Object, TestCaseResult>),
        Null,
    }

    impl TestCaseResult {
        fn test(&self, obj: &Object) {
            match (self, obj) {
                (TestCaseResult::Integer(expected), Object::Integer(actual_int)) => {
                    assert_eq!(expected, &actual_int.value)
                }
                (TestCaseResult::Boolean(expected), Object::Boolean(actual_bool)) => {
                    assert_eq!(expected, &actual_bool.value)
                }
                (TestCaseResult::String(expected), Object::String(actual_string)) => {
                    assert_eq!(expected, &actual_string.value)
                }
                (TestCaseResult::Array(expected), Object::Array(actual_array)) => {
                    assert_eq!(expected.len(), actual_array.elements.len());

                    for (idx, el) in actual_array.elements.iter().enumerate() {
                        expected[idx].test(el);
                    }
                }
                (TestCaseResult::Hash(expected), Object::HashTable(actual_hash)) => {
                    assert_eq!(expected.len(), actual_hash.pairs.len());

                    for (exp_key, exp_value) in expected {
                        let actual_value = actual_hash.pairs.get(exp_key);
                        assert!(actual_value.is_some());

                        let actual_value = actual_value.unwrap();
                        exp_value.test(actual_value);
                    }
                }
                (TestCaseResult::Null, Object::Null(_)) => {}
                (t1, t2) => panic!("can't compare {t1:?} and {t2:?}"),
            }
        }
    }

    fn run_vm_tests(cases: Vec<TestCase>) {
        for case in cases {
            let lexer = Lexer::new(case.input.clone());
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                panic!("{err}");
            }

            let program = program.unwrap();

            let mut compiler = Compiler::new();

            if let Err(err) = compiler.compile(program) {
                panic!("{err}");
            }

            let byte_code = compiler.byte_code();
            let mut vm = Vm::new(byte_code);

            if let Err(err) = vm.run() {
                panic!("{err}");
            }

            let stack_elem = vm.last_popped_stack_elem();
            assert!(stack_elem.is_ok());
            let stack_elem = stack_elem.unwrap();

            case.expected.test(&stack_elem);
        }
    }

    #[test]
    fn integer_arithmetic_test() {
        let expected = vec![
            TestCase {
                input: String::from("1"),
                expected: TestCaseResult::Integer(1),
            },
            TestCase {
                input: String::from("2"),
                expected: TestCaseResult::Integer(2),
            },
            TestCase {
                input: String::from("1 + 2"),
                // todo: fix later
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("1 - 2"),
                expected: TestCaseResult::Integer(-1),
            },
            TestCase {
                input: String::from("1 * 2"),
                expected: TestCaseResult::Integer(2),
            },
            TestCase {
                input: String::from("4 / 2"),
                expected: TestCaseResult::Integer(2),
            },
            TestCase {
                input: String::from("50 / 2 * 2 + 10 - 5"),
                expected: TestCaseResult::Integer(55),
            },
            TestCase {
                input: String::from("5 + 5 + 5 + 5 - 10"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("2 * 2 * 2 * 2 * 2"),
                expected: TestCaseResult::Integer(32),
            },
            TestCase {
                input: String::from("5 * 2 + 10"),
                expected: TestCaseResult::Integer(20),
            },
            TestCase {
                input: String::from("5 + 2 * 10"),
                expected: TestCaseResult::Integer(25),
            },
            TestCase {
                input: String::from("5 * (2 + 10)"),
                expected: TestCaseResult::Integer(60),
            },
            TestCase {
                input: String::from("-5"),
                expected: TestCaseResult::Integer(-5),
            },
            TestCase {
                input: String::from("-10"),
                expected: TestCaseResult::Integer(-10),
            },
            TestCase {
                input: String::from("-50 + 100 + -50"),
                expected: TestCaseResult::Integer(0),
            },
            TestCase {
                input: String::from("(5 + 10 * 2 + 15 / 3) * 2 + -10"),
                expected: TestCaseResult::Integer(50),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn boolean_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from("true"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("false"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 < 2"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("1 > 2"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 < 1"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 > 1"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 == 1"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("1 != 1"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 == 2"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("1 != 2"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("true == true"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("false == false"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("true == false"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("true != false"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("false != true"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("(1 < 2) == true"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("(1 < 2) == false"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("(1 > 2) == true"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("(1 > 2) == false"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("!true"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("!false"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("!5"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("!!true"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("!!false"),
                expected: TestCaseResult::Boolean(false),
            },
            TestCase {
                input: String::from("!!5"),
                expected: TestCaseResult::Boolean(true),
            },
            TestCase {
                input: String::from("!(if (false) { 5; })"),
                expected: TestCaseResult::Boolean(true),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn conditionals_test() {
        let expected = vec![
            TestCase {
                input: String::from("if (true) { 10 }"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("if (true) { 10 } else { 20 }"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("if (false) { 10 } else { 20 } "),
                expected: TestCaseResult::Integer(20),
            },
            TestCase {
                input: String::from("if (1) { 10 }"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("if (1 < 2) { 10 }"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("if (1 < 2) { 10 } else { 20 }"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("if (1 > 2) { 10 } else { 20 }"),
                expected: TestCaseResult::Integer(20),
            },
            TestCase {
                input: String::from("if (1 > 2) { 10 }"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("if (false) { 10 }"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("if ((if (false) { 10 })) { 10 } else { 20 }"),
                expected: TestCaseResult::Integer(20),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn global_let_statement_test() {
        let expected = vec![
            TestCase {
                input: String::from("let one = 1; one"),
                expected: TestCaseResult::Integer(1),
            },
            TestCase {
                input: String::from("let one = 1; let two = 2; one + two"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("let one = 1; let two = one + one; one + two"),
                expected: TestCaseResult::Integer(3),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn string_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from(r#""monkey""#),
                expected: TestCaseResult::String(String::from("monkey")),
            },
            TestCase {
                input: String::from(r#""mon" + "key""#),
                expected: TestCaseResult::String(String::from("monkey")),
            },
            TestCase {
                input: String::from(r#""mon" + "key" + "banana""#),
                expected: TestCaseResult::String(String::from("monkeybanana")),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn array_literl_test() {
        let expected = vec![
            TestCase {
                input: String::from("[]"),
                expected: TestCaseResult::Array(vec![]),
            },
            TestCase {
                input: String::from("[1, 2, 3]"),
                expected: TestCaseResult::Array(vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                ]),
            },
            TestCase {
                input: String::from("[1 + 2, 3 * 4, 5 + 6]"),
                expected: TestCaseResult::Array(vec![
                    TestCaseResult::Integer(3),
                    TestCaseResult::Integer(12),
                    TestCaseResult::Integer(11),
                ]),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn hash_literal_test() {
        let expected = vec![
            TestCase {
                input: String::from("{}"),
                expected: TestCaseResult::Hash(HashMap::new()),
            },
            TestCase {
                input: String::from("{ 1: 2, 2: 3 }"),
                expected: TestCaseResult::Hash(HashMap::from([
                    (
                        Object::Integer(Integer { value: 1 }),
                        TestCaseResult::Integer(2),
                    ),
                    (
                        Object::Integer(Integer { value: 2 }),
                        TestCaseResult::Integer(3),
                    ),
                ])),
            },
            TestCase {
                input: String::from("{1 + 1: 2 * 2, 3 + 3: 4 * 4}"),
                expected: TestCaseResult::Hash(HashMap::from([
                    (
                        Object::Integer(Integer { value: 2 }),
                        TestCaseResult::Integer(4),
                    ),
                    (
                        Object::Integer(Integer { value: 6 }),
                        TestCaseResult::Integer(16),
                    ),
                ])),
            },
        ];

        run_vm_tests(expected);
    }
}
