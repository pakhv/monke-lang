use core::panic;
use std::{collections::HashMap, usize};

use crate::{
    builtins::{get_builtin_function, BUILTINS}, code::code::{read_u16, Instructions, OpCodeType}, compiler::compiler::ByteCode, result::MonkeyResult, types::{Array, Boolean, BuiltinFunction, Closure, CompiledFunction, HashTable, Integer, Null, Object, Str}
};

const STACK_SIZE: usize = 2048;
const GLOBALS_SIZE: usize = 65536;
const MAX_FRAMES: usize = 1024;

#[derive(Debug, Clone)]
struct Frame {
    cl: Closure,
    ip: isize,
    base_pointer: usize
}

impl Frame {
    fn new(func: Closure, base_pointer: usize) -> Self {
        Frame { ip: -1, cl: func, base_pointer }
    }

    fn instructions(&self) -> &Instructions {
        &self.cl.func.instructions
    }
}

#[derive(Debug)]
pub struct Vm {
    constants: Vec<Object>,
    stack: Vec<Object>,
    sp: usize,
    pub globals: Vec<Object>,
    frames: Vec<Option<Frame>>,
    frames_index: usize
}

impl Vm {
    pub fn new(byte_code: ByteCode) -> Self {
        let main_fn = CompiledFunction { instructions: byte_code.instructions, locals_num: 0, parameters_num: 0 };
        let main_closure = Closure { func: main_fn, free: vec![] };

        let mut frames = vec![None; MAX_FRAMES];
        frames[0] = Some(Frame::new(main_closure, 0));

        Vm {
            constants: byte_code.constants,
            frames,
            frames_index: 1,
            stack: vec![Object::Null(Null {}); STACK_SIZE],
            sp: 0,
            globals: vec![Object::Null(Null {}); GLOBALS_SIZE],
        }
    }

    pub fn new_with_global_store(byte_code: ByteCode, globals: Vec<Object>) -> Self {
        let main_fn = CompiledFunction { instructions: byte_code.instructions, locals_num: 0, parameters_num: 0 };
        let main_closure = Closure { func: main_fn, free: vec![] };

        let mut frames = vec![None; MAX_FRAMES];
        frames[0] = Some(Frame::new(main_closure, 0));

        Vm {
            constants: byte_code.constants,
            frames,
            frames_index: 1,
            stack: vec![Object::Null(Null {}); STACK_SIZE],
            sp: 0,
            globals,
        }
    }

    pub fn stack_top(&self) -> Option<&Object> {
        self.stack.get(self.sp - 1)
    }

    pub fn run(&mut self) -> MonkeyResult<()> {
        let mut ip;

        while self.current_frame().is_ok_and(|f| f.instructions().len() > 0 && f.ip < (f.instructions().len() - 1) as isize) {
            self.current_frame()?.ip += 1;
            ip = self.current_frame()?.ip as usize;
            let ins = self.current_frame()?.instructions();

            let op: OpCodeType = (ins
                .get(ip)
                .ok_or(format!("couldn't parse byte code"))?)
                .clone()
                .try_into()?;

            match op {
                OpCodeType::Constant => {
                    let const_idx = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );
                    self.current_frame()?.ip += 2;

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
                    let pos = read_u16( ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );

                    self.current_frame()?.ip = (pos - 1) as isize;
                }
                OpCodeType::JumpNotTruthy => {
                    let pos = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );

                    self.current_frame()?.ip += 2;
                    let condition = self.pop()?;

                    if !Self::is_truthy(condition) {
                        self.current_frame()?.ip = (pos - 1) as isize;
                    }
                }
                OpCodeType::Null => self.push(Object::Null(Null {}))?,
                OpCodeType::SetGlobal => {
                    let pos = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );
                    self.current_frame()?.ip += 2;

                    self.globals[pos as usize] = self.pop()?;
                }
                OpCodeType::GetGlobal => {
                    let pos = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );
                    self.current_frame()?.ip += 2;

                    self.push(
                        self.globals
                            .get(pos as usize)
                            .ok_or(String::from("couldn't parse byte code"))?
                            .clone(),
                    )?;
                }
                OpCodeType::Array => {
                    let array_len = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );
                    self.current_frame()?.ip += 2;

                    let array = self.build_array(self.sp - array_len as usize, self.sp)?;
                    self.sp = self.sp - array_len as usize;

                    self.push(array)?;
                }
                OpCodeType::Hash => {
                    let hash_len = read_u16(ins
                        .get(ip + 1..)
                        .ok_or(format!("couldn't parse byte code"))?,
                    );
                    self.current_frame()?.ip += 2;

                    let hash = self.build_hash(hash_len as usize)?;
                    self.sp = self.sp - hash_len as usize;

                    self.push(hash)?;
                }
                OpCodeType::Index => {
                    let index = self.pop()?;
                    let left = self.pop()?;

                    self.execute_index_expression(left, index)?;
                }
                OpCodeType::ReturnValue => {
                    let return_value = self.pop()?;
                    let frame = self.pop_frame()?;

                    self.sp = frame.base_pointer - 1;
                    self.push(return_value)?;
                }
                OpCodeType::Return => {
                    let frame = self.pop_frame()?;
                    self.sp = frame.base_pointer - 1;

                    self.push(Object::Null(Null { }))?;
                }
                OpCodeType::SetLocal => {
                    let local_index = *ins.get(ip + 1).ok_or(format!("couldn't get local index"))?;
                    self.current_frame()?.ip += 1;

                    let base_pointer = self.current_frame()?.base_pointer;
                    self.stack[base_pointer + local_index as usize] = self.pop()?;
                }
                OpCodeType::GetLocal => {
                    let local_index = *ins.get(ip + 1).ok_or(format!("couldn't get local index"))?;
                    self.current_frame()?.ip += 1;

                    let base_pointer = self.current_frame()?.base_pointer;
                    let local = self.stack.get(base_pointer + local_index as usize).ok_or(format!("couldn't get local variable"))?.clone();
                    self.push(local)?;
                }
                OpCodeType::GetBuiltin => {
                    let builtin_index = *ins.get(ip + 1).ok_or(format!("couldn't get builtin index"))?;
                    self.current_frame()?.ip += 1;

                    let builtin_name = BUILTINS.get(builtin_index as usize).ok_or(format!("couldn't get builtin function name"))?;
                    let builtin = get_builtin_function(builtin_name).ok_or(format!("couldn't get builtin function"))?;
                    self.push(builtin)?;
                }
                OpCodeType::Call => {
                    let args_num = *ins.get(ip + 1).ok_or(format!("couldn't get args number"))?;
                    self.current_frame()?.ip += 1;

                    self.execute_call(args_num as usize)?;
                }
                OpCodeType::Closure => {
                    let const_index = read_u16(ins.get(ip + 1..).ok_or(format!("couldn't get constant index"))?);
                    let free_num = *ins.get(ip + 3).ok_or(format!("couldn't get free vars number"))?;

                    self.current_frame()?.ip += 3;
                    self.push_closure(const_index as usize, free_num as usize)?;
                }
                OpCodeType::GetFree => {
                    let free_idx = *ins.get(ip + 1).ok_or(format!("couldn't get free index"))?;
                    self.current_frame()?.ip += 1;

                    let current_closure = self.current_frame()?.cl.clone();
                    self.push(current_closure.free.get(free_idx as usize).ok_or(format!("couldn't free variable"))?.clone())?;
                }
                OpCodeType::CurrentClosure => {
                    let current_closure = self.current_frame()?.cl.clone();
                    self.push(Object::Closure(current_closure))?;
                }
                _ => todo!(),
            }
        }

        Ok(())
    }

    pub fn last_popped_stack_elem(&self) -> MonkeyResult<Object> {
        Ok(self
            .stack
            .get(self.sp)
            .ok_or(String::from(
                "couldn't pop from the stack, index is out of bounds",
            ))?
            .clone())
    }

    fn push(&mut self, object: Object) -> MonkeyResult<()> {
        if self.sp >= STACK_SIZE {
            return Err(String::from("stack overflow"));
        }

        self.stack[self.sp] = object;
        self.sp += 1;

        Ok(())
    }

    fn pop(&mut self) -> MonkeyResult<Object> {
        self.sp -= 1;

        Ok(self
            .stack
            .get(self.sp)
            .ok_or(format!(
                "couldn't pop from the stack, index is out of bounds",
            ))?
            .clone())
    }

    fn execute_binary_operation(&mut self, op: OpCodeType) -> MonkeyResult<()> {
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

    fn execute_comparison(&mut self, op: OpCodeType) -> MonkeyResult<()> {
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

    fn build_array(&self, start_idx: usize, end_idx: usize) -> MonkeyResult<Object> {
        let elements = Vec::from(
            self.stack
                .get(start_idx..end_idx)
                .ok_or(String::from("couldn't build an array"))?,
        );

        Ok(Object::Array(Array { elements }))
    }

    fn build_hash(&self, hash_len: usize) -> MonkeyResult<Object> {
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

    fn execute_index_expression(&mut self, left: Object, index: Object) -> MonkeyResult<()> {
        match (left, &index) {
            (Object::Array(array), Object::Integer(idx)) => {
                match array.elements.get(idx.value as usize) {
                    Some(el) => self.push(el.clone()),
                    None => self.push(Object::Null(Null {  }))
                }
            }
            (Object::HashTable(hash), Object::Integer(_)) 
                | (Object::HashTable(hash), Object::Boolean(_)) 
                | (Object::HashTable(hash), Object::String(_)) => {
                    match hash.pairs.get(&index) {
                        Some(el) => self.push(el.clone()),
                        None => self.push(Object::Null(Null { }))
                    }
                }
            (actual_left, actual_idx) => panic!("couldn't execute index expression, array with int index or hash table expected, but got type \"{actual_left}\" and idx \"{actual_idx}\""),
        }
    }

    fn current_frame(&mut self) -> MonkeyResult<&mut Frame> {
        self.frames
            .get_mut(self.frames_index - 1)
            .ok_or(String::from("couldn't get current frame"))?
            .as_mut()
            .ok_or(format!("couldn't get current frame"))
    }

    fn push_frame(&mut self, frame: Frame) {
        self.frames[self.frames_index] = Some(frame);
        self.frames_index +=1;
    }

    fn pop_frame(&mut self) -> MonkeyResult<Frame> {
        self.frames_index -= 1;
        self.frames
            .get(self.frames_index)
            .ok_or(format!("couldn't pop frame, frames stack is empty"))?
            .clone()
            .ok_or(format!("couldn't pop frame, frames stack is empty"))
    }

    fn execute_call(&mut self, args_num: usize) -> MonkeyResult<()> {
        let callee = self.stack.get(self.sp - 1 - args_num).ok_or(format!("couldn't get callee, while executing call"))?.clone();

        match callee {
            Object::Closure(closure) => self.call_closure(closure, args_num),
            Object::Builtin(func) => self.call_builtin(func, args_num),
            actual => Err(format!("closure or builtin function expected, but got \"{actual:?}\"")),
        }
    }

    fn call_closure(&mut self, closure: Closure, args_num: usize) -> MonkeyResult<()> {
        if args_num != closure.func.parameters_num {
            return Err(format!("wrong number of arguments: want={}, got={}", closure.func.parameters_num, args_num));
        }
        let frame = Frame::new(closure.clone(), self.sp - args_num);

        let base_pointer = frame.base_pointer;
        let locals_num = closure.func.locals_num;

        self.push_frame(frame);
        self.sp = base_pointer + locals_num;

        Ok(())
    }

    fn call_builtin(&mut self, builtin: BuiltinFunction, args_num: usize) -> MonkeyResult<()> {
        let args = self.stack.get(self.sp - args_num..self.sp).ok_or(format!("couldn't get args while calling builtin"))?;
        let result = (builtin.0)(args.to_vec())?;
        self.sp = self.sp - args_num - 1;

        self.push(result)?;

        Ok(())
    }

    fn push_closure(&mut self, const_index: usize, free_num: usize) -> MonkeyResult<()> {
        let constant = self.constants.get(const_index).ok_or(format!("couldn't get constant, while pushing closure"))?.clone();

        match constant {
            Object::CompiledFunction(compiled_fn) => { 
                let free = self.stack.get(self.sp - free_num..self.sp).ok_or(format!("couldn't get free vars while, pushing closure"))?.iter().cloned().collect::<Vec<_>>();
                self.push(Object::Closure(Closure { func: compiled_fn, free })) 
            },
            actual => Err(format!("couldn't push closure, compiled function expected, but got \"{actual}\""))
        }
    }
}

#[cfg(test)]
mod tests {
    use core::panic;
    use std::collections::HashMap;

    use crate::{
        compiler::compiler::Compiler, lexer::lexer::Lexer,
        parser::parser::Parser, types::Object,
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
        Error(String),
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

        fn test_err(&self, actual_err: String) {
            match self {
                TestCaseResult::Error(expected_err) => assert_eq!(expected_err, &actual_err),
                t1 => panic!("expected \"{t1:?}\" but got error: \"{actual_err}\""),
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
            assert!(byte_code.is_ok());

            let byte_code = byte_code.unwrap();

            for (idx, constant) in byte_code.constants.iter().enumerate() {
                println!("CONSTANT {idx} {constant}");

                match constant {
                    Object::Integer(int) => println!("Value: {}", int.value),
                    Object::CompiledFunction(compiled_func) => println!("Instructions: {}", compiled_func.instructions),
                    _ => ()
                }
            }

            let mut vm = Vm::new(byte_code);

            if let Err(err) = vm.run() {
                case.expected.test_err(err);
                continue;
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

    #[test]
    fn index_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from("[1, 2, 3][1]"),
                expected: TestCaseResult::Integer(2),
            },
            TestCase {
                input: String::from("[1, 2, 3][0 + 2]"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("[[1, 1, 1]][0][0]"),
                expected: TestCaseResult::Integer(1),
            },
            TestCase {
                input: String::from("[][0]"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("[1, 2, 3][99]"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("[1][-1]"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("{1: 1, 2: 2}[1]"),
                expected: TestCaseResult::Integer(1),
            },
            TestCase {
                input: String::from("{1: 1, 2: 2}[2]"),
                expected: TestCaseResult::Integer(2),
            },
            TestCase {
                input: String::from("{1: 1}[0]"),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("{}[0]"),
                expected: TestCaseResult::Null,
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn calling_functions_without_arguments() {
        let expected = vec![
            TestCase {
                input: String::from("
let fivePlusTen = fn() { 5 + 10; };
fivePlusTen();
"),
                expected: TestCaseResult::Integer(15),
            },
            TestCase {
                input: String::from("
let one = fn() { 1; };
let two = fn() { 2; };
one() + two()
"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("
let a = fn() { 1 };
let b = fn() { a() + 1 };
let c = fn() { b() + 1 };
c();
"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("
let earlyExit = fn() { return 99; 100; };
earlyExit();"
),
                expected: TestCaseResult::Integer(99),
            },
            TestCase {
                input: String::from("
let earlyExit = fn() { return 99; return 100; };
earlyExit();"
),
                expected: TestCaseResult::Integer(99),
            },
            TestCase {
                input: String::from("
let noReturn = fn() { };
noReturn();"
),
                expected: TestCaseResult::Null,
            },
            TestCase {
                input: String::from("
let noReturn = fn() { };
let noReturnTwo = fn() { noReturn(); };
noReturn();
noReturnTwo();"
),
                expected: TestCaseResult::Null
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn first_class_function_test() {
        let expected = vec![
            TestCase {
                input: String::from("
let returnsOne = fn() { 1; };
let returnsOneReturner = fn() { returnsOne; };
returnsOneReturner()();
"),
                expected: TestCaseResult::Integer(1),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn calling_functions_with_bindings_test() {
        let expected = vec![
            TestCase {
                input: String::from("
let one = fn() { let one = 1; one };
one();
"),
                expected: TestCaseResult::Integer(1),
            },
            TestCase {
                input: String::from("
let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
oneAndTwo();
"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("
let oneAndTwo = fn() { let one = 1; let two = 2; one + two; };
let threeAndFour = fn() { let three = 3; let four = 4; three + four; };
oneAndTwo() + threeAndFour();
"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("
let firstFoobar = fn() { let foobar = 50; foobar; };
let secondFoobar = fn() { let foobar = 100; foobar; };
firstFoobar() + secondFoobar();
"),
                expected: TestCaseResult::Integer(150),
            },
            TestCase {
                input: String::from("
let globalSeed = 50;
let minusOne = fn() {
let num = 1;
globalSeed - num;
}
let minusTwo = fn() {
let num = 2;
globalSeed - num;
}
minusOne() + minusTwo();
"),
                expected: TestCaseResult::Integer(97),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn first_class_functions_test() {
        let expected = vec![
            TestCase {
                input: String::from("
let returnsOneReturner = fn() {
let returnsOne = fn() { 1; };
returnsOne;
};
returnsOneReturner()();
"),
                expected: TestCaseResult::Integer(1),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn calling_functions_with_arguments_and_bindings_test() {
        let expected = vec![
            TestCase {
                input: String::from("
let identity = fn(a) { a; };
identity(4);
"),
                expected: TestCaseResult::Integer(4),
            },
            TestCase {
                input: String::from("
let sum = fn(a, b) { a + b; };
sum(1, 2);
"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("
let sum = fn(a, b) {
let c = a + b;
c;
};
sum(1, 2);
"),
                expected: TestCaseResult::Integer(3),
            },
            TestCase {
                input: String::from("
let sum = fn(a, b) {
let c = a + b;
c;
};
sum(1, 2) + sum(3, 4);
"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("
let sum = fn(a, b) {
let c = a + b;
c;
};
let outer = fn() {
sum(1, 2) + sum(3, 4);
};
outer();
"),
                expected: TestCaseResult::Integer(10),
            },
            TestCase {
                input: String::from("
let globalNum = 10;
let sum = fn(a, b) {
let c = a + b;
c + globalNum;
};
let outer = fn() {
sum(1, 2) + sum(3, 4) + globalNum;
};
outer() + globalNum;
"),
                expected: TestCaseResult::Integer(50),
            },
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn calling_functions_with_wrong_arguments_test() {
        let expected = vec![
            TestCase { input: String::from("fn() { 1; }(1);"), expected: TestCaseResult::Error(String::from("wrong number of arguments: want=0, got=1"))},
            TestCase { input: String::from("fn(a) { a; }();"), expected: TestCaseResult::Error(String::from("wrong number of arguments: want=1, got=0"))},
            TestCase { input: String::from("fn(a, b) { a + b; }(1);"), expected: TestCaseResult::Error(String::from("wrong number of arguments: want=2, got=1"))}
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn builtin_functions_test() {
        let expected = vec![
            TestCase { input: String::from(r#"len("")"#), expected: TestCaseResult::Integer(0), },
            TestCase { input: String::from(r#"len("four")"#), expected: TestCaseResult::Integer(4) },
            TestCase { input: String::from(r#"len("hello world")"#), expected: TestCaseResult::Integer(11) },
            TestCase { input: String::from(r#"len(1)"#), expected: TestCaseResult::Error(String::from("argument to len function is not supported, String expected, but got \"1\"")) }, 
            TestCase { input: String::from(r#"len("one", "two")"#), expected: TestCaseResult::Error(String::from("wrong number of arguments for len function, 1 argument expected, but got 2")) }, 
            TestCase { input: String::from(r#"len([])"#), expected: TestCaseResult::Integer(0)},
            TestCase { input: String::from(r#"puts("hello", "world!")"#), expected: TestCaseResult::Null},
            TestCase { input: String::from(r#"first([1, 2, 3])"#), expected: TestCaseResult::Integer(1)},
            TestCase { input: String::from(r#"first([])"#), expected: TestCaseResult::Null},
            TestCase { input: String::from(r#"first(1)"#), expected: TestCaseResult::Error(String::from("argument to first function is not supported, Array expected, but got \"1\"")) }, 
            TestCase { input: String::from(r#"last([1, 2, 3])"#), expected: TestCaseResult::Integer(3)},
            TestCase { input: String::from(r#"last([])"#), expected: TestCaseResult::Null},
            TestCase { input: String::from(r#"last(1)"#), expected: TestCaseResult::Error(String::from("argument to last function is not supported, Array expected, but got \"1\"")) }, 
            TestCase { input: String::from(r#"rest([1, 2, 3])"#), expected: TestCaseResult::Array(vec![ TestCaseResult::Integer(2), TestCaseResult::Integer(3)])},
            TestCase { input: String::from(r#"rest([])"#), expected: TestCaseResult::Null},
            TestCase { input: String::from(r#"push([], 1)"#), expected: TestCaseResult::Array(vec![TestCaseResult::Integer(1)])},
            TestCase { input: String::from(r#"push(1, 1)"#), expected: TestCaseResult::Error(String::from("argument to push function is not supported, Array expected, but got \"1\"")) }, 
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn closures_test() {
        let expected = vec![TestCase {
                input: String::from("
let newClosure = fn(a) {
    fn() { a; };
};
let closure = newClosure(99);
closure();
"
            ),
                expected: TestCaseResult::Integer(99),
            },
            TestCase {
                input: String::from("
let newAdder = fn(a, b) {
    fn(c) { a + b + c };
};
let adder = newAdder(1, 2);
adder(8);
"
            ),
                expected: TestCaseResult::Integer(11),
            },
            TestCase {
                input: String::from("
let newAdder = fn(a, b) {
    let c = a + b;
    fn(d) { c + d };
};
let adder = newAdder(1, 2);
adder(8);
"
            ),
                expected: TestCaseResult::Integer(11),
            },
            TestCase {
                input: String::from("
let newAdderOuter = fn(a, b) {
    let c = a + b;
    fn(d) {
        let e = d + c;
        fn(f) { e + f; };
    };
};
let newAdderInner = newAdderOuter(1, 2)
let adder = newAdderInner(3);
adder(8);
"
            ),
                expected: TestCaseResult::Integer(14),
            },
            TestCase {
                input: String::from("
let a = 1;
let newAdderOuter = fn(b) {
    fn(c) {
        fn(d) { a + b + c + d };
    };
};
let newAdderInner = newAdderOuter(2)
let adder = newAdderInner(3);
adder(8);
"
            ),
                expected: TestCaseResult::Integer(14),
            },
            TestCase {
                input: String::from("
let newClosure = fn(a, b) {
    let one = fn() { a; };
    let two = fn() { b; };
    fn() { one() + two(); };
};
let closure = newClosure(9, 90);
closure();
"
            ),
                expected: TestCaseResult::Integer(99),
            }
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn recursive_functions_test() {
        let expected = vec![
            TestCase {
                input: String::from("
let countDown = fn(x) {
    if (x == 0) {
        return 0;
    } else {
        countDown(x - 1);
    }
};

countDown(1);
"),
                expected: TestCaseResult::Integer(0)
            },
            TestCase {
                input: String::from("
let countDown = fn(x) {
    if (x == 0) {
        return 0;
    } else {
        countDown(x - 1);
    }
};
let wrapper = fn() {
    countDown(1);
};
wrapper();
"),
                expected: TestCaseResult::Integer(0)
            },
            TestCase {
                input: String::from("
let wrapper = fn() {
    let countDown = fn(x) {
        if (x == 0) {
            return 0;
        } else {
            countDown(x - 1);
        }
    };
    countDown(1);
};
wrapper();
"),
                expected: TestCaseResult::Integer(0)
            }
        ];

        run_vm_tests(expected);
    }

    #[test]
    fn fibonacci_function_test() {
        let expected = vec![TestCase {
                input: String::from("
let fibonacci = fn(x) {
    if (x == 0) {
        return 0;
    } else {
        if (x == 1) {
            return 1;
        } else {
            fibonacci(x - 1) + fibonacci(x - 2);
        }
    }
};

fibonacci(15);
"
            ),
                expected: TestCaseResult::Integer(610),
            }
        ];

        run_vm_tests(expected);
    }
}
