use std::{array::from_fn, usize};

use crate::{
    code::code::{read_u16, Instructions, OpCodeType},
    compiler::compiler::ByteCode,
    evaluator::types::{Integer, Null, Object},
    result::InterpreterResult,
};

const STACK_SIZE: usize = 2048;

#[derive(Debug)]
pub struct Vm {
    constants: Vec<Object>,
    instructions: Instructions,

    stack: [Object; STACK_SIZE],
    sp: usize,
}

impl Vm {
    pub fn new(byte_code: ByteCode) -> Self {
        Vm {
            constants: byte_code.constants,
            instructions: byte_code.instructions,
            stack: from_fn(|_| Object::Null(Null {})),
            sp: 0,
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
                OpCodeType::Add => {
                    let right = self.pop()?;
                    let left = self.pop()?;

                    match (left, right) {
                        (Object::Integer(left_int), Object::Integer(right_int)) => {
                            self.push(Object::Integer(Integer {
                                value: left_int.value + right_int.value,
                            }))?
                        }
                        (obj1, obj2) => {
                            Err(format!("couldn't add two objects: got {obj1} and {obj2}"))?
                        }
                    }
                }
                _ => todo!(),
            }

            ip += 1;
        }

        Ok(())
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
}

#[cfg(test)]
mod tests {
    use crate::{
        compiler::compiler::Compiler, evaluator::types::Object, lexer::lexer::Lexer,
        parser::parser::Parser,
    };

    use super::*;

    struct TestCase<T>
    where
        T: ConstTest,
    {
        input: String,
        expected: T,
    }

    impl ConstTest for i64 {
        fn test(&self, actual: &Object) {
            match actual {
                Object::Integer(int) => assert_eq!(int.value, *self),
                not_int => panic!("integer expected, got {not_int}"),
            }
        }
    }

    trait ConstTest {
        fn test(&self, actual: &Object);
    }

    fn run_vm_tests<T>(cases: Vec<TestCase<T>>)
    where
        T: ConstTest,
    {
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

            let stack_elem = vm.stack_top();
            assert!(stack_elem.is_some());
            let stack_elem = stack_elem.unwrap();

            case.expected.test(stack_elem);
        }
    }

    #[test]
    fn integer_arithmetic_test() {
        let expected = vec![
            TestCase {
                input: String::from("1"),
                expected: 1,
            },
            TestCase {
                input: String::from("2"),
                expected: 2,
            },
            TestCase {
                input: String::from("1 + 2"),
                // todo: fix later
                expected: 3,
            },
        ];

        run_vm_tests(expected);
    }
}
