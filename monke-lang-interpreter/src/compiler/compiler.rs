use std::{rc::Rc, usize};

use crate::{
    code::code::{make, Instructions, OpCodeType},
    evaluator::types::{Integer, Object, Str},
    lexer::token::Token,
    parser::ast::{Expression, Program, Statement},
    result::InterpreterResult,
};

use super::symbol_table::SymbolTable;

#[derive(Debug, Clone)]
struct EmittedInstruction {
    op_code: OpCodeType,
    position: usize,
}

#[derive(Debug)]
pub struct Compiler {
    pub instructions: Instructions,
    pub constants: Vec<Object>,
    last_instruction: Option<EmittedInstruction>,
    prev_instruction: Option<EmittedInstruction>,
    pub symbol_table: SymbolTable,
}

#[derive(Debug)]
pub struct ByteCode {
    pub instructions: Instructions,
    pub constants: Vec<Object>,
}

impl Compiler {
    const KEKL_VALUE: i32 = 9999;

    pub fn new() -> Self {
        Compiler {
            constants: vec![],
            instructions: Instructions(vec![]),
            last_instruction: None,
            prev_instruction: None,
            symbol_table: SymbolTable::new(),
        }
    }

    pub fn new_with_state(symbol_table: SymbolTable, constants: Vec<Object>) -> Self {
        Compiler {
            constants,
            instructions: Instructions(vec![]),
            last_instruction: None,
            prev_instruction: None,
            symbol_table,
        }
    }

    pub fn compile(&mut self, program: Program) -> InterpreterResult<()> {
        match program {
            Program::Statements(statements) => {
                for statement in statements {
                    self.compile(statement.into())?;
                }

                Ok(())
            }
            Program::Statement(statement) => match statement.as_ref() {
                Statement::Let(let_statement) => {
                    self.compile(Rc::clone(&let_statement.value).into())?;

                    let symbol = self.symbol_table.define(let_statement.name.to_string());
                    self.emit(OpCodeType::SetGlobal, vec![symbol.index as i32]);

                    Ok(())
                }
                Statement::Return(_) => todo!(),
                Statement::Expression(expression_statement) => {
                    self.compile(Rc::clone(&expression_statement.expression).into())?;
                    self.emit(OpCodeType::Pop, vec![]);

                    Ok(())
                }
                Statement::Block(block) => {
                    for statement in &block.statements {
                        self.compile(Rc::clone(statement).into())?;
                    }

                    Ok(())
                }
            },
            Program::Expression(expression) => match expression.as_ref() {
                Expression::Identifier(ident) => {
                    let value = self
                        .symbol_table
                        .resolve(&ident.to_string())
                        .ok_or(format!("couldn't resolve identifier value: \"{ident}\""))?;

                    self.emit(OpCodeType::GetGlobal, vec![value.index as i32]);

                    Ok(())
                }
                Expression::IntegerLiteral(int_expression) => {
                    let int = Object::Integer(Integer {
                        value: int_expression.value,
                    });
                    let operand = self.add_constant(int);
                    self.emit(OpCodeType::Constant, vec![operand as i32]);

                    Ok(())
                }
                Expression::StringLiteral(string) => {
                    let str = Object::String(Str {
                        value: string.to_string(),
                    });
                    let operand = self.add_constant(str);
                    self.emit(OpCodeType::Constant, vec![operand as i32]);

                    Ok(())
                }
                Expression::Prefix(prefix) => {
                    self.compile(Rc::clone(&prefix.right).into())?;

                    match &prefix.token {
                        Token::Bang => self.emit(OpCodeType::Bang, vec![]),
                        Token::Minus => self.emit(OpCodeType::Minus, vec![]),
                        actual => Err(format!("couldn't compile prefix expression, bang or minus operators expected, but got {actual}"))?,
                    };

                    Ok(())
                }
                Expression::Infix(infix_expression) => {
                    if infix_expression.token == Token::Lt {
                        self.compile(Rc::clone(&infix_expression.right).into())?;
                        self.compile(Rc::clone(&infix_expression.left).into())?;
                        self.emit(OpCodeType::GreaterThan, vec![]);

                        return Ok(());
                    }

                    self.compile(Rc::clone(&infix_expression.left).into())?;
                    self.compile(Rc::clone(&infix_expression.right).into())?;

                    match infix_expression.token {
                        Token::Plus => self.emit(OpCodeType::Add, vec![]),
                        Token::Minus => self.emit(OpCodeType::Sub, vec![]),
                        Token::Asterisk => self.emit(OpCodeType::Mul, vec![]),
                        Token::Slash => self.emit(OpCodeType::Div, vec![]),
                        Token::Gt => self.emit(OpCodeType::GreaterThan, vec![]),
                        Token::Eq => self.emit(OpCodeType::Equal, vec![]),
                        Token::Ne => self.emit(OpCodeType::NotEqual, vec![]),
                        _ => todo!(),
                    };

                    Ok(())
                }
                Expression::Boolean(boolean_expr) => match boolean_expr.value {
                    true => {
                        self.emit(OpCodeType::True, vec![]);
                        Ok(())
                    }
                    false => {
                        self.emit(OpCodeType::False, vec![]);
                        Ok(())
                    }
                },
                Expression::If(if_expression) => {
                    self.compile(Rc::clone(&if_expression.condition).into())?;
                    let jump_not_truthy_pos =
                        self.emit(OpCodeType::JumpNotTruthy, vec![Self::KEKL_VALUE]);

                    self.compile(Rc::clone(&if_expression.consequence).into())?;

                    if self.last_instruction_is_pop() {
                        self.remove_last_pop()?;
                    }

                    let jump_pos = self.emit(OpCodeType::Jump, vec![Self::KEKL_VALUE]);

                    let after_consequence_pos = self.instructions.len() as i32;
                    self.change_operand(jump_not_truthy_pos, after_consequence_pos)?;

                    match &if_expression.alternative {
                        Some(alternative) => {
                            self.compile(Rc::clone(alternative).into())?;

                            if self.last_instruction_is_pop() {
                                self.remove_last_pop()?;
                            }
                        }
                        None => {
                            self.emit(OpCodeType::Null, vec![]);
                        }
                    }

                    let after_alternative_pos = self.instructions.len() as i32;
                    self.change_operand(jump_pos, after_alternative_pos)?;

                    Ok(())
                }
                Expression::FunctionLiteral(_) => todo!(),
                Expression::Call(_) => todo!(),
                Expression::ArrayLiteral(array) => {
                    for el in &array.elements {
                        self.compile(Rc::clone(el).into())?;
                    }

                    self.emit(OpCodeType::Array, vec![array.elements.len() as i32]);

                    Ok(())
                }
                Expression::IndexExpression(index_exp) => {
                    self.compile(Rc::clone(&index_exp.left).into())?;
                    self.compile(Rc::clone(&index_exp.index).into())?;

                    self.emit(OpCodeType::Index, vec![]);

                    Ok(())
                }
                Expression::HashLiteral(hash_literal) => {
                    let mut keys: Vec<_> = hash_literal.pairs.keys().collect();
                    keys.sort_unstable_by(|&a, &b| {
                        a.as_ref().to_string().cmp(&b.as_ref().to_string())
                    });

                    for key in keys {
                        self.compile(Rc::clone(&key).into())?;

                        let value = hash_literal
                            .pairs
                            .get(key)
                            .ok_or(String::from("couldn't compile hash literal"))?;
                        self.compile(Rc::clone(value).into())?;
                    }

                    self.emit(
                        OpCodeType::Hash,
                        vec![(hash_literal.pairs.len() * 2) as i32],
                    );

                    Ok(())
                }
            },
        }
    }

    pub fn byte_code(&self) -> ByteCode {
        ByteCode {
            constants: self.constants.clone(),
            instructions: self.instructions.clone(),
        }
    }

    fn add_constant(&mut self, obj: Object) -> usize {
        self.constants.push(obj);
        self.constants.len() - 1
    }

    fn emit(&mut self, op: OpCodeType, operands: Vec<i32>) -> usize {
        let instructions = make(op.clone(), operands);
        let pos = self.add_instructions(instructions);

        self.set_last_instruction(op, pos);

        pos
    }

    fn add_instructions(&mut self, instructions: Instructions) -> usize {
        let new_instruction_position = self.instructions.len();

        for byte in instructions {
            self.instructions.0.push(byte);
        }

        new_instruction_position
    }

    fn set_last_instruction(&mut self, op: OpCodeType, pos: usize) {
        let prev = self.last_instruction.clone();
        let last = Some(EmittedInstruction {
            op_code: op,
            position: pos,
        });

        self.prev_instruction = prev;
        self.last_instruction = last;
    }

    fn last_instruction_is_pop(&self) -> bool {
        match &self.last_instruction {
            Some(instruction) => match instruction.op_code {
                OpCodeType::Pop => true,
                _ => false,
            },
            None => false,
        }
    }

    fn remove_last_pop(&mut self) -> InterpreterResult<()> {
        match &self.last_instruction {
            Some(EmittedInstruction {
                op_code: _,
                position,
            }) => {
                self.instructions = self
                    .instructions
                    .0
                    .get(..*position)
                    .ok_or(String::from("couldn't compile, failed to remove last pop"))?
                    .into();
                self.last_instruction = self.prev_instruction.clone();

                Ok(())
            }
            None => Err(String::from("couldn't compile, failed to remove last pop")),
        }
    }

    fn replace_instructions(
        &mut self,
        pos: usize,
        new_instructions: Instructions,
    ) -> InterpreterResult<()> {
        for idx in 0..new_instructions.len() {
            match (self.instructions.get(pos + idx), new_instructions.get(idx)) {
                (Some(_), Some(_)) => {
                    self.instructions.0[pos + idx] = new_instructions[idx];
                }
                _ => Err(String::from(
                    "couldn't compile, failed to replace intructions",
                ))?,
            }
        }

        Ok(())
    }

    fn change_operand(&mut self, pos: usize, operand: i32) -> InterpreterResult<()> {
        if let None = self.instructions.get(pos) {
            return Err(String::from("couldn't compile, failed change operand"));
        }

        let op: OpCodeType = self.instructions[pos]
            .try_into()
            .map_err(|_| String::from("couldn't compile, failed change operand"))?;
        let new_instructions = make(op, vec![operand]);

        self.replace_instructions(pos, new_instructions)
    }
}

#[cfg(test)]
mod test {
    use core::panic;

    use crate::{
        code::code::{make, Instructions, OpCodeType},
        compiler::compiler::Compiler,
        evaluator::types::Object,
        lexer::lexer::Lexer,
        parser::parser::Parser,
    };

    use super::ByteCode;

    struct TestCase {
        input: String,
        expected_constants: Vec<TestCaseResult>,
        expected_instructions: Vec<Instructions>,
    }

    #[derive(Debug)]
    enum TestCaseResult {
        Integer(i64),
        String(String),
    }

    impl TestCaseResult {
        fn test(&self, obj: &Object) {
            match (self, obj) {
                (TestCaseResult::Integer(expected), Object::Integer(actual_int)) => {
                    assert_eq!(expected, &actual_int.value)
                }
                (TestCaseResult::String(expected), Object::String(actual_str)) => {
                    assert_eq!(expected, &actual_str.value)
                }
                (t1, t2) => panic!("can't compare {t1:?} and {t2:?}"),
            }
        }
    }

    fn run_compiler_tests(cases: Vec<TestCase>) {
        for case in cases {
            let lexer = Lexer::new(case.input.clone());
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                println!("{err}");
            }

            assert!(program.is_ok());
            let program = program.unwrap();

            let mut compiler = Compiler::new();

            if let Err(err) = compiler.compile(program) {
                panic!("{err}");
            }

            let byte_code = compiler.byte_code();

            test_instructions(&byte_code, &case);
            test_constants(&byte_code, &case);
        }
    }

    fn test_constants(byte_code: &ByteCode, expected: &TestCase) {
        assert_eq!(byte_code.constants.len(), expected.expected_constants.len());

        for (idx, constant) in expected.expected_constants.iter().enumerate() {
            constant.test(&byte_code.constants[idx]);
        }
    }

    fn test_instructions(byte_code: &ByteCode, expected: &TestCase) {
        let instructions = expected
            .expected_instructions
            .clone()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        assert_eq!(
            Instructions(instructions).to_string(),
            *byte_code.instructions.to_string()
        );
    }

    #[test]
    fn integer_arithmetic_test() {
        let expected = vec![
            TestCase {
                input: String::from("1 + 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Add, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1; 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 - 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Sub, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 * 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Mul, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("2 / 1"),
                expected_constants: vec![TestCaseResult::Integer(2), TestCaseResult::Integer(1)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Div, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("-1"),
                expected_constants: vec![TestCaseResult::Integer(1)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Minus, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn boolean_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from("true"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("false"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::False, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 > 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::GreaterThan, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 < 2"),
                expected_constants: vec![TestCaseResult::Integer(2), TestCaseResult::Integer(1)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::GreaterThan, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 == 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Equal, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("1 != 2"),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::NotEqual, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("true == false"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::False, vec![]),
                    make(OpCodeType::Equal, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("true != false"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::False, vec![]),
                    make(OpCodeType::NotEqual, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("!true"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::Bang, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn conditionals_test() {
        let expected = vec![
            TestCase {
                input: String::from("if (true) { 10 }; 3333;"),
                expected_constants: vec![
                    TestCaseResult::Integer(10),
                    TestCaseResult::Integer(3333),
                ],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::JumpNotTruthy, vec![10]),
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Jump, vec![11]),
                    make(OpCodeType::Null, vec![]),
                    make(OpCodeType::Pop, vec![]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("if (true) { 10 } else { 20 }; 3333;"),
                expected_constants: vec![
                    TestCaseResult::Integer(10),
                    TestCaseResult::Integer(20),
                    TestCaseResult::Integer(3333),
                ],
                expected_instructions: vec![
                    make(OpCodeType::True, vec![]),
                    make(OpCodeType::JumpNotTruthy, vec![10]),
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Jump, vec![13]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn global_let_statement() {
        let expected = vec![
            TestCase {
                input: String::from(
                    "
let one = 1;
let two = 2;
",
                ),
                expected_constants: vec![TestCaseResult::Integer(1), TestCaseResult::Integer(2)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::SetGlobal, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::SetGlobal, vec![1]),
                ],
            },
            TestCase {
                input: String::from(
                    "
let one = 1;
one;
",
                ),
                expected_constants: vec![TestCaseResult::Integer(1)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::SetGlobal, vec![0]),
                    make(OpCodeType::GetGlobal, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from(
                    "
let one = 1;
let two = one;
two;
",
                ),
                expected_constants: vec![TestCaseResult::Integer(1)],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::SetGlobal, vec![0]),
                    make(OpCodeType::GetGlobal, vec![0]),
                    make(OpCodeType::SetGlobal, vec![1]),
                    make(OpCodeType::GetGlobal, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn string_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from(r#""monkey""#),
                expected_constants: vec![TestCaseResult::String(String::from("monkey"))],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from(r#""mon" + "key""#),
                expected_constants: vec![
                    TestCaseResult::String(String::from("mon")),
                    TestCaseResult::String(String::from("key")),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Add, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn array_literal_test() {
        let expected = vec![
            TestCase {
                input: String::from("[]"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::Array, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("[1, 2, 3]"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Array, vec![3]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("[1 + 2, 3 - 4, 5 * 6]"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                    TestCaseResult::Integer(4),
                    TestCaseResult::Integer(5),
                    TestCaseResult::Integer(6),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Add, vec![]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Constant, vec![3]),
                    make(OpCodeType::Sub, vec![]),
                    make(OpCodeType::Constant, vec![4]),
                    make(OpCodeType::Constant, vec![5]),
                    make(OpCodeType::Mul, vec![]),
                    make(OpCodeType::Array, vec![3]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn hash_literal_test() {
        let expected = vec![
            TestCase {
                input: String::from("{}"),
                expected_constants: vec![],
                expected_instructions: vec![
                    make(OpCodeType::Hash, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("{1: 2, 3: 4, 5: 6}"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                    TestCaseResult::Integer(4),
                    TestCaseResult::Integer(5),
                    TestCaseResult::Integer(6),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Constant, vec![3]),
                    make(OpCodeType::Constant, vec![4]),
                    make(OpCodeType::Constant, vec![5]),
                    make(OpCodeType::Hash, vec![6]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("{ 1: 2 + 3, 4: 5 * 6 }"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                    TestCaseResult::Integer(4),
                    TestCaseResult::Integer(5),
                    TestCaseResult::Integer(6),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Add, vec![]),
                    make(OpCodeType::Constant, vec![3]),
                    make(OpCodeType::Constant, vec![4]),
                    make(OpCodeType::Constant, vec![5]),
                    make(OpCodeType::Mul, vec![]),
                    make(OpCodeType::Hash, vec![4]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn index_expression_test() {
        let expected = vec![
            TestCase {
                input: String::from("[1, 2, 3][1 + 1]"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(3),
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(1),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Array, vec![3]),
                    make(OpCodeType::Constant, vec![3]),
                    make(OpCodeType::Constant, vec![4]),
                    make(OpCodeType::Add, vec![]),
                    make(OpCodeType::Index, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("{1: 2}[2 - 1]"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(2),
                    TestCaseResult::Integer(1),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Hash, vec![2]),
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Constant, vec![3]),
                    make(OpCodeType::Sub, vec![]),
                    make(OpCodeType::Index, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }
}
