use std::rc::Rc;

use crate::{
    code::code::{make, Instructions, OpCodeType},
    evaluator::types::{CompiledFunction, Integer, Object, Str},
    lexer::token::Token,
    parser::ast::{Expression, Program, Statement},
    result::InterpreterResult,
};

use super::symbol_table::{SymbolScope, SymbolTable, SymbolTableRef};

#[derive(Debug, Clone)]
struct EmittedInstruction {
    op_code: OpCodeType,
    position: usize,
}

#[derive(Debug)]
pub struct CompilationScope {
    pub instructions: Instructions,
    last_instruction: Option<EmittedInstruction>,
    prev_instruction: Option<EmittedInstruction>,
}

#[derive(Debug)]
pub struct Compiler {
    pub constants: Vec<Object>,
    pub symbol_table: SymbolTableRef,
    pub scopes: Vec<CompilationScope>,
    scope_index: usize,
}

#[derive(Debug)]
pub struct ByteCode {
    pub instructions: Instructions,
    pub constants: Vec<Object>,
}

impl Compiler {
    const KEKL_VALUE: i32 = 9999;

    pub fn new() -> Self {
        let main_scope = CompilationScope {
            instructions: Instructions(vec![]),
            last_instruction: None,
            prev_instruction: None,
        };

        Compiler {
            constants: vec![],
            symbol_table: SymbolTable::new(),
            scopes: vec![main_scope],
            scope_index: 0,
        }
    }

    pub fn new_with_state(symbol_table: SymbolTableRef, constants: Vec<Object>) -> Self {
        let main_scope = CompilationScope {
            instructions: Instructions(vec![]),
            last_instruction: None,
            prev_instruction: None,
        };

        Compiler {
            constants,
            symbol_table,
            scopes: vec![main_scope],
            scope_index: 0,
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

                    let symbol = self
                        .symbol_table
                        .borrow_mut()
                        .define(let_statement.name.to_string());

                    match symbol.scope {
                        SymbolScope::Global => {
                            self.emit(OpCodeType::SetGlobal, vec![symbol.index as i32])?
                        }
                        SymbolScope::Local => {
                            self.emit(OpCodeType::SetLocal, vec![symbol.index as i32])?
                        }
                    };

                    Ok(())
                }
                Statement::Return(return_statement) => {
                    self.compile(Rc::clone(&return_statement.return_value).into())?;
                    self.emit(OpCodeType::ReturnValue, vec![])?;

                    Ok(())
                }
                Statement::Expression(expression_statement) => {
                    self.compile(Rc::clone(&expression_statement.expression).into())?;
                    self.emit(OpCodeType::Pop, vec![])?;

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
                        .borrow()
                        .resolve(&ident.to_string())
                        .ok_or(format!("couldn't resolve identifier value: \"{ident}\""))?
                        .clone();

                    match value.scope {
                        SymbolScope::Global => {
                            self.emit(OpCodeType::GetGlobal, vec![value.index as i32])?
                        }
                        SymbolScope::Local => {
                            self.emit(OpCodeType::GetLocal, vec![value.index as i32])?
                        }
                    };

                    Ok(())
                }
                Expression::IntegerLiteral(int_expression) => {
                    let int = Object::Integer(Integer {
                        value: int_expression.value,
                    });
                    let operand = self.add_constant(int);
                    self.emit(OpCodeType::Constant, vec![operand as i32])?;

                    Ok(())
                }
                Expression::StringLiteral(string) => {
                    let str = Object::String(Str {
                        value: string.to_string(),
                    });
                    let operand = self.add_constant(str);
                    self.emit(OpCodeType::Constant, vec![operand as i32])?;

                    Ok(())
                }
                Expression::Prefix(prefix) => {
                    self.compile(Rc::clone(&prefix.right).into())?;

                    match &prefix.token {
                        Token::Bang => self.emit(OpCodeType::Bang, vec![])?,
                        Token::Minus => self.emit(OpCodeType::Minus, vec![])?,
                        actual => Err(format!("couldn't compile prefix expression, bang or minus operators expected, but got {actual}"))?,
                    };

                    Ok(())
                }
                Expression::Infix(infix_expression) => {
                    if infix_expression.token == Token::Lt {
                        self.compile(Rc::clone(&infix_expression.right).into())?;
                        self.compile(Rc::clone(&infix_expression.left).into())?;
                        self.emit(OpCodeType::GreaterThan, vec![])?;

                        return Ok(());
                    }

                    self.compile(Rc::clone(&infix_expression.left).into())?;
                    self.compile(Rc::clone(&infix_expression.right).into())?;

                    match infix_expression.token {
                        Token::Plus => self.emit(OpCodeType::Add, vec![])?,
                        Token::Minus => self.emit(OpCodeType::Sub, vec![])?,
                        Token::Asterisk => self.emit(OpCodeType::Mul, vec![])?,
                        Token::Slash => self.emit(OpCodeType::Div, vec![])?,
                        Token::Gt => self.emit(OpCodeType::GreaterThan, vec![])?,
                        Token::Eq => self.emit(OpCodeType::Equal, vec![])?,
                        Token::Ne => self.emit(OpCodeType::NotEqual, vec![])?,
                        _ => todo!(),
                    };

                    Ok(())
                }
                Expression::Boolean(boolean_expr) => match boolean_expr.value {
                    true => {
                        self.emit(OpCodeType::True, vec![])?;
                        Ok(())
                    }
                    false => {
                        self.emit(OpCodeType::False, vec![])?;
                        Ok(())
                    }
                },
                Expression::If(if_expression) => {
                    self.compile(Rc::clone(&if_expression.condition).into())?;
                    let jump_not_truthy_pos =
                        self.emit(OpCodeType::JumpNotTruthy, vec![Self::KEKL_VALUE])?;

                    self.compile(Rc::clone(&if_expression.consequence).into())?;

                    if self.last_instruction_is(OpCodeType::Pop) {
                        self.remove_last_pop()?;
                    }

                    let jump_pos = self.emit(OpCodeType::Jump, vec![Self::KEKL_VALUE])?;

                    let after_consequence_pos =
                        self.current_instructions().ok_or(String::from(""))?.len() as i32;
                    self.change_operand(jump_not_truthy_pos, after_consequence_pos)?;

                    match &if_expression.alternative {
                        Some(alternative) => {
                            self.compile(Rc::clone(alternative).into())?;

                            if self.last_instruction_is(OpCodeType::Pop) {
                                self.remove_last_pop()?;
                            }
                        }
                        None => {
                            self.emit(OpCodeType::Null, vec![])?;
                        }
                    }

                    let after_alternative_pos =
                        self.current_instructions().ok_or(String::from(""))?.len() as i32;
                    self.change_operand(jump_pos, after_alternative_pos)?;

                    Ok(())
                }
                Expression::FunctionLiteral(func) => {
                    self.enter_scope();
                    self.compile(Rc::clone(&func.body).into())?;

                    if self.last_instruction_is(OpCodeType::Pop) {
                        self.replace_last_pop_with_return()?;
                    }

                    if !self.last_instruction_is(OpCodeType::ReturnValue) {
                        self.emit(OpCodeType::Return, vec![])?;
                    }

                    let instructions = self.leave_scope().ok_or(String::from(""))?;
                    let compiled_fn = Object::CompiledFunction(CompiledFunction { instructions });

                    let compiled_fn_const = self.add_constant(compiled_fn);
                    self.emit(OpCodeType::Constant, vec![compiled_fn_const as i32])?;

                    Ok(())
                }
                Expression::Call(call) => {
                    self.compile(Rc::clone(&call.function).into())?;
                    self.emit(OpCodeType::Call, vec![])?;

                    Ok(())
                }
                Expression::ArrayLiteral(array) => {
                    for el in &array.elements {
                        self.compile(Rc::clone(el).into())?;
                    }

                    self.emit(OpCodeType::Array, vec![array.elements.len() as i32])?;

                    Ok(())
                }
                Expression::IndexExpression(index_exp) => {
                    self.compile(Rc::clone(&index_exp.left).into())?;
                    self.compile(Rc::clone(&index_exp.index).into())?;

                    self.emit(OpCodeType::Index, vec![])?;

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
                    )?;

                    Ok(())
                }
            },
        }
    }

    pub fn byte_code(&self) -> InterpreterResult<ByteCode> {
        Ok(ByteCode {
            constants: self.constants.clone(),
            instructions: self.current_instructions().ok_or(String::from(""))?,
        })
    }

    fn add_constant(&mut self, obj: Object) -> usize {
        self.constants.push(obj);
        self.constants.len() - 1
    }

    fn emit(&mut self, op: OpCodeType, operands: Vec<i32>) -> InterpreterResult<usize> {
        let instructions = make(op.clone(), operands);
        let pos = self.add_instructions(instructions)?;

        self.set_last_instructions(op, pos)?;

        Ok(pos)
    }

    fn add_instructions(&mut self, instructions: Instructions) -> InterpreterResult<usize> {
        let cur_instructions = self
            .current_instructions()
            .ok_or(String::from("couldn't get current instructions"))?;
        let new_instruction_position = cur_instructions.len();

        let updated_instructions = [cur_instructions.0, instructions.0].concat();
        self.scopes[self.scope_index].instructions = Instructions(updated_instructions);

        Ok(new_instruction_position)
    }

    fn current_instructions(&self) -> Option<Instructions> {
        self.scopes
            .get(self.scope_index)
            .and_then(|scope| Some(scope.instructions.clone()))
    }

    fn set_last_instructions(&mut self, op: OpCodeType, pos: usize) -> InterpreterResult<()> {
        let prev = self
            .scopes
            .get(self.scope_index)
            .ok_or(String::from("couldn't set last instruction"))?
            .last_instruction
            .clone();

        let last = Some(EmittedInstruction {
            op_code: op,
            position: pos,
        });

        self.scopes[self.scope_index].prev_instruction = prev;
        self.scopes[self.scope_index].last_instruction = last;

        Ok(())
    }

    fn last_instructions_is_pop(&self) -> bool {
        match self
            .scopes
            .get(self.scope_index)
            .and_then(|scope| scope.last_instruction.as_ref())
        {
            Some(instruction) => match instruction.op_code {
                OpCodeType::Pop => true,
                _ => false,
            },
            None => false,
        }
    }

    fn remove_last_pop(&mut self) -> InterpreterResult<()> {
        match &self
            .scopes
            .get(self.scope_index)
            .and_then(|scope| scope.last_instruction.as_ref())
        {
            Some(EmittedInstruction {
                op_code: _,
                position,
            }) => {
                self.scopes[self.scope_index].instructions = self.scopes[self.scope_index]
                    .instructions
                    .get(..*position)
                    .ok_or(String::from("couldn't compile, failed to remove last pop"))?
                    .into();
                self.scopes[self.scope_index].last_instruction =
                    self.scopes[self.scope_index].prev_instruction.clone();

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
            match (
                self.scopes
                    .get(self.scope_index)
                    .and_then(|scope| scope.instructions.get(pos + idx)),
                new_instructions.get(idx),
            ) {
                (Some(_), Some(_)) => {
                    self.scopes[self.scope_index].instructions.0[pos + idx] = new_instructions[idx];
                }
                _ => Err(String::from(
                    "couldn't compile, failed to replace intructions",
                ))?,
            }
        }

        Ok(())
    }

    fn change_operand(&mut self, pos: usize, operand: i32) -> InterpreterResult<()> {
        let cur_instructions = self.current_instructions();

        if let None = cur_instructions {
            return Err(String::from("couldn't compile, failed change operand"));
        }

        let cur_instructions = cur_instructions.unwrap();
        let op = cur_instructions.get(pos);

        if let None = op {
            return Err(String::from("couldn't compile, failed change operand"));
        }

        let op = *op.clone().unwrap();
        let op: OpCodeType = op
            .try_into()
            .map_err(|_| String::from("couldn't compile, failed change operand"))?;
        let new_instructions = make(op, vec![operand]);

        self.replace_instructions(pos, new_instructions)
    }

    fn enter_scope(&mut self) {
        let scope = CompilationScope {
            instructions: Instructions(vec![]),
            last_instruction: None,
            prev_instruction: None,
        };

        self.scopes.push(scope);
        self.scope_index += 1;
        self.symbol_table = SymbolTable::new_enclosed(Rc::clone(&self.symbol_table));
    }

    fn leave_scope(&mut self) -> Option<Instructions> {
        let scope = self.scopes.pop();

        match scope {
            Some(_) => self.scope_index -= 1,
            None => (),
        };

        let outer_symbol_table = {
            let symbol_table = self.symbol_table.borrow();
            Rc::clone(symbol_table.outer.as_ref().ok_or(format!("")).unwrap())
        };

        self.symbol_table = outer_symbol_table;

        scope.map(|scope| scope.instructions)
    }

    fn last_instruction_is(&self, op: OpCodeType) -> bool {
        match self.scopes.get(self.scope_index) {
            Some(scope) => match &scope.last_instruction {
                Some(ins) => ins.op_code == op,
                None => false,
            },
            None => false,
        }
    }

    fn replace_last_pop_with_return(&mut self) -> InterpreterResult<()> {
        let mut last_instructions = self
            .scopes
            .get(self.scope_index)
            .ok_or(String::from(""))?
            .last_instruction
            .clone()
            .ok_or(String::from(""))?;

        self.replace_instructions(
            last_instructions.position,
            make(OpCodeType::ReturnValue, vec![]),
        )?;
        last_instructions.op_code = OpCodeType::ReturnValue;
        self.scopes[self.scope_index].last_instruction = Some(last_instructions);

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use core::panic;
    use std::rc::Rc;

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
        InstructionsVec(Vec<Instructions>),
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
                (
                    TestCaseResult::InstructionsVec(expected),
                    Object::CompiledFunction(actual_func),
                ) => {
                    let expected_flattened: Instructions = expected
                        .clone()
                        .into_iter()
                        .flatten()
                        .collect::<Vec<_>>()
                        .as_slice()
                        .into();

                    assert_eq!(
                        expected_flattened.to_string(),
                        actual_func.instructions.to_string()
                    );
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
            assert!(byte_code.is_ok());
            let byte_code = byte_code.unwrap();

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

    #[test]
    fn function_test() {
        let expected = vec![
            TestCase {
                input: String::from("fn() { return 5 + 10 }"),
                expected_constants: vec![
                    TestCaseResult::Integer(5),
                    TestCaseResult::Integer(10),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::Constant, vec![1]),
                        make(OpCodeType::Add, vec![]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("fn() { 5 + 10 }"),
                expected_constants: vec![
                    TestCaseResult::Integer(5),
                    TestCaseResult::Integer(10),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::Constant, vec![1]),
                        make(OpCodeType::Add, vec![]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("fn() { 1; 2 }"),
                expected_constants: vec![
                    TestCaseResult::Integer(1),
                    TestCaseResult::Integer(2),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::Pop, vec![]),
                        make(OpCodeType::Constant, vec![1]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from("fn() { }"),
                expected_constants: vec![TestCaseResult::InstructionsVec(vec![make(
                    OpCodeType::Return,
                    vec![],
                )])],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn compiler_scope_test() {
        let mut compiler = Compiler::new();
        assert_eq!(compiler.scope_index, 0);

        assert!(compiler.emit(OpCodeType::Mul, vec![]).is_ok());
        compiler.enter_scope();

        assert_eq!(compiler.scope_index, 1);
        assert!(compiler.emit(OpCodeType::Sub, vec![]).is_ok());

        assert!(compiler.scopes.get(compiler.scope_index).is_some());
        assert_eq!(compiler.scopes[compiler.scope_index].instructions.len(), 1);

        let last = compiler.scopes[compiler.scope_index]
            .last_instruction
            .clone();
        assert!(last.is_some());
        assert_eq!(last.unwrap().op_code, OpCodeType::Sub);

        compiler.leave_scope();
        assert_eq!(compiler.scope_index, 0);

        assert!(compiler.emit(OpCodeType::Add, vec![]).is_ok());
        assert!(compiler.scopes.get(compiler.scope_index).is_some());
        assert_eq!(compiler.scopes[compiler.scope_index].instructions.len(), 2);

        let last = compiler.scopes[compiler.scope_index]
            .last_instruction
            .clone();
        assert!(last.is_some());
        assert_eq!(last.unwrap().op_code, OpCodeType::Add);

        let prev = compiler.scopes[compiler.scope_index]
            .prev_instruction
            .clone();
        assert!(prev.is_some());
        assert_eq!(prev.unwrap().op_code, OpCodeType::Mul);
    }

    #[test]
    fn function_call_test() {
        let expected = vec![
            TestCase {
                input: String::from("fn() { 24 }();"),
                expected_constants: vec![
                    TestCaseResult::Integer(24),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Call, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from(
                    "let noArg = fn() { 24 };
noArg();",
                ),
                expected_constants: vec![
                    TestCaseResult::Integer(24),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::SetGlobal, vec![0]),
                    make(OpCodeType::GetGlobal, vec![0]),
                    make(OpCodeType::Call, vec![]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn let_statement_scope_test() {
        let expected = vec![
            TestCase {
                input: String::from(
                    "
let num = 55;
fn() { num };",
                ),
                expected_constants: vec![
                    TestCaseResult::Integer(55),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::GetGlobal, vec![0]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![0]),
                    make(OpCodeType::SetGlobal, vec![0]),
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from(
                    "
fn() {
    let num = 55;
    num
}",
                ),
                expected_constants: vec![
                    TestCaseResult::Integer(55),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::SetLocal, vec![0]),
                        make(OpCodeType::GetLocal, vec![0]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![1]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
            TestCase {
                input: String::from(
                    "
fn() {
    let a = 55;
    let b = 77;
    a + b
}
",
                ),
                expected_constants: vec![
                    TestCaseResult::Integer(55),
                    TestCaseResult::Integer(77),
                    TestCaseResult::InstructionsVec(vec![
                        make(OpCodeType::Constant, vec![0]),
                        make(OpCodeType::SetLocal, vec![0]),
                        make(OpCodeType::Constant, vec![1]),
                        make(OpCodeType::SetLocal, vec![1]),
                        make(OpCodeType::GetLocal, vec![0]),
                        make(OpCodeType::GetLocal, vec![1]),
                        make(OpCodeType::Add, vec![]),
                        make(OpCodeType::ReturnValue, vec![]),
                    ]),
                ],
                expected_instructions: vec![
                    make(OpCodeType::Constant, vec![2]),
                    make(OpCodeType::Pop, vec![]),
                ],
            },
        ];

        run_compiler_tests(expected);
    }

    #[test]
    fn compiler_scopes_test() {
        let mut compiler = Compiler::new();
        assert_eq!(0, compiler.scope_index);

        let global_scope = Rc::clone(&compiler.symbol_table);

        assert!(compiler.emit(OpCodeType::Mul, vec![]).is_ok());
        compiler.enter_scope();
        assert_eq!(1, compiler.scope_index);

        assert!(compiler.emit(OpCodeType::Sub, vec![]).is_ok());

        assert!(compiler.scopes.get(compiler.scope_index).is_some());
        assert_eq!(1, compiler.scopes[compiler.scope_index].instructions.len());

        let last = compiler.scopes[compiler.scope_index]
            .last_instruction
            .as_ref();

        assert!(last.is_some());
        assert_eq!(OpCodeType::Sub, last.unwrap().op_code);

        {
            assert!(compiler.symbol_table.borrow().outer.is_some());
            let symbol_table = compiler.symbol_table.borrow();

            let outer = symbol_table.outer.as_ref().unwrap().borrow();
            assert_eq!(outer.store, global_scope.borrow().store);
            assert_eq!(outer.outer, global_scope.borrow().outer);
            assert_eq!(outer.num_definitions, global_scope.borrow().num_definitions);
        }

        compiler.leave_scope();

        assert_eq!(0, compiler.scope_index);

        {
            let symbol_table = compiler.symbol_table.borrow();

            assert_eq!(symbol_table.store, global_scope.borrow().store);
            assert_eq!(symbol_table.outer, global_scope.borrow().outer);
            assert_eq!(
                symbol_table.num_definitions,
                global_scope.borrow().num_definitions
            );
            assert!(compiler.symbol_table.borrow().outer.is_none());
        }

        assert!(compiler.emit(OpCodeType::Add, vec![]).is_ok());
        assert_eq!(2, compiler.scopes[compiler.scope_index].instructions.len());

        let last = compiler.scopes[compiler.scope_index]
            .last_instruction
            .as_ref();

        assert!(last.is_some());
        assert_eq!(OpCodeType::Add, last.unwrap().op_code);

        let prev = compiler.scopes[compiler.scope_index]
            .prev_instruction
            .as_ref();

        assert!(prev.is_some());
        assert_eq!(OpCodeType::Mul, prev.unwrap().op_code);
    }
}
