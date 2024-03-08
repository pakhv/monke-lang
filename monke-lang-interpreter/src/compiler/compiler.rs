use crate::{code::code::Instructions, evaluator::types::Object, parser::ast::Program};

#[derive(Debug)]
pub struct Compiler {
    pub instructions: Instructions,
    pub constants: Vec<Object>,
}

#[derive(Debug)]
pub struct ByteCode {
    pub instructions: Instructions,
    pub constants: Vec<Object>,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            constants: vec![],
            instructions: Instructions(vec![]),
        }
    }

    pub fn compile(&self, node: Program) {}

    pub fn byte_code(&self) -> ByteCode {
        ByteCode {
            constants: self.constants.clone(),
            instructions: self.instructions.clone(),
        }
    }
}

#[cfg(test)]
mod test {
    use core::panic;
    use std::usize;

    use crate::{
        code::code::{get_definition, make, read_operands, Definition, Instructions, OpCodeType},
        compiler::compiler::Compiler,
        evaluator::types::Object,
        lexer::lexer::Lexer,
        parser::parser::Parser,
    };

    use super::ByteCode;

    trait ConstTest {
        fn test(&self, actual: &Object);
    }

    impl ConstTest for i64 {
        fn test(&self, actual: &Object) {
            match actual {
                Object::Integer(int) => assert_eq!(int.value, *self),
                not_int => panic!("integer expected, got {not_int}"),
            }
        }
    }

    struct TestCase<T>
    where
        T: ConstTest,
    {
        input: String,
        expected_constants: Vec<T>,
        expected_instructions: Vec<Instructions>,
    }

    fn run_compiler_tests<T>(cases: Vec<TestCase<T>>)
    where
        T: ConstTest,
    {
        for case in cases {
            let lexer = Lexer::new(case.input.clone());
            let mut parser = Parser::new(lexer);

            let program = parser.parse_program();

            if let Err(err) = &program {
                println!("{err}");
            }

            assert!(program.is_ok());
            let program = program.unwrap();

            let compiler = Compiler::new();
            compiler.compile(program);

            let byte_code = compiler.byte_code();

            test_instructions(&byte_code, &case);
            test_constants(&byte_code, &case);
        }
    }

    fn test_constants<T>(byte_code: &ByteCode, expected: &TestCase<T>)
    where
        T: ConstTest,
    {
        assert_eq!(byte_code.constants.len(), expected.expected_constants.len());

        for (idx, constant) in expected.expected_constants.iter().enumerate() {
            constant.test(&byte_code.constants[idx]);
        }
    }

    fn test_instructions<T>(byte_code: &ByteCode, expected: &TestCase<T>)
    where
        T: ConstTest,
    {
        let instructions = expected
            .expected_instructions
            .clone()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();

        assert_eq!(instructions, *byte_code.instructions);
    }

    #[test]
    fn integer_arithmetic_test() {
        let expected = vec![TestCase {
            input: String::from("1 + 2"),
            expected_constants: vec![1, 2],
            expected_instructions: vec![
                make(OpCodeType::Constant, vec![0]),
                make(OpCodeType::Constant, vec![1]),
            ],
        }];

        run_compiler_tests(expected);
    }

    #[test]
    fn instructions_string_test() {
        let instructions = vec![
            make(OpCodeType::Constant, vec![1]),
            make(OpCodeType::Constant, vec![2]),
            make(OpCodeType::Constant, vec![65535]),
        ];

        let expected = r#"0000 OpConstant 1
0003 OpConstant 2
0006 OpConstant 65535
"#;

        let instructions = Instructions(instructions.into_iter().flatten().collect::<Vec<_>>());

        assert_eq!(instructions.to_string(), expected);
    }
}
