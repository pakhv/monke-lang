use std::{
    fmt::{Display, Error},
    ops::Deref,
    vec::IntoIter,
};

const BYTE_LENGTH: usize = 0x8;

pub type OpCode = u8;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Instructions(pub Vec<u8>);

impl Deref for Instructions {
    type Target = Vec<u8>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl IntoIterator for Instructions {
    type Item = u8;

    type IntoIter = IntoIter<u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Into<Instructions> for &[u8] {
    fn into(self) -> Instructions {
        Instructions(self.to_owned())
    }
}

impl Display for Instructions {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut i = 0;
        let mut buffer = String::new();

        while i < self.0.len() {
            let op: OpCodeType = (*self.0.get(i).ok_or(Error)?)
                .try_into()
                .map_err(|_| Error)?;
            let def = get_definition(&op);

            let (operands, read) =
                read_operands(def.clone(), self.0.get(i + 1..).ok_or(Error)?.into());

            let fmt = match operands.len() {
                0 => def.name.to_string(),
                1 => format!("{} {}", op.to_string(), operands[0]),
                _ => Err(Error)?,
            };

            buffer = format!("{buffer}{i:0>4} {fmt}\n");

            i += 1 + read;
        }

        write!(f, "{buffer}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OpCodeType {
    Constant = 1,
    Add,
    Pop,
    Sub,
    Mul,
    Div,
    True,
    False,
    Equal,
    NotEqual,
    GreaterThan,
    Minus,
    Bang,
    JumpNotTruthy,
    Jump,
    Null,
    GetGlobal,
    SetGlobal,
    Array,
    Hash,
    Index,
    Call,
    ReturnValue,
    Return,
    GetLocal,
    SetLocal,
}

impl TryInto<OpCodeType> for u8 {
    type Error = String;

    fn try_into(self) -> Result<OpCodeType, Self::Error> {
        match self {
            1 => Ok(OpCodeType::Constant),
            2 => Ok(OpCodeType::Add),
            3 => Ok(OpCodeType::Pop),
            4 => Ok(OpCodeType::Sub),
            5 => Ok(OpCodeType::Mul),
            6 => Ok(OpCodeType::Div),
            7 => Ok(OpCodeType::True),
            8 => Ok(OpCodeType::False),
            9 => Ok(OpCodeType::Equal),
            10 => Ok(OpCodeType::NotEqual),
            11 => Ok(OpCodeType::GreaterThan),
            12 => Ok(OpCodeType::Minus),
            13 => Ok(OpCodeType::Bang),
            14 => Ok(OpCodeType::JumpNotTruthy),
            15 => Ok(OpCodeType::Jump),
            16 => Ok(OpCodeType::Null),
            17 => Ok(OpCodeType::GetGlobal),
            18 => Ok(OpCodeType::SetGlobal),
            19 => Ok(OpCodeType::Array),
            20 => Ok(OpCodeType::Hash),
            21 => Ok(OpCodeType::Index),
            22 => Ok(OpCodeType::Call),
            23 => Ok(OpCodeType::ReturnValue),
            24 => Ok(OpCodeType::Return),
            25 => Ok(OpCodeType::GetLocal),
            26 => Ok(OpCodeType::SetLocal),
            n => {
                let error = format!("Error converting \"{n}\" to OpCodeType");

                println!("{error}");
                Err(error)
            }
        }
    }
}

impl From<OpCodeType> for u8 {
    fn from(value: OpCodeType) -> Self {
        match value {
            OpCodeType::Constant => 1,
            OpCodeType::Add => 2,
            OpCodeType::Pop => 3,
            OpCodeType::Sub => 4,
            OpCodeType::Mul => 5,
            OpCodeType::Div => 6,
            OpCodeType::True => 7,
            OpCodeType::False => 8,
            OpCodeType::Equal => 9,
            OpCodeType::NotEqual => 10,
            OpCodeType::GreaterThan => 11,
            OpCodeType::Minus => 12,
            OpCodeType::Bang => 13,
            OpCodeType::JumpNotTruthy => 14,
            OpCodeType::Jump => 15,
            OpCodeType::Null => 16,
            OpCodeType::GetGlobal => 17,
            OpCodeType::SetGlobal => 18,
            OpCodeType::Array => 19,
            OpCodeType::Hash => 20,
            OpCodeType::Index => 21,
            OpCodeType::Call => 22,
            OpCodeType::ReturnValue => 23,
            OpCodeType::Return => 24,
            OpCodeType::GetLocal => 25,
            OpCodeType::SetLocal => 26,
        }
    }
}

impl Display for OpCodeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpCodeType::Constant => write!(f, "OpConstant"),
            OpCodeType::Add => write!(f, "OpAdd"),
            OpCodeType::Pop => write!(f, "OpPop"),
            OpCodeType::Sub => write!(f, "OpSub"),
            OpCodeType::Mul => write!(f, "OpMul"),
            OpCodeType::Div => write!(f, "OpDiv"),
            OpCodeType::True => write!(f, "OpTrue"),
            OpCodeType::False => write!(f, "OpFalse"),
            OpCodeType::Equal => write!(f, "OpEqual"),
            OpCodeType::NotEqual => write!(f, "OpNotEqual"),
            OpCodeType::GreaterThan => write!(f, "OpGreaterThan"),
            OpCodeType::Minus => write!(f, "OpMinus"),
            OpCodeType::Bang => write!(f, "OpBang"),
            OpCodeType::JumpNotTruthy => write!(f, "OpJumpNotTruthy"),
            OpCodeType::Jump => write!(f, "OpJump"),
            OpCodeType::Null => write!(f, "OpNull"),
            OpCodeType::GetGlobal => write!(f, "OpGetGlobal"),
            OpCodeType::SetGlobal => write!(f, "OpSetGlobal"),
            OpCodeType::Array => write!(f, "OpArray"),
            OpCodeType::Hash => write!(f, "OpHash"),
            OpCodeType::Index => write!(f, "OpIndex"),
            OpCodeType::Call => write!(f, "OpCall"),
            OpCodeType::ReturnValue => write!(f, "OpReturnValue"),
            OpCodeType::Return => write!(f, "OpReturn"),
            OpCodeType::GetLocal => write!(f, "OpGetLocal"),
            OpCodeType::SetLocal => write!(f, "OpSetLocal"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Definition {
    pub name: OpCodeType,
    pub operand_widths: Vec<u32>,
}

pub fn get_definition(name: &OpCodeType) -> Definition {
    let operand_widths = match name {
        OpCodeType::Constant => vec![2],
        OpCodeType::Add => vec![],
        OpCodeType::Pop => vec![],
        OpCodeType::Sub => vec![],
        OpCodeType::Mul => vec![],
        OpCodeType::Div => vec![],
        OpCodeType::True => vec![],
        OpCodeType::False => vec![],
        OpCodeType::Equal => vec![],
        OpCodeType::NotEqual => vec![],
        OpCodeType::GreaterThan => vec![],
        OpCodeType::Minus => vec![],
        OpCodeType::Bang => vec![],
        OpCodeType::JumpNotTruthy => vec![2],
        OpCodeType::Jump => vec![2],
        OpCodeType::Null => vec![],
        OpCodeType::GetGlobal => vec![2],
        OpCodeType::SetGlobal => vec![2],
        OpCodeType::Array => vec![2],
        OpCodeType::Hash => vec![2],
        OpCodeType::Index => vec![],
        OpCodeType::Call => vec![1],
        OpCodeType::ReturnValue => vec![],
        OpCodeType::Return => vec![],
        OpCodeType::GetLocal => vec![1],
        OpCodeType::SetLocal => vec![1],
    };

    Definition {
        name: name.clone(),
        operand_widths,
    }
}

pub fn make(op: OpCodeType, operands: Vec<i32>) -> Instructions {
    let definition = get_definition(&op);

    let mut converted_operands = operands
        .iter()
        .enumerate()
        .map(|(idx, operand)| {
            (0..=definition.operand_widths[idx] - 1)
                .rev()
                .map(|byte_num| ((*operand >> byte_num * BYTE_LENGTH as u32) & 0xFF) as u8)
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<u8>>();

    let mut instructions = vec![u8::from(op)];
    instructions.append(&mut converted_operands);

    Instructions(instructions)
}

pub fn read_operands(def: Definition, instruction: Instructions) -> (Vec<i32>, usize) {
    let mut offset = 0;

    let mut result = Vec::with_capacity(def.operand_widths.len());

    for width in def.operand_widths.into_iter() {
        let slice = &instruction.0[offset..offset + width as usize];

        match width {
            2 => {
                result.push((slice[0] as i32) << BYTE_LENGTH | slice[1] as i32);
            }
            1 => result.push(slice[0] as i32),
            _ => (),
        }

        offset += width as usize;
    }

    (result, offset)
}

pub fn read_u16(bytes: &[u8]) -> u16 {
    match bytes.len() {
        0 => 0,
        1 => ((bytes[0] as u16) << BYTE_LENGTH) as u16,
        _ => ((bytes[0] as u16) << BYTE_LENGTH | bytes[1] as u16) as u16,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn make_test() {
        let expected_result: Vec<(_, Vec<i32>, _)> = vec![
            (
                OpCodeType::Constant,
                vec![65534],
                vec![OpCodeType::Constant.into(), 255, 254],
            ),
            (OpCodeType::Add, vec![], vec![OpCodeType::Add.into()]),
            (
                OpCodeType::GetLocal,
                vec![255],
                vec![OpCodeType::GetLocal.into(), 255],
            ),
        ];

        for (opcode, operands, expected) in expected_result {
            let actual = make(opcode, operands);

            assert_eq!(expected.len(), actual.len());

            for (idx, b) in expected.iter().enumerate() {
                assert_eq!(b, &actual[idx]);
            }
        }
    }

    #[test]
    fn read_operands_test() {
        let expected = vec![
            (OpCodeType::Constant, vec![65535], 2),
            (OpCodeType::GetLocal, vec![255], 1),
        ];

        for (op, operands, bytes_read) in expected {
            let instruction = make(op.clone(), operands.clone());
            let def = get_definition(&op);

            let (operands_read, n) = read_operands(def, instruction[1..].into());

            assert_eq!(n, bytes_read);
            assert_eq!(operands_read, operands);
        }
    }

    #[test]
    fn instructions_string_test() {
        let instructions = vec![
            make(OpCodeType::Add, vec![]),
            make(OpCodeType::GetLocal, vec![1]),
            make(OpCodeType::Constant, vec![2]),
            make(OpCodeType::Constant, vec![65535]),
        ];

        let expected = r#"0000 OpAdd
0001 OpGetLocal 1
0003 OpConstant 2
0006 OpConstant 65535
"#;

        let instructions = Instructions(instructions.into_iter().flatten().collect::<Vec<_>>());

        assert_eq!(instructions.to_string(), expected);
    }
}
