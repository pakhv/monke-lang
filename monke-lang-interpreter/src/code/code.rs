use std::{
    fmt::{Display, Error},
    ops::Deref,
    vec::IntoIter,
};

const BYTE_LENGTH: usize = 0x8;

pub type OpCode = u8;

#[derive(Debug, Clone)]
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

            let (operands, read) = read_operands(def, self.0.get(i + 1..).ok_or(Error)?.into());

            let fmt = match operands.len() {
                1 => format!("{} {}", op.to_string(), operands[0]),
                _ => Err(Error)?,
            };

            buffer = format!("{buffer}{i:0>4} {fmt}\n");

            i += 1 + read;
        }

        write!(f, "{buffer}")
    }
}

#[derive(Clone, Debug)]
pub enum OpCodeType {
    Constant = 1,
}

impl TryInto<OpCodeType> for u8 {
    type Error = String;

    fn try_into(self) -> Result<OpCodeType, Self::Error> {
        match self {
            1 => Ok(OpCodeType::Constant),
            n => Err(format!("Error converting \"{n}\" to OpCodeType")),
        }
    }
}

impl From<OpCodeType> for u8 {
    fn from(value: OpCodeType) -> Self {
        match value {
            OpCodeType::Constant => 1,
        }
    }
}

impl Display for OpCodeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpCodeType::Constant => write!(f, "OpConstant"),
        }
    }
}

#[derive(Debug)]
pub struct Definition {
    pub name: OpCodeType,
    pub operand_widths: Vec<u32>,
}

pub fn get_definition(name: &OpCodeType) -> Definition {
    let operand_widths = match name {
        OpCodeType::Constant => vec![2],
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
            _ => todo!(),
        }

        offset += width as usize;
    }

    (result, offset)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn make_test() {
        let expected_result: Vec<(_, Vec<i32>, _)> = vec![(
            OpCodeType::Constant,
            vec![65534],
            vec![OpCodeType::Constant.into(), 255, 254],
        )];

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
        let expected = vec![(OpCodeType::Constant, vec![65535], 2)];

        for (op, operands, bytes_read) in expected {
            let instruction = make(op.clone(), operands.clone());
            let def = get_definition(&op);

            let (operands_read, n) = read_operands(def, instruction[1..].into());

            assert_eq!(n, bytes_read);
            assert_eq!(operands_read, operands);
        }
    }
}
