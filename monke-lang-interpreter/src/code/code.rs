type OpCode = u8;
type Instructions = Vec<u8>;

#[derive(Clone, Debug)]
pub enum OpCodeType {
    Constant = 1,
}

impl From<OpCodeType> for u8 {
    fn from(value: OpCodeType) -> Self {
        match value {
            OpCodeType::Constant => 1,
        }
    }
}

#[derive(Debug)]
pub struct Definition {
    name: OpCodeType,
    operand_widths: Vec<u32>,
}

fn get_definition(name: &OpCodeType) -> Definition {
    let operand_widths = match name {
        OpCodeType::Constant => vec![2],
    };

    Definition {
        name: name.clone(),
        operand_widths,
    }
}

pub fn make(op: OpCodeType, operands: Vec<i32>) -> Vec<u8> {
    let definition = get_definition(&op);

    let mut converted_operands = operands
        .iter()
        .enumerate()
        .map(|(idx, operand)| {
            (0..=definition.operand_widths[idx] - 1)
                .rev()
                .map(|byte_num| ((*operand >> byte_num * 0x8) & 0xFF) as u8)
                .collect::<Vec<_>>()
        })
        .flatten()
        .collect::<Vec<u8>>();

    let mut instructions = vec![u8::from(op)];
    instructions.append(&mut converted_operands);

    instructions
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
}
