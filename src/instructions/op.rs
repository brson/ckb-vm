#![allow(unused)]

use std::fmt::{self, Debug, Formatter};

pub use ckb_vm_definitions::instructions::{
    self as insts, Instruction, InstructionOpcode, INSTRUCTION_OPCODE_NAMES, MAXIMUM_RVC_OPCODE,
    MINIMAL_RVC_OPCODE,
};

pub struct Op(pub InstructionOpcode);

impl Debug for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", INSTRUCTION_OPCODE_NAMES[self.0 as usize])
    }
}
