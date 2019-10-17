#![allow(unused)]

use std::fmt::{self, Debug, Formatter};

pub use ckb_vm_definitions::registers::REGISTER_ABI_NAMES;

pub struct Reg(pub usize);

impl Debug for Reg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", REGISTER_ABI_NAMES[self.0 as usize])
    }
}
