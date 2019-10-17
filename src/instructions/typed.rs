#![allow(unused)]

use super::{
    super::{machine::Machine, registers::SP, Error},
    common, extract_opcode, instruction_length,
    utils::update_register,
    Instruction, InstructionOpcode, Itype, Register, Rtype, Stype, Utype,
};
use ckb_vm_definitions::instructions as insts;
use std::fmt::{self, Debug, Formatter};
use crate::instructions::op::Op;

#[derive(Debug, Clone, Copy)]
pub enum AnyInst {
    Rtype(Rtype),
    Stype(Stype),
    Itype(Itype),
    Utype(Utype),
    System(SystemInst),
}

#[derive(Clone, Copy)]
pub struct SystemInst(pub Instruction);

impl SystemInst {
    pub fn op(self) -> InstructionOpcode {
        self.0 as u8 as InstructionOpcode
    }
}

impl Debug for SystemInst {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("System")
            .field("op", &Op(self.op()))
            .finish()
    }
}

pub fn get<Mac: Machine>(inst: Instruction, machine: &Mac) -> Result<AnyInst, Error> {
    let op = extract_opcode(inst);
    match op {
        insts::OP_SUB => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        /*insts::OP_SUBW => {
            let i = Rtype(inst);
            common::subw(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_ADD => {
            let i = Rtype(inst);
            common::add(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_ADDW => {
            let i = Rtype(inst);
            common::addw(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_XOR => {
            let i = Rtype(inst);
            common::xor(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_OR => {
            let i = Rtype(inst);
            common::or(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_AND => {
            let i = Rtype(inst);
            common::and(machine, i.rd(), i.rs1(), i.rs2());
            None
        }*/
        insts::OP_SLL => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        /*insts::OP_SLLW => {
            let i = Rtype(inst);
            let shift_value = machine.registers()[i.rs2()].clone() & Mac::REG::from_u8(0x1F);
            let value = machine.registers()[i.rs1()].clone() << shift_value;
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_SRL => {
            let i = Rtype(inst);
            let shift_value =
                machine.registers()[i.rs2()].clone() & Mac::REG::from_u8(Mac::REG::SHIFT_MASK);
            let value = machine.registers()[i.rs1()].clone() >> shift_value;
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_SRLW => {
            let i = Rtype(inst);
            let shift_value = machine.registers()[i.rs2()].clone() & Mac::REG::from_u8(0x1F);
            let value =
                machine.registers()[i.rs1()].zero_extend(&Mac::REG::from_u8(32)) >> shift_value;
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_SRA => {
            let i = Rtype(inst);
            let shift_value =
                machine.registers()[i.rs2()].clone() & Mac::REG::from_u8(Mac::REG::SHIFT_MASK);
            let value = machine.registers()[i.rs1()].signed_shr(&shift_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_SRAW => {
            let i = Rtype(inst);
            let shift_value = machine.registers()[i.rs2()].clone() & Mac::REG::from_u8(0x1F);
            let value = machine.registers()[i.rs1()]
                .sign_extend(&Mac::REG::from_u8(32))
                .signed_shr(&shift_value);
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_SLT => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.lt_s(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_SLTU => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.lt(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_LB => {
            let i = Itype(inst);
            common::lb(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }
        insts::OP_LH => {
            let i = Itype(inst);
            common::lh(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }*/
        insts::OP_LW => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_LD => {
            let i = Itype(inst);
            common::ld(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }*/
        insts::OP_LBU => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_LHU => {
            let i = Itype(inst);
            common::lhu(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }
        insts::OP_LWU => {
            let i = Itype(inst);
            common::lwu(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }*/
        insts::OP_ADDI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_ADDIW => {
            let i = Itype(inst);
            common::addiw(machine, i.rd(), i.rs1(), i.immediate_s());
            None
        }
        insts::OP_XORI => {
            let i = Itype(inst);
            common::xori(machine, i.rd(), i.rs1(), i.immediate_s());
            None
        }
        insts::OP_ORI => {
            let i = Itype(inst);
            common::ori(machine, i.rd(), i.rs1(), i.immediate_s());
            None
        }*/
        insts::OP_ANDI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_SLTI => {
            let i = Itype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let imm_value = Mac::REG::from_i32(i.immediate_s());
            let value = rs1_value.lt_s(&imm_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_SLTIU => {
            let i = Itype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let imm_value = Mac::REG::from_i32(i.immediate_s());
            let value = rs1_value.lt(&imm_value);
            update_register(machine, i.rd(), value);
            None
        }*/
        insts::OP_JALR => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        insts::OP_SLLI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_SRLI => {
            let i = Itype(inst);
            common::srli(machine, i.rd(), i.rs1(), i.immediate());
            None
        }*/
        insts::OP_SRAI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_SLLIW => {
            let i = Itype(inst);
            common::slliw(machine, i.rd(), i.rs1(), i.immediate());
            None
        }
        insts::OP_SRLIW => {
            let i = Itype(inst);
            common::srliw(machine, i.rd(), i.rs1(), i.immediate());
            None
        }
        insts::OP_SRAIW => {
            let i = Itype(inst);
            common::sraiw(machine, i.rd(), i.rs1(), i.immediate());
            None
        }*/
        insts::OP_SB => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        /*insts::OP_SH => {
            let i = Stype(inst);
            common::sh(machine, i.rs1(), i.rs2(), i.immediate_s())?;
            None
        }*/
        insts::OP_SW => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        /*insts::OP_SD => {
            let i = Stype(inst);
            common::sd(machine, i.rs1(), i.rs2(), i.immediate_s())?;
            None
        }*/
        insts::OP_BEQ => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_BNE => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_BLT => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        /*insts::OP_BGE => {
            let i = Stype(inst);
            let pc = machine.pc();
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let condition = rs1_value.ge_s(&rs2_value);
            let new_pc = condition.cond(
                &Mac::REG::from_i32(i.immediate_s()).overflowing_add(&pc),
                &Mac::REG::from_u8(4).overflowing_add(&pc),
            );
            Some(new_pc)
        }*/
        insts::OP_BLTU => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_BGEU => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_LUI => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_AUIPC => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_ECALL => {
            Ok(AnyInst::System(SystemInst(inst)))
        }
        /*insts::OP_EBREAK => {
            machine.ebreak()?;
            None
        }
        insts::OP_FENCEI => None,
        insts::OP_FENCE => None,
        insts::OP_JAL => {
            let i = Utype(inst);
            common::jal(machine, i.rd(), i.immediate_s(), 4)
        }
        insts::OP_MUL => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_mul(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_MULW => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value
                .zero_extend(&Mac::REG::from_u8(32))
                .overflowing_mul(&rs2_value.zero_extend(&Mac::REG::from_u8(32)));
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_MULH => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_mul_high_signed(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_MULHSU => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_mul_high_signed_unsigned(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_MULHU => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_mul_high_unsigned(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_DIV => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_div_signed(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_DIVW => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let rs1_value = rs1_value.sign_extend(&Mac::REG::from_u8(32));
            let rs2_value = rs2_value.sign_extend(&Mac::REG::from_u8(32));
            let value = rs1_value.overflowing_div_signed(&rs2_value);
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_DIVU => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_div(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_DIVUW => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let rs1_value = rs1_value.zero_extend(&Mac::REG::from_u8(32));
            let rs2_value = rs2_value.zero_extend(&Mac::REG::from_u8(32));
            let value = rs1_value.overflowing_div(&rs2_value);
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_REM => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_rem_signed(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_REMW => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let rs1_value = rs1_value.sign_extend(&Mac::REG::from_u8(32));
            let rs2_value = rs2_value.sign_extend(&Mac::REG::from_u8(32));
            let value = rs1_value.overflowing_rem_signed(&rs2_value);
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }
        insts::OP_REMU => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let value = rs1_value.overflowing_rem(&rs2_value);
            update_register(machine, i.rd(), value);
            None
        }
        insts::OP_REMUW => {
            let i = Rtype(inst);
            let rs1_value = &machine.registers()[i.rs1()];
            let rs2_value = &machine.registers()[i.rs2()];
            let rs1_value = rs1_value.zero_extend(&Mac::REG::from_u8(32));
            let rs2_value = rs2_value.zero_extend(&Mac::REG::from_u8(32));
            let value = rs1_value.overflowing_rem(&rs2_value);
            update_register(machine, i.rd(), value.sign_extend(&Mac::REG::from_u8(32)));
            None
        }*/
        insts::OP_RVC_SUB => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        insts::OP_RVC_ADD => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        /*insts::OP_RVC_XOR => {
            let i = Rtype(inst);
            common::xor(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        insts::OP_RVC_OR => {
            let i = Rtype(inst);
            common::or(machine, i.rd(), i.rs1(), i.rs2());
            None
        }*/
        insts::OP_RVC_AND => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        // > C.SUBW (RV64/128; RV32 RES)
        /*insts::OP_RVC_SUBW => {
            let i = Rtype(inst);
            common::subw(machine, i.rd(), i.rs1(), i.rs2());
            None
        }
        // > C.ADDW (RV64/128; RV32 RES)
        insts::OP_RVC_ADDW => {
            let i = Rtype(inst);
            common::addw(machine, i.rd(), i.rs1(), i.rs2());
            None
        }*/
        insts::OP_RVC_ADDI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        insts::OP_RVC_ANDI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_RVC_ADDIW => {
            let i = Itype(inst);
            common::addiw(machine, i.rd(), i.rs1(), i.immediate_s());
            None
        }*/
        insts::OP_RVC_SLLI => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_RVC_SRLI => {
            let i = Itype(inst);
            common::srli(machine, i.rd(), i.rs1(), i.immediate());
            None
        }
        insts::OP_RVC_SRAI => {
            let i = Itype(inst);
            common::srai(machine, i.rd(), i.rs1(), i.immediate());
            None
        }*/
        insts::OP_RVC_LW => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_RVC_LD => {
            let i = Itype(inst);
            common::ld(machine, i.rd(), i.rs1(), i.immediate_s())?;
            None
        }*/
        insts::OP_RVC_SW => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        /*insts::OP_RVC_SD => {
            let i = Stype(inst);
            common::sd(machine, i.rs1(), i.rs2(), i.immediate_s())?;
            None
        }*/
        insts::OP_RVC_LI => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_RVC_LUI => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_RVC_ADDI4SPN => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_RVC_LWSP => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        /*insts::OP_RVC_LDSP => {
            let i = Utype(inst);
            common::ld(machine, i.rd(), SP, i.immediate_s())?;
            None
        }*/
        insts::OP_RVC_SWSP => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        /*insts::OP_RVC_SDSP => {
            let i = Stype(inst);
            common::sd(machine, SP, i.rs2(), i.immediate_s())?;
            None
        }*/
        insts::OP_RVC_BEQZ => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_RVC_BNEZ => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_RVC_MV => {
            Ok(AnyInst::Rtype(Rtype(inst)))
        }
        insts::OP_RVC_JAL => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_RVC_J => {
            Ok(AnyInst::Utype(Utype(inst)))
        }
        insts::OP_RVC_JR => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_RVC_JALR => {
            Ok(AnyInst::Stype(Stype(inst)))
        }
        insts::OP_RVC_ADDI16SP => {
            Ok(AnyInst::Itype(Itype(inst)))
        }
        /*insts::OP_RVC_SRLI64 => None,
        insts::OP_RVC_SRAI64 => None,
        insts::OP_RVC_SLLI64 => None,
        insts::OP_RVC_NOP => None,
        insts::OP_RVC_EBREAK => {
            machine.ebreak()?;
            None
        }
        insts::OP_CUSTOM_LOAD_IMM => {
            let i = Utype(inst);
            let value = Mac::REG::from_i32(i.immediate_s());
            update_register(machine, i.rd(), value);
            None
        }*/
        _ => Err(Error::InvalidOp(op as u8)),
    }
}
