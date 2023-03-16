use crate::opcodes;
use std::collections::HashMap;

pub const CARRY_FLAG: u8 =        0b0000_0001;
pub const ZERO_FLAG: u8 =         0b0000_0010;
pub const INTERRUPT_DISABLE: u8 = 0b0000_0100;
pub const DECIMAL_MODE_FLAG: u8 = 0b0000_1000;
pub const BREAK_ONE: u8 =         0b0001_0000;
pub const BREAK_TWO: u8 =         0b0010_0000;
pub const OVERFLOW_FLAG: u8 =     0b0100_0000;
pub const NEGATIVE_FLAG: u8 =     0b1000_0000;

pub const INV_CARRY_FLAG: u8 =        0b1111_1110;
pub const INV_ZERO_FLAG: u8 =         0b1111_1101;
pub const INV_INTERRUPT_DISABLE: u8 = 0b1111_1011;
pub const INV_DECIMAL_MODE_FLAG: u8 = 0b1111_0111;
pub const INV_BREAK_ONE: u8 =         0b1110_1111;
pub const INV_BREAK_TWO: u8 =         0b1101_1111;
pub const INV_OVERFLOW_FLAG: u8 =     0b1011_1111;
pub const INV_NEGATIVE_FLAG: u8 =     0b0111_1111;


pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,  
    memory: [u8; 0xFFFF]
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}
  
impl CPU {

    pub fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            program_counter: 0,
            memory: [0x00; 0xFFFF]
        }
    }

    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000 .. (0x8000 + program.len())].copy_from_slice(&program[..]);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    pub fn run(&mut self) {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;
        loop {
            let code = self.mem_read(self.program_counter);
            self.program_counter += 1;
            let program_counter_state = self.program_counter;

            let opcode = opcodes.get(&code).expect(&format!("OpCode {:x} is not recognized", code));

            match code {
                // ADC
                0x69 | 0x65 | 0x75 | 0x6d | 0x7d | 0x79 | 0x61 | 0x71 => {
                    self.adc(&opcode.mode);
                }
                // AND
                0x29 | 0x25 | 0x35 | 0x2d | 0x3d | 0x39 | 0x21 | 0x31 => {
                    self.and(&opcode.mode);
                }
                // ASL
                0x0a | 0x06 | 0x16 | 0x0e | 0x1e => {
                    self.asl(&opcode.mode);
                }
                // BCC
                0x90 => self.bcc(),
                // BCS
                0xB0 => self.bcs(),
                // BEQ
                0xF0 => self.beq(),
                // BMI
                0x30 => self.bmi(),
                // BNE
                0xd0 => self.bne(),
                // BPL
                0x10 => self.bpl(),
                // BVC
                0x50 => self.bvc(),
                // BVS
                0x70 => self.bvs(),
                // BIT
                0x24 | 0x2C => {
                    self.bit(&opcode.mode);
                }
                // CLC
                0x18 => self.clc(),
                // CLD
                0xd8 => self.cld(),
                //CLI
                0x58 => self.cli(),
                // CLV
                0xb8 => self.clv(),
                // CMP
                0xc9 | 0xC5 | 0xd5 | 0xcd | 0xdd | 0xd9 | 0xc1 | 0xd1 => {
                    self.cmp(&opcode.mode);
                }
                // CPX
                0xe0 | 0xe4 | 0xec => {
                    self.cpx(&opcode.mode);
                }
                // CPY
                0xc0 | 0xc4 | 0xcc => {
                    self.cpy(&opcode.mode);
                }
                // DEC
                0xc6 | 0xd6 | 0xce | 0xde => {
                    self.dec(&opcode.mode);
                }
                // LDA
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }
                // STA
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x1 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                0xAA => self.tax(), // TAX
                0xE8 => self.inx(), // INX
                0x00 => return, // BRK
                _ => todo!()
            }

            if program_counter_state == self.program_counter {
                self.program_counter += (opcode.len - 1) as u16;
            }
        }
    }

    fn update_carry_flag(&mut self, carry: bool) {
        if carry {
            self.status = self.status | CARRY_FLAG;
        } else {
            self.status = self.status & INV_CARRY_FLAG;
        }
    }

    fn update_zero_and_negative_flags(&mut self, result: u8) {
        if result == 0 {
            self.status = self.status | ZERO_FLAG;
        } else {
            self.status = self.status & INV_ZERO_FLAG;
        }

        if result & 0b1000_0000 != 0 {
            self.status = self.status | NEGATIVE_FLAG;
        } else {
            self.status = self.status & INV_NEGATIVE_FLAG;
        }
    }

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(self.program_counter);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }
            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(self.program_counter);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect_X => {
                let base = self.mem_read(self.program_counter);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(self.program_counter);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        // add self.register_a and value 
        let (mut result, mut carry) = self.register_a.overflowing_add(value);
        // add 1 if carry flag already set
        if self.status & 0b0000_0001 != 0 {
            (result, carry) = result.overflowing_add(1);
        }
        // set carry flag
        self.update_carry_flag(carry);
        // set overflow with magic math
        if ((self.register_a ^ result) & (value ^ result) & 0x80) != 0 {
            self.status = self.status | OVERFLOW_FLAG;
        } else {
            self.status = self.status & INV_OVERFLOW_FLAG;
        }
        self.register_a = result;
        self.update_zero_and_negative_flags(result);
    }

    fn and(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = self.register_a & value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn asl(&mut self, mode: &AddressingMode) {
        match mode {
            // Accumulator Addressing
            AddressingMode::NoneAddressing => {
                // set carry flag to contents of bit 7 before shift
                self.update_carry_flag(self.register_a & 0b1000_0000 != 0);
                //shift
                self.register_a = (((self.register_a as u16) << 1) & 0b0_1111_1111) as u8;
                self.update_zero_and_negative_flags(self.register_a);
            } 
            _ => {
                let addr = self.get_operand_address(mode);
                let value = self.mem_read(addr);
                let result = (((value as u16) << 1) & 0b0_1111_1111) as u8;

                // set carry flag
                self.update_carry_flag(value & 0b1000_0000 != 0);

                self.mem_write(addr, result);
                self.update_zero_and_negative_flags(result);
            }
        }
    }

    fn branch(&mut self) {
        let jump: i8 = self.mem_read(self.program_counter) as i8;
        let jump_addr = self.program_counter.wrapping_add(1).wrapping_add(jump as u16);

        self.program_counter = jump_addr;
    }

    fn bcc(&mut self) {
        // only branch if carry bit is 0
        if self.status & CARRY_FLAG == 0 {
            self.branch();
        }
    }

    fn bcs(&mut self) {
        // only branch if carry bit is 1
        if self.status & CARRY_FLAG != 0 {
            self.branch();
        }
    }

    fn beq(&mut self) {
        // only branch if zero flag set
        if self.status & ZERO_FLAG != 0 {
            self.branch();
        }
    }

    fn bmi(&mut self) {
        // branch on negative flag set
        if self.status & NEGATIVE_FLAG != 0 {
            self.branch();
        }
    }

    fn bne(&mut self) {
        // branch on zero flag clear
        if self.status & ZERO_FLAG == 0 {
            self.branch();
        }
    }

    fn bpl(&mut self) {
        // branch on positive
        if self.status & NEGATIVE_FLAG == 0 {
            self.branch();
        }
    }

    fn bvc(&mut self) {
        // branch on no overflow
        if self.status & OVERFLOW_FLAG == 0 {
            self.branch();
        }
    }

    fn bvs(&mut self) {
        // branch on overflow
        if self.status & OVERFLOW_FLAG != 0 {
            self.branch();
        }
    }

    fn bit(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);

        let test = data & self.register_a;
        self.update_zero_and_negative_flags(test);
        if data & 0b0100_0000 != 0 {
            self.status = self.status | OVERFLOW_FLAG;
        } else {
            self.status = self.status & INV_OVERFLOW_FLAG;
        }
    }

    fn clc(&mut self) {
        self.status = self.status & INV_CARRY_FLAG;
    }

    fn cld(&mut self) {
        self.status = self.status & INV_DECIMAL_MODE_FLAG;
    }
    fn cli(&mut self) {
        self.status = self.status & INV_INTERRUPT_DISABLE;
    }
    fn clv(&mut self) {
        self.status = self.status & INV_OVERFLOW_FLAG;
    }

    fn compare(&mut self, comparator: u8, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        if comparator >= value {
            self.status = self.status | CARRY_FLAG;
        } else {
            self.status = self.status & INV_CARRY_FLAG;
        }
        self.update_zero_and_negative_flags(comparator.wrapping_sub(value));
    }

    fn cmp(&mut self, mode: &AddressingMode) {
        self.compare(self.register_a, mode);
    }

    fn cpx(&mut self, mode: &AddressingMode) {
        self.compare(self.register_x, mode);
    }

    fn cpy(&mut self, mode: &AddressingMode) {
        self.compare(self.register_y, mode);
    }

    fn dec(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let result = value.wrapping_sub(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
  
  #[test]
  fn test_0xa9_lda_load_data() {
      let mut cpu = CPU::new();
      cpu.load_and_run(vec![0xa9, 0x05, 0x00]);

      assert_eq!(cpu.register_a, 0x05);
      assert!(cpu.status & ZERO_FLAG == 0b00);
      assert!(cpu.status & NEGATIVE_FLAG == 0);
  }

  #[test]
  fn test_0xa9_lda_zero_flag() {
      let mut cpu = CPU::new();
      cpu.load_and_run(vec![0xa9, 0x00, 0x00]);

      assert!(cpu.status & ZERO_FLAG == 0b10);
  }

  #[test]
  fn test_0xa9_lda_negative_flag() {
      let mut cpu = CPU::new();
      cpu.load_and_run(vec![0xa9, 0x81, 0x00]);

      assert!(cpu.status & NEGATIVE_FLAG != 0);
  }

  #[test]
  fn test_lda_from_memory() {
    let mut cpu = CPU::new();
    cpu.mem_write(0x10, 0x55);

    cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

    assert_eq!(cpu.register_a, 0x55);
  }

  #[test]
  fn test_0xaa_tax_move_a_to_x() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xaa, 0x00]);
    cpu.reset();
    cpu.register_a = 10;
    assert_eq!(cpu.register_a, 10);
    cpu.run();
    assert_eq!(cpu.register_x, 10);
  }

  #[test]
  fn test_inx_overflow() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xE8, 0xE8, 0x00]);
    cpu.reset();
    cpu.register_x = 0xff;
    cpu.run();

    assert_eq!(cpu.register_x, 1);
  }

  #[test]
  fn test_5_ops_work_together() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

    assert_eq!(cpu.register_x, 0xc1);
  }

  #[test]
  fn test_sta() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xa2, 0x85, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0xa2);
  }

  #[test]
  fn test_and() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xa2, 0x85, 0x10, 0xa9, 0x03, 0x2d, 0x10, 0x00, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_asl_shifts_bit_in_memory() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0x06, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x02);
  }

  #[test]
  fn test_asl_shifts_accumulator() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x01, 0x0a, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_asl_shift_accumulator_fills_carry_bit() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xff, 0x0a, 0x00]);
    assert_eq!(cpu.register_a, 0b1111_1110);
    assert!(cpu.status & CARRY_FLAG != 0);
  }

  #[test]
  fn test_asl_memory_fills_carry_bit() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0x06, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0b1111_1110);
    assert!(cpu.status & CARRY_FLAG != 0);
  }

  #[test]
  fn test_adc_immediate() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0x65, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_adc_sets_carry() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0xa9, 0x01, 0x65, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x00);
    assert!(cpu.status & CARRY_FLAG != 0);
    assert!(cpu.status & OVERFLOW_FLAG == 0);
  }

  #[test]
  fn test_adc_sets_overflow() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x50, 0x85, 0x10, 0x65, 0x10, 0x00]);
    assert!(cpu.status & CARRY_FLAG == 0);
    assert!(cpu.status & OVERFLOW_FLAG != 0);
  }

  #[test]
  fn test_bcc_branches_on_clear() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xfc, 0x69, 0x01, 0x90, 0xfc, 0x00]);
    assert_eq!(cpu.register_x, 0x00);
  }

  #[test]
  fn test_bit_set_neg_and_overflow() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xc0, 0x85, 0x10, 0x24, 0x10, 0x00]);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
    assert_ne!(cpu.status & OVERFLOW_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0)
  }

  #[test]
  fn test_bit_set_zero() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x00, 0x85, 0x10, 0x24, 0x10, 0x00]);
    assert_ne!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & OVERFLOW_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_clc() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x18, 0x00]);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_cld() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xd8, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | DECIMAL_MODE_FLAG;
    cpu.run();
    assert_eq!(cpu.status & DECIMAL_MODE_FLAG, 0);
  }

  #[test]
  fn test_cli() {
    let mut cpu = CPU::new();
    cpu.load(vec![0x58, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | INTERRUPT_DISABLE;
    cpu.run();
    assert_eq!(cpu.status & INTERRUPT_DISABLE, 0);
  }

  #[test]
  fn test_clv() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xb8, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | OVERFLOW_FLAG;
    cpu.run();
    assert_eq!(cpu.status & OVERFLOW_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_carry() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xa9, 0x03, 0xcd, 0x10, 0x00, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_zero() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_ne!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_negative_and_carry() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xa9, 0xff, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_negative_only(){
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0xfe, 0x85, 0x10, 0xa9, 0xf0, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_cpx() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xa9, 0xf0, 0x85, 0x10, 0xe4, 0x10, 0x00]);
    cpu.reset();
    cpu.register_x = 0xfe;
    cpu.run();
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_cpy() {
    let mut cpu = CPU::new();
    cpu.load(vec![0xa9, 0xf0, 0x85, 0x10, 0xc4, 0x10, 0x00]);
    cpu.reset();
    cpu.register_y = 0xfe;
    cpu.run();
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_dec_dec_by_one() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xc6, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x01);
  }

  #[test]
  fn test_dec_set_zero() {
    let mut cpu = CPU::new();
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0xc6, 0x10, 0x00]);
  }
}
