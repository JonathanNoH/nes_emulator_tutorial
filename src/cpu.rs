use crate::{opcodes, bus::Bus};
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

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;


pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,
    pub stack_ptr: u8,
    pub bus: Bus,
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
    Indirect,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

pub trait Mem {
    fn mem_read(&mut self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);


    fn mem_read_u16(&mut self, pos: u16) -> u16 {
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
}

impl Mem for CPU {

    fn mem_read(&mut self, addr: u16) -> u8 {
        self.bus.mem_read(addr)
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.bus.mem_write(addr, data);
    }

    fn mem_read_u16(&mut self, pos: u16) -> u16 {
        self.bus.mem_read_u16(pos)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        self.bus.mem_write_u16(pos, data);
    }
}
  
impl CPU {

    pub fn new(bus: Bus) -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0b100100,
            program_counter: 0,
            stack_ptr: STACK_RESET,
            bus,
        }
    }

    pub fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0b100100;
        self.stack_ptr = STACK_RESET;
        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    pub fn load_and_run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.run();
    }

    pub fn load(&mut self, program: Vec<u8>) {
        /* CHANGE BACK TO 0x8000 */
        for i in 0..(program.len() as u16) {
            self.mem_write(0x0600 + i, program[i as usize]);
        }
        //self.mem_write_u16(0xFFFC, 0x0600);
    }

    pub fn run(&mut self) {
        self.run_with_callback(|_| {});
    }

    pub fn run_with_callback<F>(&mut self, mut callback: F)
    where
        F: FnMut(&mut CPU)
    {
        let ref opcodes: HashMap<u8, &'static opcodes::OpCode> = *opcodes::OPCODES_MAP;
        loop {
            callback(self);

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
                // DEX
                0xca => self.dex(),
                // DEY
                0x88 => self.dey(),
                // EOR
                0x49 | 0x45 | 0x55 | 0x4d | 0x5d | 0x59 | 0x41 | 0x51 => {
                    self.eor(&opcode.mode);
                }
                // INC
                0xe6 | 0xf6 | 0xee | 0xfe => {
                    self.inc(&opcode.mode);
                }
                // INX
                0xE8 => self.inx(),
                // INY
                0xc8 => self.iny(),
                // JMP
                0x4c | 0x6c => {
                    self.jmp(&opcode.mode);
                }
                //JSR
                0x20 => {
                    self.jsr();
                }
                // LDA
                0xa9 | 0xa5 | 0xb5 | 0xad | 0xbd | 0xb9 | 0xa1 | 0xb1 => {
                    self.lda(&opcode.mode);
                }
                // LDX
                0xa2 | 0xa6 | 0xb6 | 0xae | 0xbe => {
                    self.ldx(&opcode.mode);
                }
                // LDY
                0xa0 | 0xa4 | 0xb4 | 0xac | 0xbc => {
                    self.ldy(&opcode.mode);
                }
                // LSR
                0x4a | 0x46 | 0x56 | 0x4e | 0x5e => {
                    self.lsr(&opcode.mode);
                }
                // NOP
                0xea => self.nop(),
                // ORA
                0x09 | 0x05 | 0x15 | 0x0d | 0x1d | 0x19 | 0x01 | 0x11 => {
                    self.ora(&opcode.mode);
                }
                // PHA
                0x48 => self.pha(),
                // PHP
                0x08 => self.php(),
                // PLA
                0x68 => self.pla(),
                // PLP
                0x28 => self.plp(),
                // RTS
                0x60 => self.rts(),
                // ROL
                0x2a | 0x26 | 0x36 | 0x2e | 0x3e => {
                    self.rol(&opcode.mode);
                }
                // ROR
                0x6a | 0x66 | 0x76 | 0x6e | 0x7e => {
                    self.ror(&opcode.mode);
                }
                // RTI
                0x40 => self.rti(),
                // SBC
                0xe9 | 0xe5 | 0xf5 | 0xed | 0xfd | 0xf9 | 0xe1 | 0xf1 => {
                    self.sbc(&opcode.mode);
                }
                // SEC
                0x38 => self.sec(),
                // SED
                0xf8 => self.sed(),
                // SEI
                0x78 => self.sei(),
                // STA
                0x85 | 0x95 | 0x8d | 0x9d | 0x99 | 0x81 | 0x91 => {
                    self.sta(&opcode.mode);
                }
                // STX
                0x86 | 0x96 | 0x8e => {
                    self.stx(&opcode.mode);
                }
                // STY
                0x84 | 0x94 | 0x8c => {
                    self.sty(&opcode.mode);
                }
                // TAX
                0xAA => self.tax(),
                // TAY
                0xa8 => self.tay(),
                // TSX
                0xba => self.tsx(),
                // TXA
                0x8a => self.txa(),
                // TXA
                0x9a => self.txs(),
                // TYA
                0x98 => self.tya(),
                /* UNOFFICIAL */
                // ANC
                0x0b | 0x2b => self.anc(&opcode.mode),
                // ARR
                0x6b => {
                    self.arr(&opcode.mode);
                }
                // ASR
                0x4b => {
                    self.asr(&opcode.mode);
                }
                // LAX
                0xab | 0xa3 | 0xa7 | 0xaf | 0xb3 | 0xb7 | 0xbf => {
                    self.lax(&opcode.mode);
                }
                // SAX
                0x83 | 0x87 | 0x8f | 0x97 => {
                    self.sax(&opcode.mode);
                }
                // DCP
                0xc3 | 0xc7 | 0xcf | 0xd3 | 0xd7 | 0xdb | 0xdf => {
                    self.dcp(&opcode.mode);
                }
                // ISC
                0xe3 | 0xe7 | 0xef | 0xf3 | 0xf7 | 0xfb | 0xff => {
                    self.isc(&opcode.mode);
                }
                // RLA
                0x23 | 0x27 | 0x2f | 0x33 | 0x37 | 0x3b | 0x3f => {
                    self.rla(&opcode.mode);
                }
                // RRA
                0x63 | 0x67 | 0x6f | 0x73 | 0x77 | 0x7b | 0x7f => {
                    self.rra(&opcode.mode);
                }
                // SLO
                0x03 | 0x07 | 0x0f | 0x13 | 0x17 | 0x1b | 0x1f => {
                    self.slo(&opcode.mode);
                }
                // SRE 
                0x43 | 0x47 | 0x4f | 0x53 | 0x57 | 0x5b | 0x5f => {
                    self.sre(&opcode.mode);
                }
                // SBC but unofficial
                0xeb => {
                    self.sbc(&opcode.mode);
                }
                // MORE NOP
                0x1a | 0x3a | 0x5a | 0x7a | 0xda | 0xfa => {
                    self.nop();
                }
                // SKB NOP 2 ELECTRIC BOOGALOO
                0x80 | 0x82 | 0x89 | 0xc2 | 0xe2 => {
                    self.skb();
                }
                // SKB 3 RETURN OF THE NOP
                0x0c | 0x1c | 0x3c | 0x5c | 0x7c | 0xdc | 0xfc | 0x04 | 0x44 | 0x64 | 0x14 | 0x34 | 0x54 | 0x74 | 0xd4 | 0xf4 => {
                    self.skb();
                }
                0x00 => return, // BRK
                _ => panic!("Something went wrong. Invalid Command.")
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

    pub fn get_absolute_address(&mut self, mode: &AddressingMode, addr: u16) -> u16 {
        match mode {
            AddressingMode::ZeroPage => self.mem_read(addr) as u16,

            AddressingMode::Absolute => self.mem_read_u16(addr),

            AddressingMode::ZeroPage_X => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_x) as u16;
                addr
            }
            AddressingMode::ZeroPage_Y => {
                let pos = self.mem_read(addr);
                let addr = pos.wrapping_add(self.register_y) as u16;
                addr
            }

            AddressingMode::Absolute_X => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_x as u16);
                addr
            }
            AddressingMode::Absolute_Y => {
                let base = self.mem_read_u16(addr);
                let addr = base.wrapping_add(self.register_y as u16);
                addr
            }
            AddressingMode::Indirect => {
                //060f
                // weird bugs with page boundary stuff
                let mem_addr = self.mem_read_u16(self.program_counter);
                let addr = if mem_addr & 0x00FF == 0x00FF {
                    let lo = self.mem_read(mem_addr);
                    let hi = self.mem_read(mem_addr & 0xFF00);
                    (hi as u16) << 8 | (lo as u16)
                } else {
                    self.mem_read_u16(mem_addr)
                };
                addr
            }

            AddressingMode::Indirect_X => {
                let base = self.mem_read(addr);

                let ptr: u8 = (base as u8).wrapping_add(self.register_x);
                let lo = self.mem_read(ptr as u16);
                let hi = self.mem_read(ptr.wrapping_add(1) as u16);
                (hi as u16) << 8 | (lo as u16)
            }
            AddressingMode::Indirect_Y => {
                let base = self.mem_read(addr);

                let lo = self.mem_read(base as u16);
                let hi = self.mem_read((base as u8).wrapping_add(1) as u16);
                let deref_base = (hi as u16) << 8 | (lo as u16);
                let deref = deref_base.wrapping_add(self.register_y as u16);
                deref
            }

            _ => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn get_operand_address(&mut self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            _ => self.get_absolute_address(mode, self.program_counter),
        }
    }

    fn stack_push(&mut self, data: u8) {
        self.mem_write((STACK as u16) + self.stack_ptr as u16, data);
        self.stack_ptr = self.stack_ptr.wrapping_sub(1)
    }

    fn stack_push_u16(&mut self, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.stack_push(hi);
        self.stack_push(lo);
    }

    fn stack_pop(&mut self) -> u8 {
        self.stack_ptr = self.stack_ptr.wrapping_add(1);
        self.mem_read((STACK as u16) + self.stack_ptr as u16)
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lo = self.stack_pop() as u16;
        let hi = self.stack_pop() as u16;

        hi << 8 | lo
    }

    fn adc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.addition(value);
    }

    fn addition(&mut self, value: u8) {
        // add self.register_a and value 
        let (mut result, carry_one) = self.register_a.overflowing_add(value);
        // add 1 if carry flag already set
        let mut carry_two = false;
        if self.status & 0b0000_0001 != 0 {
            (result, carry_two) = result.overflowing_add(1);
        }
        // set carry flag
        self.update_carry_flag(carry_one || carry_two);
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
        //self.update_zero_and_negative_flags(test);
        //zero flag
        if test == 0 {
            self.status = self.status | ZERO_FLAG;
        } else {
            self.status = self.status & INV_ZERO_FLAG;
        }
        //negative
        if data & 0b1000_0000 != 0 {
            self.status = self.status | NEGATIVE_FLAG;
        } else {
            self.status = self.status & INV_NEGATIVE_FLAG;
        }
        // overflow
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
        self.update_carry_flag(comparator >= value);
        self.update_zero_and_negative_flags(comparator.wrapping_sub(value));
        //if comparator == value { self.update_carry_flag(true)};
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

    fn dex(&mut self) {
        self.register_x = self.register_x.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn dey(&mut self) {
        self.register_y = self.register_y.wrapping_sub(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn eor(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = self.register_a ^ value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn inc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        let result = value.wrapping_add(1);
        self.mem_write(addr, result);
        self.update_zero_and_negative_flags(result);
    }

    fn inx(&mut self) {
        self.register_x = self.register_x.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn iny(&mut self) {
        self.register_y = self.register_y.wrapping_add(1);
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn jmp(&mut self, mode: &AddressingMode) {
        let jump_addr = self.get_operand_address(mode);

        self.program_counter = jump_addr;
    }

    fn jsr(&mut self) {
        self.stack_push_u16(self.program_counter + 3 - 1/* jsr len */ - 1);
        let target_addr = self.mem_read_u16(self.program_counter);
        self.program_counter = target_addr
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_a = value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn ldx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_x = value;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn ldy(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.register_y = value;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn lsr(&mut self, mode: &AddressingMode) {
        match mode {
            AddressingMode::NoneAddressing => {
                self.update_carry_flag(self.register_a & 0b0000_0001 != 0);
                self.register_a = self.register_a >> 1;
                self.update_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let addr = self.get_operand_address(mode);
                let value = self.mem_read(addr);
                self.update_carry_flag(value & 0b0000_0001 != 0);
                let result = value >> 1;
                self.mem_write(addr, result);
                self.update_zero_and_negative_flags(result);
            }
        }
    }

    fn nop(&self) {
        return;
    }

    fn ora(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);
        self.register_a = self.register_a | value;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn pha(&mut self) {
        self.stack_push(self.register_a);
    }

    fn php(&mut self) {
        let mut flags = self.status;
        flags = flags | (BREAK_ONE | BREAK_TWO);
        self.stack_push(flags);
    }

    fn pla(&mut self) {
        self.register_a = self.stack_pop();
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn plp(&mut self) {
        self.status = self.stack_pop();
        self.status = self.status & INV_BREAK_ONE;
        self.status = self.status | BREAK_TWO;
    }

    fn rts(&mut self) {
        self.program_counter = self.stack_pop_u16() + 1;
    }

    fn rol(&mut self, mode: &AddressingMode) {
        match mode {
            AddressingMode::NoneAddressing => {
                let old_carry = self.status & CARRY_FLAG;
                self.update_carry_flag(self.register_a & 0b1000_0000 != 0);
                self.register_a = (((self.register_a as u16) << 1) & 0b0_1111_1111) as u8;
                if old_carry != 0 {
                    self.register_a = self.register_a | 0b0000_0001;
                }
                self.update_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let addr = self.get_operand_address(mode);
                let data = self.mem_read(addr);

                let old_carry = self.status & CARRY_FLAG;
                self.update_carry_flag(data & 0b1000_0000 != 0);
                let mut new_data = (((data as u16) << 1) & 0b0_1111_1111) as u8;
                if old_carry != 0 {
                    new_data = new_data | 0b0000_0001;
                }
                self.mem_write(addr, new_data);
                self.update_zero_and_negative_flags(new_data);
            }
        }
    }

    fn ror(&mut self, mode: &AddressingMode) {
        match mode {
            AddressingMode::NoneAddressing => {
                let old_carry = self.status & CARRY_FLAG;
                self.update_carry_flag(self.register_a & 1 != 0);
                self.register_a = self.register_a >> 1;
                if old_carry != 0 {
                    self.register_a = self.register_a | 0b1000_0000;
                }
                self.update_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let addr = self.get_operand_address(mode);
                let data = self.mem_read(addr);

                let old_carry = self.status & CARRY_FLAG;
                self.update_carry_flag(data & 1 != 0);
                let mut new_data = data >> 1;
                if old_carry != 0 {
                    new_data = new_data | 0b1000_0000;
                }
                self.mem_write(addr, new_data);
                self.update_zero_and_negative_flags(new_data);
            }
        }
    }

    fn rti(&mut self) {
        self.status = self.stack_pop();
        self.status = self.status & INV_BREAK_ONE;
        self.status = self.status | BREAK_TWO;

        self.program_counter = self.stack_pop_u16();
    }

    fn sbc(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let value = self.mem_read(addr);

        self.addition(255-value);
    }

    fn sec(&mut self) {
        self.status = self.status | CARRY_FLAG;
    }

    fn sed(&mut self) {
        self.status = self.status | DECIMAL_MODE_FLAG;
    }

    fn sei(&mut self) {
        self.status = self.status | INTERRUPT_DISABLE;
    }

    fn sta(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_a);
    }

    fn stx(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_x);
    }

    fn sty(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        self.mem_write(addr, self.register_y);
    }

    fn tax(&mut self) {
        self.register_x = self.register_a;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn tay(&mut self) {
        self.register_y = self.register_a;
        self.update_zero_and_negative_flags(self.register_y);
    }

    fn tsx(&mut self) {
        self.register_x = self.stack_ptr;
        self.update_zero_and_negative_flags(self.register_x);
    }

    fn txs(&mut self) {
        self.stack_ptr = self.register_x;
    }

    fn txa(&mut self) {
        self.register_a = self.register_x;
        self.update_zero_and_negative_flags(self.register_a);
    }

    fn tya(&mut self) {
        self.register_a = self.register_y;
        self.update_zero_and_negative_flags(self.register_a);
    }

    /* UNNOFFIAL OP CODES */

    fn anc(&mut self, mode: &AddressingMode) {
        self.and(mode);
        self.update_carry_flag(self.status & NEGATIVE_FLAG != 0);
    }

    fn sax(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.register_a & self.register_x;
        self.mem_write(addr, data);
    }

    fn arr(&mut self, mode: &AddressingMode) {
        let addr = self.get_operand_address(mode);
        let data = self.mem_read(addr);
        self.register_a = data & self.register_a;
        let old_carry = self.status & CARRY_FLAG;
        self.register_a = self.register_a >> 1;
        if old_carry != 0 {
            self.register_a = self.register_a | 0b1000_0000;
        }
        self.update_carry_flag(self.register_a & 0b0100_0000 != 0);
        self.update_zero_and_negative_flags(self.register_a);
        if (self.register_a & 0b0100_0000) ^ (self.register_a & 0b0010_0000) != 0 {
            self.status = self.status | OVERFLOW_FLAG;
        } else {
            self.status = self.status & INV_OVERFLOW_FLAG;
        }
    }

    fn asr(&mut self, mode: &AddressingMode) {
        self.and(mode);
        self.lsr(&AddressingMode::NoneAddressing); // Accumulator addressing
    }

    fn lax(&mut self, mode: &AddressingMode) {
        self.lda(mode);
        self.tax();
    }

    fn dcp(&mut self, mode: &AddressingMode) {
        self.dec(mode);
        self.cmp(mode);
    }

    fn isc(&mut self, mode: &AddressingMode) {
        self.inc(mode);
        self.sbc(mode);
    }

    fn rla(&mut self, mode: &AddressingMode) {
        self.rol(mode);
        self.and(mode);
    }

    fn rra(&mut self, mode: &AddressingMode) {
        self.ror(mode);
        self.adc(mode);
    }

    fn slo(&mut self, mode: &AddressingMode) {
        self.asl(mode);
        self.ora(mode);
    }

    fn sre(&mut self, mode: &AddressingMode) {
        self.lsr(mode);
        self.eor(mode);
    }

    fn skb(&mut self) {
        return;
    }

}

#[cfg(test)]
mod tests {
    use crate::rom::test;

    use super::*;
  
  #[test]
  fn test_0xa9_lda_load_data() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
      cpu.load_and_run(vec![0xa9, 0x05, 0x00]);

      assert_eq!(cpu.register_a, 0x05);
      assert!(cpu.status & ZERO_FLAG == 0b00);
      assert!(cpu.status & NEGATIVE_FLAG == 0);
  }

  #[test]
  fn test_0xa9_lda_zero_flag() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
      cpu.load_and_run(vec![0xa9, 0x00, 0x00]);

      assert!(cpu.status & ZERO_FLAG == 0b10);
  }

  #[test]
  fn test_0xa9_lda_negative_flag() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
      cpu.load_and_run(vec![0xa9, 0x81, 0x00]);

      assert!(cpu.status & NEGATIVE_FLAG != 0);
  }

  #[test]
  fn test_lda_from_memory() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.mem_write(0x10, 0x55);

    cpu.load_and_run(vec![0xa5, 0x10, 0x00]);

    assert_eq!(cpu.register_a, 0x55);
  }

  #[test]
  fn test_0xaa_tax_move_a_to_x() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xaa, 0x00]);
    cpu.reset();
    cpu.register_a = 10;
    assert_eq!(cpu.register_a, 10);
    cpu.run();
    assert_eq!(cpu.register_x, 10);
  }

  #[test]
  fn test_inx_overflow() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xE8, 0xE8, 0x00]);
    cpu.reset();
    cpu.register_x = 0xff;
    cpu.run();

    assert_eq!(cpu.register_x, 1);
  }

  #[test]
  fn test_5_ops_work_together() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

    assert_eq!(cpu.register_x, 0xc1);
  }

  #[test]
  fn test_sta() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xa2, 0x85, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0xa2);
  }

  #[test]
  fn test_and() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xa2, 0x85, 0x10, 0xa9, 0x03, 0x2d, 0x10, 0x00, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_asl_shifts_bit_in_memory() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0x06, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x02);
  }

  #[test]
  fn test_asl_shifts_accumulator() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x0a, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_asl_shift_accumulator_fills_carry_bit() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x0a, 0x00]);
    assert_eq!(cpu.register_a, 0b1111_1110);
    assert!(cpu.status & CARRY_FLAG != 0);
  }

  #[test]
  fn test_asl_memory_fills_carry_bit() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0x06, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0b1111_1110);
    assert!(cpu.status & CARRY_FLAG != 0);
  }

  #[test]
  fn test_adc_immediate() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0x65, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_adc_sets_carry() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0xa9, 0x01, 0x65, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x00);
    assert!(cpu.status & CARRY_FLAG != 0);
    assert!(cpu.status & OVERFLOW_FLAG == 0);
  }

  #[test]
  fn test_adc_sets_overflow() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x50, 0x85, 0x10, 0x65, 0x10, 0x00]);
    assert!(cpu.status & CARRY_FLAG == 0);
    assert!(cpu.status & OVERFLOW_FLAG != 0);
  }

  #[test]
  fn test_bcc_branches_on_clear() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xfc, 0x69, 0x01, 0x90, 0xfc, 0x00]);
    assert_eq!(cpu.register_x, 0x00);
  }

  #[test]
  fn test_bit_set_neg_and_overflow() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xc0, 0x85, 0x10, 0x24, 0x10, 0x00]);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
    assert_ne!(cpu.status & OVERFLOW_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0)
  }

  #[test]
  fn test_bit_set_zero() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x00, 0x85, 0x10, 0x24, 0x10, 0x00]);
    assert_ne!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & OVERFLOW_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_clc() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x69, 0x01, 0x18, 0x00]);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_cld() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xd8, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | DECIMAL_MODE_FLAG;
    cpu.run();
    assert_eq!(cpu.status & DECIMAL_MODE_FLAG, 0);
  }

  #[test]
  fn test_cli() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0x58, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | INTERRUPT_DISABLE;
    cpu.run();
    assert_eq!(cpu.status & INTERRUPT_DISABLE, 0);
  }

  #[test]
  fn test_clv() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xb8, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | OVERFLOW_FLAG;
    cpu.run();
    assert_eq!(cpu.status & OVERFLOW_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_carry() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xa9, 0x03, 0xcd, 0x10, 0x00, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_zero() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_ne!(cpu.status & ZERO_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_negative_and_carry() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xa9, 0xff, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
  }

  #[test]
  fn test_cmp_set_negative_only(){
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xfe, 0x85, 0x10, 0xa9, 0xf0, 0xc5, 0x10, 0x00]);
    assert_ne!(cpu.status & NEGATIVE_FLAG, 0);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_cpx() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
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
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xa9, 0xf0, 0x85, 0x10, 0xc4, 0x10, 0x00]);
    cpu.reset();
    cpu.register_y = 0xfe;
    cpu.run();
    assert_ne!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & NEGATIVE_FLAG, 0);
    assert_eq!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_dec_by_one() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xc6, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x01);
  }

  #[test]
  fn test_dec_set_zero() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0xc6, 0x10, 0x00]);
    assert_ne!(cpu.status & ZERO_FLAG, 0);
  }

  #[test]
  fn test_dex() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xca, 0x00]);
    cpu.reset();
    cpu.register_x = 0x02;
    cpu.run();
    assert_eq!(cpu.register_x, 1);
  }

  #[test]
  fn test_dey() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0x88, 0x00]);
    cpu.reset();
    cpu.register_y = 0x02;
    cpu.run();
    assert_eq!(cpu.register_y, 1);
  }

  #[test]
  fn test_eor() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xaa, 0x85, 0x10, 0xa9, 0xff, 0x45, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x55);
  }

  #[test]
  fn test_inc() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x02, 0x85, 0x10, 0xe6, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x03);
  }

  #[test]
  fn test_iny() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xc8, 0x00]);
    cpu.reset();
    cpu.register_y = 0x01;
    cpu.run();
    assert_eq!(cpu.register_y, 0x02);
  }

  #[test]
  fn test_absolute_jump() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x00, 0x69, 0x01, 0x4c, 0x09, 0x06, 0x69, 0x01, 0x00]);
    assert_eq!(cpu.register_a, 0x01);
  }

  #[test]
  fn test_indirect_jump() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x0f, 0x85, 0x10, 0xa9, 0x80, 0x85, 0x11, 0xa9, 0x01, 0x6c, 0x10, 0x00, 0x69, 0x01, 0x69, 0x01, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_ldx() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa2, 0x03, 0x00]);
    assert_eq!(cpu.register_x, 0x03);
  }

  #[test]
  fn test_ldy() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x10, 0x85, 0x10, 0xa4, 0x10, 0x00]);
    assert_eq!(cpu.register_y, 0x10);
  }

  #[test]
  fn test_lsr_accumulator() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x4a, 0x00]);
    assert_eq!(cpu.register_a, 0);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_lsr_memory_zero_page_x() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xfe, 0x85, 0x10, 0xa2, 0x01, 0x56, 0x0f, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0x7f);
  }

  #[test]
  fn test_nop() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xea, 0x00]);
    assert_eq!(cpu.program_counter, 0x8002);
  }

  #[test]
  fn test_ora() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x85, 0x10, 0xa9, 0x02, 0x05, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x03);
  }

  #[test]
  fn test_pha() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x48, 0x48, 0x00]);
    assert_eq!(cpu.mem_read(0x01ff), 0x01);
    assert_eq!(cpu.mem_read(0x01fe), 0x01);
    assert_eq!(cpu.stack_ptr, 0xfd);
  }

  #[test]
  fn test_php() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0x08, 0x08, 0x00]);
    cpu.reset();
    cpu.status = 0b1100_1101;
    cpu.run();
    assert_eq!(cpu.mem_read(0x01ff), 0b1100_1101);
    assert_eq!(cpu.mem_read(0x01fe), 0b1100_1101);
    assert_eq!(cpu.mem_read(0x1fd), 0x00);
    assert_eq!(cpu.stack_ptr, 0xfd);
  }

  #[test]
  fn test_pla() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x48, 0x48, 0xa9, 0x02, 0x68, 0x00]);
    assert_eq!(cpu.mem_read(0x01ff), 0x01);
    //assert_eq!(cpu.mem_read(0x01fe), 0x00);
    assert_eq!(cpu.stack_ptr, 0xfe);
    assert_eq!(cpu.register_a, 0x01);
  }

  #[test]
  fn test_plp() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0x08, 0x08, 0x28, 0x00]);
    cpu.reset();
    cpu.status = 0b1100_1101;
    cpu.run();
    assert_eq!(cpu.mem_read(0x01ff), 0b1100_1101);
    //assert_eq!(cpu.mem_read(0x01fe), 0);
    assert_eq!(cpu.stack_ptr, 0xfe);
  }

  #[test]
  fn test_jsr_rts() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0x20, 0x09, 0x80, 0x20, 0x0c, 0x80, 0x20, 0x12, 0x80, 0xa2, 0x00, 0x60, 0xe8, 0xe0, 0x05, 0xd0, 0xfb, 0x60, 0x00]);
    assert_eq!(cpu.register_x, 0x05);
    assert_eq!(cpu.stack_ptr, 0xfd);
  }

  #[test]
  fn test_rol_accumulator() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x2a, 0x00]);
    assert_eq!(cpu.register_a, 0x02);
  }

  #[test]
  fn test_rol_accumulator_shift_carry() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x2a, 0x00]);
    assert_eq!(cpu.register_a, 0xfe);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_rol_acc_shift_carry_to_acc() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x2a, 0x2a, 0x00]);
    assert_eq!(cpu.register_a, 0xfd);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_rol_mem() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0x26, 0x10, 0x26, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0xfd);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_ror_accumulator() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x6a, 0x6a, 0x00]);
    assert_eq!(cpu.register_a, 0xbf);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_ror_mem() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xff, 0x85, 0x10, 0x66, 0x10, 0x66, 0x10, 0x00]);
    assert_eq!(cpu.mem_read(0x10), 0xbf);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }
  /*
  #[test]
  fn test_rti() {
    todo!()
  }*/

  #[test]
  fn test_sbc() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load(vec![0xa9, 0xf0, 0x85, 0x10, 0xa9, 0x50, 0xe5, 0x10, 0x00]);
    cpu.reset();
    cpu.status = cpu.status | CARRY_FLAG;
    cpu.run();
    assert_eq!(cpu.register_a, 0x60);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
    assert_eq!(cpu.status & OVERFLOW_FLAG, 0);
  }

  #[test]
  fn test_sbc_set_overflow() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xb0, 0x85, 0x10, 0xa9, 0x50, 0x38, 0xe5, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0xa0);
    assert_eq!(cpu.status & CARRY_FLAG, 0);
    assert_ne!(cpu.status & OVERFLOW_FLAG, 0);
  }

  #[test]
  fn test_sbc_sets_carry() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0xd0, 0x85, 0x10, 0xa9, 0xf0, 0xe5, 0x10, 0x00]);
    assert_eq!(cpu.register_a, 0x1f);
    assert_ne!(cpu.status & CARRY_FLAG, 0);
  }

  #[test]
  fn test_stx() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa2, 0x01, 0x86, 0x12, 0x00]);
    assert_eq!(cpu.register_x, 1);
    assert_eq!(cpu.mem_read(0x12), 1);
  }

  #[test]
  fn test_sty() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa0, 0x01, 0x84, 0x12, 0x00]);
    assert_eq!(cpu.register_y, 1);
    assert_eq!(cpu.mem_read(0x12), 1);
  }

  #[test]
  fn test_tay() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0xa8, 0x00]);
    assert_eq!(cpu.register_y, 1);
  }

  #[test]
  fn test_tsx() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa9, 0x01, 0x48, 0xba, 0x00]);
    assert_eq!(cpu.stack_ptr, 0xfe);
    assert_eq!(cpu.register_x, 0xfe);
  }

  #[test]
  fn test_txa() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa2, 0x01, 0x8a, 0x00]);
    assert_eq!(cpu.register_x, 0x01);
  }

  #[test]
  fn test_tya() {
    let bus = Bus::new(test::test_rom());
    let mut cpu = CPU::new(bus);
    cpu.load_and_run(vec![0xa0, 0x01, 0x98, 0x00]);
    assert_eq!(cpu.register_y, 0x01);
  }
}
