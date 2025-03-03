// z80_cpu.rs

//!
//! Zilog Z80 CPU Core Implementation in Rust
//!
//! This module provides an emulation of the Zilog Z80 microprocessor, a widely used 8-bit CPU
//! introduced in 1976. The Z80 features a 16-bit address bus (64KB address space), an 8-bit data
//! bus, and a rich instruction set with 158 opcodes, including undocumented ones. This
//! implementation includes the CPU's registers, instruction execution, interrupt handling, and
//! I/O operations, aiming for compatibility with the official Z80 specifications.
//!
//! Key Features:
//! - Full register set: main (A, F, B, C, D, E, H, L), alternate, index (IX, IY), SP, PC, I, R
//! - Flag register (F) with S, Z, H, P/V, N, C flags
//! - Support for standard opcodes, CB/DD/ED/FD prefixes
//! - Interrupt modes (IM 0, IM 1, IM 2) and NMI handling
//! - Cycle-accurate execution for implemented instructions
//!
//! Dependencies:
//! - `memory.rs`: Provides the `Memory` trait for memory access
//!
//! Usage:
//! Create a `Z80` instance with `Z80::new()`, then use `step()` to execute instructions,
//! interfacing with memory and I/O devices via traits.
//!
//! Limitations:
//! - Some opcodes (e.g., IN, OUT) are unimplemented; they panic with `unimplemented!()`.
//! - Undocumented opcodes and edge cases may not be fully supported yet.
//!

// use crate::memory::Memory;

pub trait Z80Memory {
    fn read(&self, address: u16) -> u8;
    fn write(&mut self, address: u16, value: u8);
}

// Constants for flag bits in the F register
pub const FLAG_C: u8 = 0b00000001;  // Carry flag (bit 0)
pub const FLAG_N: u8 = 0b00000010;  // Add/Subtract flag (bit 1)
pub const FLAG_PV: u8 = 0b00000100; // Parity/Overflow flag (bit 2)
pub const FLAG_H: u8 = 0b00010000;  // Half-carry flag (bit 4)
pub const FLAG_Z: u8 = 0b01000000;  // Zero flag (bit 6)
pub const FLAG_S: u8 = 0b10000000;  // Sign flag (bit 7)

/// Represents the complete register set of the Z80 CPU.
pub struct Registers {
    pub a: u8,      // Accumulator
    pub f: u8,      // Flag register
    pub b: u8,      // B register
    pub c: u8,      // C register
    pub d: u8,      // D register
    pub e: u8,      // E register
    pub h: u8,      // H register (high byte of HL)
    pub l: u8,      // L register (low byte of HL)
    pub a_alt: u8,  // Alternate accumulator
    pub f_alt: u8,  // Alternate flag register
    pub b_alt: u8,  // Alternate B register
    pub c_alt: u8,  // Alternate C register
    pub d_alt: u8,  // Alternate D register
    pub e_alt: u8,  // Alternate E register
    pub h_alt: u8,  // Alternate H register
    pub l_alt: u8,  // Alternate L register
    pub ix: u16,    // Index register IX
    pub iy: u16,    // Index register IY
    pub sp: u16,    // Stack pointer
    pub pc: u16,    // Program counter
    pub i: u8,      // Interrupt vector register
    pub r: u8,      // Memory refresh register
}

impl Registers {
    /// Creates a new `Registers` instance with all values initialized to zero.
    pub fn new() -> Self {
        Registers {
            a: 0, f: 0, b: 0, c: 0, d: 0, e: 0, h: 0, l: 0,
            a_alt: 0, f_alt: 0, b_alt: 0, c_alt: 0, d_alt: 0, e_alt: 0, h_alt: 0, l_alt: 0,
            ix: 0, iy: 0, sp: 0, pc: 0, i: 0, r: 0,
        }
    }

    /// Gets the 16-bit BC register pair.
    pub fn get_bc(&self) -> u16 { ((self.b as u16) << 8) | self.c as u16 }

    /// Sets the 16-bit BC register pair.
    pub fn set_bc(&mut self, value: u16) { self.b = (value >> 8) as u8; self.c = value as u8; }

    /// Gets the 16-bit DE register pair.
    pub fn get_de(&self) -> u16 { ((self.d as u16) << 8) | self.e as u16 }

    /// Sets the 16-bit DE register pair.
    pub fn set_de(&mut self, value: u16) { self.d = (value >> 8) as u8; self.e = value as u8; }

    /// Gets the 16-bit HL register pair.
    pub fn get_hl(&self) -> u16 { ((self.h as u16) << 8) | self.l as u16 }

    /// Sets the 16-bit HL register pair.
    pub fn set_hl(&mut self, value: u16) { self.h = (value >> 8) as u8; self.l = value as u8; }

    /// Gets the 16-bit AF register pair.
    pub fn get_af(&self) -> u16 { ((self.a as u16) << 8) | self.f as u16 }

    /// Sets the 16-bit AF register pair.
    pub fn set_af(&mut self, value: u16) { self.a = (value >> 8) as u8; self.f = value as u8; }

    /// Sets a flag in the F register.
    pub fn set_flag(&mut self, flag: u8, value: bool) {
        if value { self.f |= flag; } else { self.f &= !flag; }
    }

    /// Gets the state of a flag in the F register.
    pub fn get_flag(&self, flag: u8) -> bool { self.f & flag != 0 }
}

/// Trait defining the interface for I/O devices in the Z80 emulator.
pub trait IoDevice {
    /// Reads a byte from the specified 16-bit port.
    fn read(&self, port: u16) -> u8;

    /// Writes a byte to the specified 16-bit port.
    fn write(&mut self, port: u16, value: u8);
}

/// A dummy I/O device that returns 0 on reads and ignores writes.
pub struct DummyIoDevice;

impl IoDevice for DummyIoDevice {
    fn read(&self, _port: u16) -> u8 { 0 }
    fn write(&mut self, _port: u16, _value: u8) {}
}

/// Represents the Z80 CPU, encapsulating its state and execution logic.
pub struct Z80 {
    registers: Registers, // CPU registers
    halted: bool,        // Halt state
    iff1: bool,          // Interrupt Flip-Flop 1 (enabled/disabled)
    iff2: bool,          // Interrupt Flip-Flop 2 (for NMI)
    im: u8,              // Interrupt mode (0, 1, or 2)
    cycles: u64,         // Total cycles elapsed
}

impl Z80 {
    /// Creates a new `Z80` instance with default values.
    pub fn new() -> Self {
        Z80 {
            registers: Registers::new(),
            halted: false,
            iff1: false,
            iff2: false,
            im: 0,
            cycles: 0,
        }
    }

    /// Executes one CPU instruction, returning the number of cycles consumed.
    pub fn step(&mut self, memory: &mut dyn Z80Memory, io: &mut dyn IoDevice) -> u8 {
        if self.halted {
            self.registers.r = self.registers.r.wrapping_add(1);
            return 4; // HALT takes 4 cycles
        }
        let opcode = self.fetch_byte(memory);
        let cycles = self.execute(opcode, memory, io);
        self.cycles += cycles as u64;
        cycles
    }

    /// Fetches a byte from memory at PC, incrementing PC and R.
    pub fn fetch_byte(&mut self, memory: &dyn Z80Memory) -> u8 {
        let byte = memory.read(self.registers.pc);
        self.registers.pc = self.registers.pc.wrapping_add(1);
        self.registers.r = self.registers.r.wrapping_add(1);
        byte
    }

    /// Fetches a 16-bit word from memory, incrementing PC twice.
    pub fn fetch_word(&mut self, memory: &dyn Z80Memory) -> u16 {
        let low = self.fetch_byte(memory) as u16;
        let high = self.fetch_byte(memory) as u16;
        (high << 8) | low
    }

    /// Gets a register value by index (0-7: B, C, D, E, H, L, (HL), A).
    pub fn get_register(&self, r: u8, memory: &dyn Z80Memory) -> u8 {
        match r {
            0 => self.registers.b,
            1 => self.registers.c,
            2 => self.registers.d,
            3 => self.registers.e,
            4 => self.registers.h,
            5 => self.registers.l,
            6 => memory.read(self.registers.get_hl()),
            7 => self.registers.a,
            _ => unreachable!("Invalid register index"),
        }
    }

    /// Sets a register value by index (0-7: B, C, D, E, H, L, (HL), A).
    pub fn set_register(&mut self, r: u8, value: u8, memory: &mut dyn Z80Memory) {
        match r {
            0 => self.registers.b = value,
            1 => self.registers.c = value,
            2 => self.registers.d = value,
            3 => self.registers.e = value,
            4 => self.registers.h = value,
            5 => self.registers.l = value,
            6 => memory.write(self.registers.get_hl(), value),
            7 => self.registers.a = value,
            _ => unreachable!("Invalid register index"),
        }
    }

    /// Pushes the PC onto the stack.
    pub fn push_pc(&mut self, memory: &mut dyn Z80Memory) {
        self.registers.sp = self.registers.sp.wrapping_sub(2);
        memory.write(self.registers.sp, self.registers.pc as u8);
        memory.write(self.registers.sp + 1, (self.registers.pc >> 8) as u8);
    }

    /// Pops the PC from the stack.
    pub fn pop_pc(&mut self, memory: &dyn Z80Memory) {
        let low = memory.read(self.registers.sp) as u16;
        let high = memory.read(self.registers.sp + 1) as u16;
        self.registers.pc = (high << 8) | low;
        self.registers.sp = self.registers.sp.wrapping_add(2);
    }

    /// Executes the given opcode, returning the number of cycles.
    pub fn execute(&mut self, opcode: u8, memory: &mut dyn Z80Memory, io: &mut dyn IoDevice) -> u8 {
        match opcode {
            // No Operation: Does nothing, takes 4 cycles
            0x00 => 4, // NOP

            // Load BC with immediate 16-bit value nn from memory (PC+1, PC+2)
            0x01 => { let nn = self.fetch_word(memory); self.registers.set_bc(nn); 10 }, // LD BC, nn

            // Store accumulator A to memory location pointed to by BC
            0x02 => { memory.write(self.registers.get_bc(), self.registers.a); 7 }, // LD (BC), A

            // Increment register B, setting S, Z, H, PV flags (N reset, C unaffected)
            0x04 => { self.registers.b = self.inc_8bit(self.registers.b); 4 }, // INC B

            // Decrement register B, setting S, Z, H, PV flags (N set, C unaffected)
            0x05 => { self.registers.b = self.dec_8bit(self.registers.b); 4 }, // DEC B

            // Load register B with immediate 8-bit value n from memory (PC+1)
            0x06 => {
                let n = self.fetch_byte(memory); // Fetch the immediate value
                self.registers.b = n;            // Load it into register B
                7                                // Return the number of cycles
            }, // LD B, n

            // Rotate Left Circular Accumulator: Bit 7 to bit 0 and C flag, H/N reset
            0x07 => {
                let a = self.registers.a;
                let carry = (a & 0x80) != 0;
                self.registers.a = (a << 1) | if carry { 1 } else { 0 };
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, carry);
                4
            }, // RLCA

            // Exchange AF with AF': Swap accumulator and flags with shadow registers
            0x08 => {
                let temp_a = self.registers.a;
                let temp_f = self.registers.f;
                self.registers.a = self.registers.a_alt;
                self.registers.f = self.registers.f_alt;
                self.registers.a_alt = temp_a;
                self.registers.f_alt = temp_f;
                4
            }, // EX AF, AF'

            // Add 16-bit register pair BC to HL, setting H and C flags (others unaffected)
            0x09 => {
                let hl = self.registers.get_hl();
                let bc = self.registers.get_bc();
                let (result, carry) = hl.overflowing_add(bc);
                let half_carry = ((hl & 0x0FFF) + (bc & 0x0FFF)) > 0x0FFF;
                self.registers.set_hl(result);
                self.registers.set_flag(FLAG_H, half_carry);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, carry);
                11
            }, // ADD HL, BC

            // Load accumulator A from memory location pointed to by BC
            0x0A => {
                let bc = self.registers.get_bc();
                self.registers.a = memory.read(bc);
                7
            }, // LD A, (BC)

            // Increment register C, setting S, Z, H, PV flags (N reset, C unaffected)
            0x0C => { self.registers.c = self.inc_8bit(self.registers.c); 4 }, // INC C

            // Decrement register C, setting S, Z, H, PV flags (N set, C unaffected)
            0x0D => { self.registers.c = self.dec_8bit(self.registers.c); 4 }, // DEC C

            // Load register C with immediate 8-bit value n from memory (PC+1)
            0x0E => { self.registers.c = self.fetch_byte(memory); 7 }, // LD C, n

            // Rotate Right Circular Accumulator: Bit 0 to bit 7 and C flag, H/N reset
            0x0F => {
                let a = self.registers.a;
                let carry = (a & 0x01) != 0;
                self.registers.a = (a >> 1) | if carry { 0x80 } else { 0 };
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, carry);
                4
            }, // RRCA

            // Decrement B and jump relative if B != 0 (e is signed offset from PC+2)
            0x10 => {
                self.registers.b = self.registers.b.wrapping_sub(1);
                let e = self.fetch_byte(memory) as i8;
                if self.registers.b != 0 {
                    self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                    13
                } else {
                    8
                }
            }, // DJNZ e

            // Load DE with immediate 16-bit value nn from memory (PC+1, PC+2)
            0x11 => { let nn = self.fetch_word(memory); self.registers.set_de(nn); 10 }, // LD DE, nn

            // Store accumulator A to memory location pointed to by DE
            0x12 => { memory.write(self.registers.get_de(), self.registers.a); 7 }, // LD (DE), A

            // Increment register D, setting S, Z, H, PV flags (N reset, C unaffected)
            0x14 => { self.registers.d = self.inc_8bit(self.registers.d); 4 }, // INC D

            // Decrement register D, setting S, Z, H, PV flags (N set, C unaffected)
            0x15 => { self.registers.d = self.dec_8bit(self.registers.d); 4 }, // DEC D

            // Load register D with immediate 8-bit value n from memory (PC+1)
            0x16 => { let n = self.fetch_byte(memory); self.registers.d = n; 7 }, // LD D, n

            // Rotate Left Accumulator through Carry: Bit 7 to C, C to bit 0, H/N reset
            0x17 => {
                let a = self.registers.a;
                let old_carry = if self.registers.get_flag(FLAG_C) { 1 } else { 0 };
                let new_carry = (a & 0x80) != 0;
                self.registers.a = (a << 1) | old_carry;
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, new_carry);
                4
            }, // RLA

            // Jump relative: Add signed offset e to PC (PC+2 + e)
            0x18 => {
                let e = self.fetch_byte(memory) as i8;
                self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                12
            }, // JR e

            // Load accumulator A from memory location pointed to by DE
            0x1A => {
                let de = self.registers.get_de();
                self.registers.a = memory.read(de);
                7
            }, // LD A, (DE)

            // Increment register E, setting S, Z, H, PV flags (N reset, C unaffected)
            0x1C => { self.registers.e = self.inc_8bit(self.registers.e); 4 }, // INC E

            // Decrement register E, setting S, Z, H, PV flags (N set, C unaffected)
            0x1D => { self.registers.e = self.dec_8bit(self.registers.e); 4 }, // DEC E

            // Load register E with immediate 8-bit value n from memory (PC+1)
            0x1E => { let n = self.fetch_byte(memory); self.registers.e = n; 7 }, // LD E, n

            // Rotate Right Accumulator through Carry: Bit 0 to C, C to bit 7, H/N reset
            0x1F => {
                let a = self.registers.a;
                let old_carry = if self.registers.get_flag(FLAG_C) { 0x80 } else { 0 };
                let new_carry = (a & 0x01) != 0;
                self.registers.a = (a >> 1) | old_carry;
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, new_carry);
                4
            }, // RRA

            // Jump relative if Zero flag is reset (NZ): PC+2 + e if Z = 0
            0x20 => {
                let e = self.fetch_byte(memory) as i8;
                if !self.registers.get_flag(FLAG_Z) {
                    self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                    12
                } else {
                    7
                }
            }, // JR NZ, e

            // Load HL with immediate 16-bit value nn from memory (PC+1, PC+2)
            0x21 => { let nn = self.fetch_word(memory); self.registers.set_hl(nn); 10 }, // LD HL, nn

            // Store HL to memory at address nn (little-endian: L at nn, H at nn+1)
            0x22 => {
                let nn = self.fetch_word(memory);
                let hl = self.registers.get_hl();
                memory.write(nn, (hl & 0xFF) as u8);
                memory.write(nn.wrapping_add(1), (hl >> 8) as u8);
                16
            }, // LD (nn), HL

            // Increment register H, setting S, Z, H, PV flags (N reset, C unaffected)
            0x23 => {
                let hl = self.registers.get_hl();       // Get current HL value
                let new_hl = hl.wrapping_add(1);        // Increment with wrapping
                self.registers.set_hl(new_hl);          // Set new HL value
                6                                       // Return 6 cycles
            }, // INC HL

            // Increment register H, setting S, Z, H, PV flags (N reset, C unaffected)
            0x24 => { self.registers.h = self.inc_8bit(self.registers.h); 4 }, // INC H

            // Decrement register H, setting S, Z, H, PV flags (N set, C unaffected)
            0x25 => { self.registers.h = self.dec_8bit(self.registers.h); 4 }, // DEC H

            // Load register H with immediate 8-bit value n from memory (PC+1)
            0x26 => { let n = self.fetch_byte(memory); self.registers.h = n; 7 }, // LD H, n

            // Decimal Adjust Accumulator: Adjust A for BCD arithmetic after ADD/SUB
            0x27 => {
                let mut a = self.registers.a;
                let mut correction = 0;
                let carry = self.registers.get_flag(FLAG_C);
                let half_carry = self.registers.get_flag(FLAG_H);
                let subtract = self.registers.get_flag(FLAG_N);

                if half_carry || (!subtract && (a & 0x0F) > 9) {
                    correction |= 0x06;
                }
                if carry || (!subtract && a > 0x99) || (subtract && ((a & 0xF0) > 0x90)) {
                    correction |= 0x60;
                }
                if subtract {
                    a = a.wrapping_sub(correction);
                } else {
                    a = a.wrapping_add(correction);
                }
                let new_carry = carry || (correction & 0x60) != 0;
                self.registers.set_flag(FLAG_S, a & 0x80 != 0);
                self.registers.set_flag(FLAG_Z, a == 0);
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_PV, Self::parity(a));
                self.registers.set_flag(FLAG_C, new_carry);
                self.registers.a = a;
                4
            }, // DAA

            // Jump relative if Zero flag is set (Z): PC+2 + e if Z = 1
            0x28 => {
                let e = self.fetch_byte(memory) as i8;
                if self.registers.get_flag(FLAG_Z) {
                    self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                    12
                } else {
                    7
                }
            }, // JR Z, e

            // Add 16-bit register pair HL to HL (double HL), setting H and C flags
            0x29 => {
                let hl = self.registers.get_hl();
                let (result, carry) = hl.overflowing_add(hl);
                let half_carry = ((hl & 0x0FFF) + (hl & 0x0FFF)) > 0x0FFF;
                self.registers.set_hl(result);
                self.registers.set_flag(FLAG_H, half_carry);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, carry);
                11
            }, // ADD HL, HL

            // Load HL from memory at address nn (little-endian: L from nn, H from nn+1)
            0x2A => {
                let nn = self.fetch_word(memory);
                let low = memory.read(nn);
                let high = memory.read(nn.wrapping_add(1));
                self.registers.set_hl((high as u16) << 8 | low as u16);
                16
            }, // LD HL, (nn)

            // Increment register L, setting S, Z, H, PV flags (N reset, C unaffected)
            0x2C => { self.registers.l = self.inc_8bit(self.registers.l); 4 }, // INC L

            // Decrement register L, setting S, Z, H, PV flags (N set, C unaffected)
            0x2D => { self.registers.l = self.dec_8bit(self.registers.l); 4 }, // DEC L

            // Load register L with immediate 8-bit value n from memory (PC+1)
            0x2E => { let n = self.fetch_byte(memory); self.registers.l = n; 7 }, // LD L, n

            // Complement Accumulator: Invert all bits of A, set H and N flags
            0x2F => {
                self.registers.a = !self.registers.a;
                self.registers.set_flag(FLAG_H, true);
                self.registers.set_flag(FLAG_N, true);
                4
            }, // CPL

            // Jump relative if Carry flag is reset (NC): PC+2 + e if C = 0
            0x30 => {
                let e = self.fetch_byte(memory) as i8;
                if !self.registers.get_flag(FLAG_C) {
                    self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                    12
                } else {
                    7
                }
            }, // JR NC, e

            // Load Stack Pointer with immediate 16-bit value nn from memory (PC+1, PC+2)
            0x31 => { self.registers.sp = self.fetch_word(memory); 10 }, // LD SP, nn

            // Store accumulator A to memory at address nn (PC+1, PC+2)
            0x32 => {
                let nn = self.fetch_word(memory);
                memory.write(nn, self.registers.a);
                13
            }, // LD (nn), A

            // Increment value at (HL), setting S, Z, H, PV flags (N reset, C unaffected)
            0x34 => {
                let hl = self.registers.get_hl();
                let value = memory.read(hl);
                let new_value = self.inc_8bit(value);
                memory.write(hl, new_value);
                11
            }, // INC (HL)

            // Decrement value at (HL), setting S, Z, H, PV flags (N set, C unaffected)
            0x35 => {
                let hl = self.registers.get_hl();
                let value = memory.read(hl);
                let new_value = self.dec_8bit(value);
                memory.write(hl, new_value);
                11
            }, // DEC (HL)

            // Load memory at (HL) with immediate 8-bit value n from memory (PC+1)
            0x36 => {
                let n = self.fetch_byte(memory);
                let hl = self.registers.get_hl();
                memory.write(hl, n);
                10
            }, // LD (HL), n

            // Set Carry Flag: C flag set, H and N flags reset
            0x37 => {
                self.registers.set_flag(FLAG_H, false);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, true);
                4
            }, // SCF

            // Jump relative if Carry flag is set (C): PC+2 + e if C = 1
            0x38 => {
                let e = self.fetch_byte(memory) as i8;
                if self.registers.get_flag(FLAG_C) {
                    self.registers.pc = self.registers.pc.wrapping_add(e as u16);
                    12
                } else {
                    7
                }
            }, // JR C, e

            // Add 16-bit register pair DE to HL, setting H and C flags
            0x39 => {
                let hl = self.registers.get_hl();
                let de = self.registers.get_de();
                let (result, carry) = hl.overflowing_add(de);
                let half_carry = ((hl & 0x0FFF) + (de & 0x0FFF)) > 0x0FFF;
                self.registers.set_hl(result);
                self.registers.set_flag(FLAG_H, half_carry);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, carry);
                11
            }, // ADD HL, DE

            // Load accumulator A from memory at address nn (PC+1, PC+2)
            0x3A => {
                let nn = self.fetch_word(memory);
                self.registers.a = memory.read(nn);
                13
            }, // LD A, (nn)

            // Increment register A, setting S, Z, H, PV flags (N reset, C unaffected)
            0x3C => { self.registers.a = self.inc_8bit(self.registers.a); 4 }, // INC A

            // Decrement register A, setting S, Z, H, PV flags (N set, C unaffected)
            0x3D => { self.registers.a = self.dec_8bit(self.registers.a); 4 }, // DEC A

            // Load register A with immediate 8-bit value n from memory (PC+1)
            0x3E => { self.registers.a = self.fetch_byte(memory); 7 }, // LD A, n

            // Complement Carry Flag: Invert C flag, set H to old C, N reset
            0x3F => {
                let carry = self.registers.get_flag(FLAG_C);
                self.registers.set_flag(FLAG_H, carry);
                self.registers.set_flag(FLAG_N, false);
                self.registers.set_flag(FLAG_C, !carry);
                4
            }, // CCF

            // Load register-to-register or memory at (HL): 0x40-0x7F except 0x76 (HALT)
            0x40..=0x7F => {
                if opcode == 0x76 {
                    self.halted = true;
                    4 // HALT: Halt CPU until interrupt
                } else {
                    let dest = (opcode >> 3) & 0x07; // Bits 3-5: destination register
                    let src = opcode & 0x07;          // Bits 0-2: source register
                    let value = self.get_register(src, memory);
                    self.set_register(dest, value, memory);
                    if dest == 6 || src == 6 {
                        7 // Memory access via (HL) takes 7 cycles
                    } else {
                        4 // Register-to-register takes 4 cycles
                    }
                }
            },

            // Add register or (HL) to A, setting all flags (H for carry from bit 3)
            0x80..=0x87 => self.add_a_r(self.get_register(opcode & 0x07, memory)), // ADD A, r

            // Add register or (HL) plus Carry to A, setting all flags
            0x88..=0x8F => {
                let r = self.get_register(opcode & 0x07, memory);
                self.adc_a_r(r);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // ADC A, r

            // Subtract register or (HL) from A, setting all flags (H for borrow)
            0x90..=0x97 => self.sub_a_r(self.get_register(opcode & 0x07, memory)), // SUB r

            // Subtract register or (HL) plus Carry from A, setting all flags
            0x98..=0x9F => {
                let r = self.get_register(opcode & 0x07, memory);
                self.sbc_a_r(r);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // SBC A, r

            // Bitwise AND of register or (HL) with A, setting S, Z, H, PV (N/C reset)
            0xA0..=0xA7 => {
                let r = self.get_register(opcode & 0x07, memory);
                self.and_a_r(r);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // AND r

            // Bitwise XOR of register or (HL) with A, setting S, Z, PV (H/N/C reset)
            0xA8..=0xAF => {
                let r = self.get_register(opcode & 0x07, memory);
                self.xor_a_r(r);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // XOR r

            // Bitwise OR of register or (HL) with A, setting S, Z, PV (H/N/C reset)
            0xB0..=0xB7 => {
                let r = self.get_register(opcode & 0x07, memory);
                self.or_a_r(r);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // OR r

            // Compare register or (HL) with A (A - r), setting all flags, A unchanged
            0xB8..=0xBF => {
                let r = self.get_register(opcode & 0x07, memory);
                let a = self.registers.a;
                let result = a.wrapping_sub(r);
                let half_carry = (a & 0x0F) < (r & 0x0F);
                let overflow = ((a ^ r) & 0x80 != 0) && ((a ^ result) & 0x80 != 0);
                let carry = a < r;
                self.registers.set_flag(FLAG_S, result & 0x80 != 0);
                self.registers.set_flag(FLAG_Z, result == 0);
                self.registers.set_flag(FLAG_H, half_carry);
                self.registers.set_flag(FLAG_PV, overflow);
                self.registers.set_flag(FLAG_N, true);
                self.registers.set_flag(FLAG_C, carry);
                if (opcode & 0x07) == 6 { 7 } else { 4 } // (HL) takes 7, others 4 cycles
            }, // CP r

            // Pop BC from stack: C from (SP), B from (SP+1), then SP += 2
            0xC1 => {
                self.registers.c = memory.read(self.registers.sp);
                self.registers.b = memory.read(self.registers.sp + 1);
                self.registers.sp = self.registers.sp.wrapping_add(2);
                10
            }, // POP BC

            // Jump if Zero flag is reset (NZ): PC = nn if Z = 0 (always 10 cycles)
            0xC2 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_Z) {
                    self.registers.pc = nn;
                }
                10
            }, // JP NZ, nn

            // Jump absolute: Set PC to 16-bit address nn from memory (PC+1, PC+2)
            0xC3 => { self.registers.pc = self.fetch_word(memory); 10 }, // JP nn

            // Call subroutine if Zero flag is reset (NZ): Push PC, PC = nn if Z = 0
            0xC4 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_Z) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL NZ, nn

            // Push BC to stack: SP -= 2, (SP+1) = B, (SP) = C
            0xC5 => {
                self.registers.sp = self.registers.sp.wrapping_sub(2);
                memory.write(self.registers.sp + 1, self.registers.b);
                memory.write(self.registers.sp, self.registers.c);
                11 // Note: Corrected to 11 cycles per Z80 manual
            }, // PUSH BC

            // Add immediate value n to A, setting all flags
            0xC6 => {
                let n = self.fetch_byte(memory);
                self.add_a_r(n);
                7 // Clock cycles for ADD A, n
            }, // ADD A, n

            // Restart at 0x00: Push PC, set PC to 0x0000
            0xC7 => {
                self.push_pc(memory);
                self.registers.pc = 0x0000;
                11
            }, // RST 00H

            // Return if Zero flag is reset (NZ): Pop PC if Z = 0
            0xC0 => {
                if !self.registers.get_flag(FLAG_Z) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET NZ

            // Pop HL from stack: L from (SP), H from (SP+1), then SP += 2
            0xE1 => {
                self.registers.l = memory.read(self.registers.sp);
                self.registers.h = memory.read(self.registers.sp + 1);
                self.registers.sp = self.registers.sp.wrapping_add(2);
                10
            }, // POP HL

            // Jump if Zero flag is set (Z): PC = nn if Z = 1 (always 10 cycles)
            0xCA => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_Z) {
                    self.registers.pc = nn;
                }
                10
            }, // JP Z, nn

            // CB prefix: Fetch next byte and execute bit operation
            0xCB => { let cb_opcode = self.fetch_byte(memory); self.execute_cb(cb_opcode, memory) },

            // Call subroutine if Zero flag is set (Z): Push PC, PC = nn if Z = 1
            0xCC => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_Z) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL Z, nn

            // Call subroutine: Push PC, set PC to nn
            0xCD => {
                let nn = self.fetch_word(memory);
                self.push_pc(memory);
                self.registers.pc = nn;
                17
            }, // CALL nn

            // Add immediate value n plus Carry to A, setting all flags
            0xCE => {
                let n = self.fetch_byte(memory);
                self.adc_a_r(n);
                7
            }, // ADC A, n

            // Restart at 0x08: Push PC, set PC to 0x0008
            0xCF => {
                self.push_pc(memory);
                self.registers.pc = 0x0008;
                11
            }, // RST 08H

            // Return if Zero flag is set (Z): Pop PC if Z = 1
            0xC8 => {
                if self.registers.get_flag(FLAG_Z) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET Z

            // Return: Pop PC from stack
            0xC9 => { self.pop_pc(memory); 10 }, // RET

            // Jump if Carry flag is reset (NC): PC = nn if C = 0
            0xD2 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_C) {
                    self.registers.pc = nn;
                }
                10
            }, // JP NC, nn

            // Output A to port n: Port address from (PC+1)
            0xD3 => {
                let n = self.fetch_byte(memory); // Get the port number from memory
                io.write(n as u16, self.registers.a); // Write A's value to the port
                11 // Return the number of clock cycles
            }, // OUT (n), A

            // Call subroutine if Carry flag is reset (NC): Push PC, PC = nn if C = 0
            0xD4 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_C) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL NC, nn

            // Push DE to stack: SP -= 2, (SP+1) = D, (SP) = E
            0xD5 => {
                self.registers.sp = self.registers.sp.wrapping_sub(2);
                memory.write(self.registers.sp + 1, self.registers.d);
                memory.write(self.registers.sp, self.registers.e);
                11
            }, // PUSH DE

            // Subtract immediate value n from A, setting all flags
            0xD6 => {
                let n = self.fetch_byte(memory);
                self.sub_a_r(n);
                7 // Clock cycles for SUB n
            }, // SUB n

            // Restart at 0x10: Push PC, set PC to 0x0010
            0xD7 => {
                self.push_pc(memory);
                self.registers.pc = 0x0010;
                11
            }, // RST 10H

            // Return if Carry flag is reset (NC): Pop PC if C = 0
            0xD0 => {
                if !self.registers.get_flag(FLAG_C) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET NC

            // Pop DE from stack: E from (SP), D from (SP+1), then SP += 2
            0xD1 => {
                self.registers.e = memory.read(self.registers.sp);
                self.registers.d = memory.read(self.registers.sp + 1);
                self.registers.sp = self.registers.sp.wrapping_add(2);
                10
            }, // POP DE

            // Jump if Carry flag is set (C): PC = nn if C = 1
            0xDA => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_C) {
                    self.registers.pc = nn;
                }
                10
            }, // JP C, nn

            // Input from port n to A: Port address from (PC+1)
            0xDB => {
                let n = self.fetch_byte(memory);
                self.registers.a = io.read(n as u16);
                11
            }, // IN A, (n)

            // Call subroutine if Carry flag is set (C): Push PC, PC = nn if C = 1
            0xDC => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_C) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL C, nn

            // DD prefix: Fetch next byte and execute IX-related instruction
            0xDD => { let dd_opcode = self.fetch_byte(memory); self.execute_dd(dd_opcode, memory, io) },

            // Subtract immediate value n plus Carry from A, setting all flags
            0xDE => {
                let n = self.fetch_byte(memory);
                self.sbc_a_r(n);
                7
            }, // SBC A, n

            // Restart at 0x18: Push PC, set PC to 0x0018
            0xDF => {
                self.push_pc(memory);
                self.registers.pc = 0x0018;
                11
            }, // RST 18H

            // Return if Carry flag is set (C): Pop PC if C = 1
            0xD8 => {
                if self.registers.get_flag(FLAG_C) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET C

            // Exchange DE with HL: Swap register pairs
            0xEB => {
                let temp_d = self.registers.d;
                let temp_e = self.registers.e;
                self.registers.d = self.registers.h;
                self.registers.e = self.registers.l;
                self.registers.h = temp_d;
                self.registers.l = temp_e;
                4
            }, // EX DE, HL

            // Jump if Parity Odd (PO): PC = nn if PV = 0
            0xE2 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_PV) {
                    self.registers.pc = nn;
                }
                10
            }, // JP PO, nn

            // Jump indirect via HL: PC = HL
            0xE9 => {
                self.registers.pc = self.registers.get_hl();
                4
            }, // JP (HL)

            // Call subroutine if Parity Odd (PO): Push PC, PC = nn if PV = 0
            0xE4 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_PV) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL PO, nn

            // Push HL to stack: SP -= 2, (SP+1) = H, (SP) = L
            0xE5 => {
                self.registers.sp = self.registers.sp.wrapping_sub(2);
                memory.write(self.registers.sp + 1, self.registers.h);
                memory.write(self.registers.sp, self.registers.l);
                11
            }, // PUSH HL

            // Bitwise AND of immediate n with A, setting S, Z, H, PV (N/C reset)
            0xE6 => {
                let n = self.fetch_byte(memory);
                self.and_a_r(n);
                7
            }, // AND n

            // Restart at 0x20: Push PC, set PC to 0x0020
            0xE7 => {
                self.push_pc(memory);
                self.registers.pc = 0x0020;
                11
            }, // RST 20H

            // Return if Parity Odd (PO): Pop PC if PV = 0
            0xE0 => {
                if !self.registers.get_flag(FLAG_PV) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET PO

            // Exchange (SP) with HL: Swap HL with top of stack
            0xE3 => {
                let low = memory.read(self.registers.sp);
                let high = memory.read(self.registers.sp + 1);
                memory.write(self.registers.sp, self.registers.l);
                memory.write(self.registers.sp + 1, self.registers.h);
                self.registers.l = low;
                self.registers.h = high;
                19
            }, // EX (SP), HL

            // Jump if Parity Even (PE): PC = nn if PV = 1
            0xEA => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_PV) {
                    self.registers.pc = nn;
                }
                10
            }, // JP PE, nn

            // Bitwise XOR of immediate n with A, setting S, Z, PV (H/N/C reset)
            0xEE => {
                let n = self.fetch_byte(memory);
                self.xor_a_r(n);
                7
            }, // XOR n

            // Restart at 0x28: Push PC, set PC to 0x0028
            0xEF => {
                self.push_pc(memory);
                self.registers.pc = 0x0028;
                11
            }, // RST 28H

            // Return if Parity Even (PE): Pop PC if PV = 1
            0xE8 => {
                if self.registers.get_flag(FLAG_PV) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET PE

            // Call subroutine if Parity Even (PE): Push PC, PC = nn if PV = 1
            0xEC => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_PV) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL PE, nn

            // Pop AF from stack: F from (SP), A from (SP+1), then SP += 2
            0xF1 => {
                self.registers.f = memory.read(self.registers.sp);
                self.registers.a = memory.read(self.registers.sp + 1);
                self.registers.sp = self.registers.sp.wrapping_add(2);
                10
            }, // POP AF

            // Jump if Positive (P): PC = nn if S = 0
            0xF2 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_S) {
                    self.registers.pc = nn;
                }
                10
            }, // JP P, nn

            // Disable Interrupts: Clear both interrupt flip-flops
            0xF3 => {
                self.iff1 = false;
                self.iff2 = false;
                4
            }, // DI

            // Call subroutine if Positive (P): Push PC, PC = nn if S = 0
            0xF4 => {
                let nn = self.fetch_word(memory);
                if !self.registers.get_flag(FLAG_S) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL P, nn

            // Push AF to stack: SP -= 2, (SP+1) = A, (SP) = F
            0xF5 => {
                self.registers.sp = self.registers.sp.wrapping_sub(2);
                memory.write(self.registers.sp + 1, self.registers.a);
                memory.write(self.registers.sp, self.registers.f);
                11
            }, // PUSH AF

            // Bitwise OR of immediate n with A, setting S, Z, PV (H/N/C reset)
            0xF6 => {
                let n = self.fetch_byte(memory);
                self.or_a_r(n);
                7
            }, // OR n

            // Restart at 0x30: Push PC, set PC to 0x0030
            0xF7 => {
                self.push_pc(memory);
                self.registers.pc = 0x0030;
                11
            }, // RST 30H

            // Return if Positive (P): Pop PC if S = 0
            0xF0 => {
                if !self.registers.get_flag(FLAG_S) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET P

            // Load SP with HL: SP = HL
            0xF9 => { // Note: Overlaps with ADD HL, SP; corrected below
                self.registers.sp = self.registers.get_hl();
                6
            }, // LD SP, HL
            
            // Jump if Minus (M): PC = nn if S = 1
            0xFA => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_S) {
                    self.registers.pc = nn;
                }
                10
            }, // JP M, nn

            // Call subroutine if Minus (M): Push PC, PC = nn if S = 1
            0xFC => {
                let nn = self.fetch_word(memory);
                if self.registers.get_flag(FLAG_S) {
                    self.push_pc(memory);
                    self.registers.pc = nn;
                    17
                } else {
                    10
                }
            }, // CALL M, nn

            // Enable Interrupts: Set both interrupt flip-flops after next instruction
            0xFB => { self.iff1 = true; self.iff2 = true; 4 }, // EI

            // Compare immediate n with A (A - n), setting all flags, A unchanged
            0xFE => {
                let n = self.fetch_byte(memory);
                let a = self.registers.a;
                let result = a.wrapping_sub(n);
                let half_carry = (a & 0x0F) < (n & 0x0F);
                let overflow = ((a ^ n) & 0x80 != 0) && ((a ^ result) & 0x80 != 0);
                let carry = a < n;
                self.registers.set_flag(FLAG_S, result & 0x80 != 0);
                self.registers.set_flag(FLAG_Z, result == 0);
                self.registers.set_flag(FLAG_H, half_carry);
                self.registers.set_flag(FLAG_PV, overflow);
                self.registers.set_flag(FLAG_N, true);
                self.registers.set_flag(FLAG_C, carry);
                7
            }, // CP n

            // Restart at 0x38: Push PC, set PC to 0x0038
            0xFF => {
                self.push_pc(memory);
                self.registers.pc = 0x0038;
                11
            }, // RST 38H

            // Return if Minus (M): Pop PC if S = 1
            0xF8 => {
                if self.registers.get_flag(FLAG_S) {
                    self.pop_pc(memory);
                    11
                } else {
                    5
                }
            }, // RET M

            // FD prefix: Fetch next byte and execute IY-related instruction
            0xFD => { let fd_opcode = self.fetch_byte(memory); self.execute_fd(fd_opcode, memory, io) },

            // ED prefix: Fetch next byte and execute extended instruction
            0xED => { let ed_opcode = self.fetch_byte(memory); self.execute_ed(ed_opcode, memory, io) },

            // Unimplemented opcodes trigger a panic with the opcode value
            _ => unimplemented!("Opcode {:#04x} not implemented", opcode),
        }
    }

    /// Executes CB-prefixed instructions (bit operations).
    fn execute_cb(&mut self, opcode: u8, memory: &mut dyn Z80Memory) -> u8 {
        let r = opcode & 0x07;
        let b = (opcode >> 3) & 0x07;
        match opcode >> 6 {
            0 => match (opcode >> 3) & 0x07 {
                0 => self.rlc_r(r, memory), // RLC r
                _ => unimplemented!("CB opcode {:#04x} not implemented", opcode),
            },
            1 => self.bit_b_r(b, r, memory), // BIT b, r
            2 => self.res_b_r(b, r, memory), // RES b, r
            3 => self.set_b_r(b, r, memory), // SET b, r
            _ => unreachable!("Invalid CB opcode prefix"),
        }
    }

    /// Executes DD-prefixed instructions (IX operations).
    fn execute_dd(&mut self, opcode: u8, memory: &mut dyn Z80Memory, _io: &mut dyn IoDevice) -> u8 {
        match opcode {
            0x21 => { self.registers.ix = self.fetch_word(memory); 14 }, // LD IX, nn
            0x36 => { // LD (IX+d), n
                let d = self.fetch_byte(memory) as i8;
                let n = self.fetch_byte(memory);
                memory.write(self.registers.ix.wrapping_add(d as u16), n);
                19
            },
            _ => unimplemented!("DD opcode {:#04x} not implemented", opcode),
        }
    }

    /// Executes ED-prefixed instructions (extended operations).
    fn execute_ed(&mut self, opcode: u8, memory: &mut dyn Z80Memory, _io: &mut dyn IoDevice) -> u8 {
        match opcode {
            0x56 => { self.im = 1; 8 }, // IM 1
            0xB0 => self.ldir(memory),  // LDIR
            _ => unimplemented!("ED opcode {:#04x} not implemented", opcode),
        }
    }

    /// Executes FD-prefixed instructions (IY operations).
    fn execute_fd(&mut self, opcode: u8, memory: &mut dyn Z80Memory, _io: &mut dyn IoDevice) -> u8 {
        match opcode {
            0x21 => { self.registers.iy = self.fetch_word(memory); 14 }, // LD IY, nn
            0x7E => { // LD A, (IY+d)
                let d = self.fetch_byte(memory) as i8;
                self.registers.a = memory.read(self.registers.iy.wrapping_add(d as u16));
                19
            },
            _ => unimplemented!("FD opcode {:#04x} not implemented", opcode),
        }
    }

    /// ADD A, r: Adds register r to A, updating flags.
    fn add_a_r(&mut self, r: u8) -> u8 {
        let a = self.registers.a;
        let result = a.wrapping_add(r);
        let half_carry = (a & 0x0F) + (r & 0x0F) > 0x0F;
        let overflow = ((a ^ r) & 0x80) == 0 && ((a ^ result) & 0x80) != 0;
        let carry = (a as u16) + (r as u16) > 0xFF;
        self.registers.a = result;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, carry);
        if r == 6 { 7 } else { 4 } // (HL) takes 7 cycles, others 4
    }

    /// SUB r: Subtracts register r from A, updating flags.
    fn sub_a_r(&mut self, r: u8) -> u8 {
        let a = self.registers.a;
        let result = a.wrapping_sub(r);
        let half_carry = (a & 0x0F) < (r & 0x0F);
        let overflow = ((a ^ r) & 0x80) != 0 && ((a ^ result) & 0x80) != 0;
        let carry = a < r;
        self.registers.a = result;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, true);
        self.registers.set_flag(FLAG_C, carry);
        if r == 6 { 7 } else { 4 } // (HL) takes 7 cycles, others 4
    }

    /// BIT b, r: Tests bit b in register r, setting flags.
    fn bit_b_r(&mut self, b: u8, r: u8, memory: &dyn Z80Memory) -> u8 {
        let value = self.get_register(r, memory);
        let bit = 1 << b;
        let zero = value & bit == 0;
        self.registers.set_flag(FLAG_Z, zero);
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_H, true);
        if r == 6 { 12 } else { 8 } // (HL) takes 12 cycles, others 8
    }

    /// RES b, r: Resets bit b in register r.
    fn res_b_r(&mut self, b: u8, r: u8, memory: &mut dyn Z80Memory) -> u8 {
        let value = self.get_register(r, memory);
        let result = value & !(1 << b);
        self.set_register(r, result, memory);
        if r == 6 { 15 } else { 8 } // (HL) takes 15 cycles, others 8
    }

    /// SET b, r: Sets bit b in register r.
    fn set_b_r(&mut self, b: u8, r: u8, memory: &mut dyn Z80Memory) -> u8 {
        let value = self.get_register(r, memory);
        let result = value | (1 << b);
        self.set_register(r, result, memory);
        if r == 6 { 15 } else { 8 } // (HL) takes 15 cycles, others 8
    }

    /// RLC r: Rotates register r left, setting flags.
    fn rlc_r(&mut self, r: u8, memory: &mut dyn Z80Memory) -> u8 {
        let value = self.get_register(r, memory);
        let carry = value & 0x80 != 0;
        let result = (value << 1) | if carry { 1 } else { 0 };
        self.set_register(r, result, memory);
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, false);
        self.registers.set_flag(FLAG_PV, Self::parity(result));
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, carry);
        if r == 6 { 15 } else { 8 } // (HL) takes 15 cycles, others 8
    }

    /// LDIR: Block transfer from (HL) to (DE), repeats until BC = 0.
    fn ldir(&mut self, memory: &mut dyn Z80Memory) -> u8 {
        let hl = self.registers.get_hl();
        let de = self.registers.get_de();
        let bc = self.registers.get_bc();
        let value = memory.read(hl);
        memory.write(de, value);
        let new_bc = bc.wrapping_sub(1);
        self.registers.set_hl(hl.wrapping_add(1));
        self.registers.set_de(de.wrapping_add(1));
        self.registers.set_bc(new_bc);
        self.registers.set_flag(FLAG_H, false);
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_PV, new_bc != 0);
        if new_bc != 0 {
            self.registers.pc = self.registers.pc.wrapping_sub(2);
            21 // Repeat takes 21 cycles
        } else {
            16 // Non-repeat takes 16 cycles
        }
    }

    /// Computes parity (true if even number of 1 bits).
    fn parity(value: u8) -> bool {
        value.count_ones() % 2 == 0
    }

    fn inc_8bit(&mut self, value: u8) -> u8 {
        let result = value.wrapping_add(1);
        let half_carry = (value & 0x0F) == 0x0F;
        let overflow = value == 0x7F;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, false);
        result
    }

    fn dec_8bit(&mut self, value: u8) -> u8 {
        let result = value.wrapping_sub(1);
        let half_carry = (value & 0x0F) == 0;
        let overflow = value == 0x80;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, true);
        result
    }

    fn adc_a_r(&mut self, r: u8) {
        let a = self.registers.a;
        let carry = if self.registers.get_flag(FLAG_C) { 1 } else { 0 };
        let result = a.wrapping_add(r).wrapping_add(carry);
        let half_carry = (a & 0x0F) + (r & 0x0F) + carry > 0x0F;
        let overflow = ((a ^ r) & 0x80 != 0) && ((a ^ result) & 0x80 != 0);
        let carry_out = (a as u16) + (r as u16) + (carry as u16) > 0xFF;
        self.registers.a = result;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, carry_out);
    }

    fn sbc_a_r(&mut self, r: u8) {
        let a = self.registers.a;
        let carry = if self.registers.get_flag(FLAG_C) { 1 } else { 0 };
        let result = a.wrapping_sub(r).wrapping_sub(carry);
        let half_carry = (a & 0x0F) < (r & 0x0F) + carry;
        let overflow = ((a ^ r) & 0x80 != 0) && ((a ^ result) & 0x80 != 0);
        let carry_out = (a as u16) < (r as u16) + (carry as u16);
        self.registers.a = result;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, half_carry);
        self.registers.set_flag(FLAG_PV, overflow);
        self.registers.set_flag(FLAG_N, true);
        self.registers.set_flag(FLAG_C, carry_out);
    }

    fn and_a_r(&mut self, r: u8) {
        self.registers.a &= r;
        let result = self.registers.a;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, true);
        self.registers.set_flag(FLAG_PV, Self::parity(result));
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, false);
    }

    fn xor_a_r(&mut self, r: u8) {
        self.registers.a ^= r;
        let result = self.registers.a;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, false);
        self.registers.set_flag(FLAG_PV, Self::parity(result));
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, false);
    }

    fn or_a_r(&mut self, r: u8) {
        self.registers.a |= r;
        let result = self.registers.a;
        self.registers.set_flag(FLAG_S, result & 0x80 != 0);
        self.registers.set_flag(FLAG_Z, result == 0);
        self.registers.set_flag(FLAG_H, false);
        self.registers.set_flag(FLAG_PV, Self::parity(result));
        self.registers.set_flag(FLAG_N, false);
        self.registers.set_flag(FLAG_C, false);
    }

    /// Triggers a Non-Maskable Interrupt (NMI).
    pub fn trigger_nmi(&mut self, memory: &mut dyn Z80Memory) {
        self.halted = false;
        self.iff2 = self.iff1;
        self.iff1 = false;
        self.push_pc(memory);
        self.registers.pc = 0x0066; // NMI vector
        self.cycles += 11;
    }

    /// Triggers a maskable interrupt with the given bus value.
    pub fn trigger_int(&mut self, memory: &mut dyn Z80Memory, io: &mut dyn IoDevice, bus_value: u8) -> u8 {
        if self.iff1 {
            self.halted = false;
            self.iff1 = false;
            self.iff2 = false;
            match self.im {
                0 => {
                    self.execute(bus_value, memory, io);
                    13 // Approximate for typical RST instruction
                },
                1 => {
                    self.push_pc(memory);
                    self.registers.pc = 0x0038; // IM 1 vector
                    self.cycles += 13;
                    13
                },
                2 => {
                    let addr = ((self.registers.i as u16) << 8) | bus_value as u16;
                    let low = memory.read(addr);
                    let high = memory.read(addr + 1);
                    let jump_addr = ((high as u16) << 8) | low as u16;
                    self.push_pc(memory);
                    self.registers.pc = jump_addr;
                    self.cycles += 19;
                    19
                },
                _ => unreachable!("Invalid interrupt mode"),
            }
        } else {
            0 // No cycles if interrupt not taken
        }
    }

    // Getter methods for testing
    pub fn get_a(&self) -> u8 { self.registers.a }
    pub fn get_b(&self) -> u8 { self.registers.b }
    pub fn get_bc(&self) -> u16 { self.registers.get_bc() }
    pub fn get_de(&self) -> u16 { self.registers.get_de() }
    pub fn get_hl(&self) -> u16 { self.registers.get_hl() }
    pub fn get_sp(&self) -> u16 { self.registers.sp }
    pub fn get_pc(&self) -> u16 { self.registers.pc }
    pub fn get_ix(&self) -> u16 { self.registers.ix }
    pub fn get_iy(&self) -> u16 { self.registers.iy }
    pub fn get_flag(&self, flag: u8) -> bool { self.registers.get_flag(flag) }
    pub fn is_halted(&self) -> bool { self.halted }

    // Setter methods for testing
    pub fn set_a(&mut self, value: u8) { self.registers.a = value }
    pub fn set_sp(&mut self, value: u16) { self.registers.sp = value }
    pub fn set_flag(&mut self, flag: u8, value: bool) { self.registers.set_flag(flag, value) }
}
