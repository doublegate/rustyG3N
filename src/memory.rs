// src/memory.rs

use std::io::Read;
use std::fs::File;
use std::path::Path;
use crate::m68k_cpu::{M68kMemory, Exception};
use crate::z80_cpu::{Z80Memory, IoDevice};

/// A very rough, incomplete memory map for the Sega Genesis 68k side.
/// For real emulation, you’d need to handle many more regions:
/// - 0x000000 - 0x3FFFFF: Cartridge ROM (max 4MB)
/// - 0xA00000 - 0xA0FFFF: Z80 access (sound CPU comms)
/// - 0xC00000 - 0xC0001F: VDP regs
/// - 0xE00000 - 0xE0FFFF: RAM (64KB)
/// - etc.
pub struct GenesisMemory {
    pub rom: Vec<u8>,
    pub ram_68k: [u8; 0x10000], // 64KB 68k RAM at 0xE00000
    pub z80_ram: [u8; 0x2000],  // 8KB Z80 RAM, banked or mirrored

    // Possibly other devices like VDP, IO, etc.
}   /// Trait that the 68000 CPU expects

impl GenesisMemory {
    pub fn new() -> Self {
        Self {
            rom: vec![],
            ram_68k: [0; 0x10000],
            z80_ram: [0; 0x2000],
        }
    }

    /// Load a .bin or .md Sega Genesis ROM from disk into `self.rom`.
    pub fn load_cartridge<P: AsRef<Path>>(&mut self, path: P) -> std::io::Result<()> {
        let mut file = File::open(path)?;
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)?;
        self.rom = buffer;
        Ok(())
    }

    // Helper: sign-extend 24-bit addresses to 32-bit
    fn mask_address_68k(&self, address: u32) -> u32 {
        address & 0xFFFFFF
    }

    /// Return a mirrored or clamped region if the cart is smaller than 4MB, etc.
    fn read_rom(&self, address: u32) -> u8 {
        if address as usize >= self.rom.len() {
            0 // open bus or mirror
        } else {
            self.rom[address as usize]
        }
    }
}

impl M68kMemory for GenesisMemory {
    fn read_byte(&mut self, address: u32) -> Result<u8, Exception> {
        let addr = self.mask_address_68k(address);

        match addr {
            0x000000..=0x3FFFFF => {
                // Cartridge ROM
                Ok(self.read_rom(addr))
            }
            0xE00000..=0xE0FFFF => {
                // 68k RAM
                let offset = (addr - 0xE00000) as usize;
                Ok(self.ram_68k[offset])
            }
            0xA00000..=0xA0FFFF => {
                // Z80 bus window (very simplified approach!)
                // Typically you'd handle bank / bus capture logic
                let offset = (addr & 0x1FFF) as usize;
                Ok(self.z80_ram[offset])
            }
            _ => {
                // For everything else, we just return 0 or raise AddressError.
                // The real Genesis has many more mapped addresses.
                Err(Exception::AddressError)
            }
        }
    }

    fn read_word(&mut self, address: u32) -> Result<u16, Exception> {
        // The 68k requires aligned word reads on even addresses.
        if address & 1 != 0 {
            return Err(Exception::AddressError);
        }

        let high = self.read_byte(address)? as u16;
        let low  = self.read_byte(address + 1)? as u16;
        Ok((high << 8) | low)
    }

    fn read_long(&mut self, address: u32) -> Result<u32, Exception> {
        // Must be aligned on a 2-byte boundary (strictly, 4 bytes for good measure).
        if address & 1 != 0 {
            return Err(Exception::AddressError);
        }

        let w1 = self.read_word(address)? as u32;
        let w2 = self.read_word(address + 2)? as u32;
        Ok((w1 << 16) | w2)
    }

    fn write_byte(&mut self, address: u32, value: u8) -> Result<(), Exception> {
        let addr = self.mask_address_68k(address);

        match addr {
            0x000000..=0x3FFFFF => {
                // Cartridge ROM is read-only; ignore or raise an error
                Ok(())
            }
            0xE00000..=0xE0FFFF => {
                // 68k RAM
                let offset = (addr - 0xE00000) as usize;
                self.ram_68k[offset] = value;
                Ok(())
            }
            0xA00000..=0xA0FFFF => {
                // Write to Z80 space
                let offset = (addr & 0x1FFF) as usize;
                self.z80_ram[offset] = value;
                Ok(())
            }
            _ => {
                Err(Exception::AddressError)
            }
        }
    }

    fn write_word(&mut self, address: u32, value: u16) -> Result<(), Exception> {
        if address & 1 != 0 {
            return Err(Exception::AddressError);
        }

        let high = (value >> 8) as u8;
        let low  = (value & 0xFF) as u8;
        self.write_byte(address,     high)?;
        self.write_byte(address + 1, low)?;
        Ok(())
    }

    fn write_long(&mut self, address: u32, value: u32) -> Result<(), Exception> {
        if address & 1 != 0 {
            return Err(Exception::AddressError);
        }

        let w1 = (value >> 16) as u16;
        let w2 = (value & 0xFFFF) as u16;
        self.write_word(address,     w1)?;
        self.write_word(address + 2, w2)?;
        Ok(())
    }
}

/// Simple trait for the Z80 memory. This is an example that matches the
/// `Memory` trait used by your Z80 CPU. Typically, your Z80 core expects:
///   fn read(&self, address: u16) -> u8
///   fn write(&mut self, address: u16, value: u8)
///
/// We'll implement a separate struct for clarity.
/// Example Z80 bus struct.
/// You can adjust fields to match your actual design.
pub struct Z80Bus {
    pub z80_ram: [u8; 0x2000], // 8KB for demonstration
}
/// A reference back to the shared GenesisMemory, so we can read/write
/// the same Z80 RAM or the 68k->Z80 window. In the real Genesis, the
/// Z80 sees 64KB of its own space, possibly including the YM2612 regs,
/// PSG, etc.
impl Z80Memory for Z80Bus {
// Implement the trait your Z80 CPU uses:
    fn read(&self, address: u16) -> u8 {
        // The Z80 has a 64KB address space, but the Genesis only exposes 8KB.
        // We'll mirror the RAM across the whole space for simplicity.
        let offset = (address as usize) & 0x1FFF;
        self.z80_ram[offset]
    }

    fn write(&mut self, address: u16, value: u8) {
        let offset = (address as usize) & 0x1FFF;
        self.z80_ram[offset] = value;
    }
}

/// A simple IO device that does nothing but satisfy the IoDevice trait.
pub struct DummyIoDevice;

impl IoDevice for DummyIoDevice {
    fn read(&self, _port: u16) -> u8 {
        0
    }

    fn write(&mut self, _port: u16, _value: u8) {
        // No-op
    }
}