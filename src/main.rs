// src/main.rs
mod display;
mod memory;
mod m68k_cpu;
mod z80_cpu;
mod vdp;

use crate::memory::{GenesisMemory, Z80Bus, DummyIoDevice};
use crate::m68k_cpu::{CPU as M68K, Exception};
use crate::m68k_cpu::M68kMemory;
use crate::z80_cpu::{Z80, IoDevice};
use crate::display::Display;  // <--- ADD
use crate::vdp::SCANLINES_PER_FRAME; // to access '262'
use crate::vdp::CYCLES_PER_SCANLINE;


use std::env;

fn main() {
    // 1. Parse command-line to get ROM path, or default
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: cargo run -- <path_to_genesis_rom>");
        return;
    }
    let rom_path = &args[1];

    // 2. Create our memory and load the ROM
    let mut mem = GenesisMemory::new();
    if let Err(e) = mem.load_cartridge(rom_path) {
        eprintln!("Failed to load ROM: {}", e);
        return;
    }
    let rom_size = mem.rom.len();
    println!("Loaded ROM: {} ({} bytes)", rom_path, rom_size);

    // 3. Initialize the 68000 CPU
    // The Genesis reset vector is at offset 0 in the ROM for initial SP, offset 4 for initial PC.
    // However, many ROMs map the vector table at 0x000000, so let's read it from memory:
    let init_sp = mem.read_long(0x000000).unwrap_or(0x00FF0000);
    let init_pc = mem.read_long(0x000004).unwrap_or(0x00000100);

    let mut m68k_cpu = M68K::new(mem);

    // Set up the CPU registers from the reset vector
    m68k_cpu.a[7] = init_sp; // A7 is the 68k's stack pointer
    m68k_cpu.pc   = init_pc;

    // Prefetch (optional, but your CPU implementation might require it)
    m68k_cpu.prefetch();

    // 4. Create the Z80, hooking it to our memory
 
    /*
        // We pass a *mutable reference* to the same memory structure if we want
        // the Z80 to see the same state. Or you can store separate references if
        // your architecture differs. We'll do a trick with interior mutability:
        //   - We'll temporarily clone the memory to pass to Z80 for demonstration
        //   - Or we can unify them in a single structure with `RefCell` or `Arc<Mutex<...>>`.
        //   - Or we can use a global memory bus, etc.
        //
        // For demonstration, let's do a separate struct referencing the same data.
        //
        // let mut shared_mem = unsafe {
        //     // VERY rough approach: we move the memory out from M68K, then reconstruct later.
        //     // A more typical approach is to store the memory in a global or higher-level struct.
        //     // We'll just demonstrate the concept. In a real program, you'd design your memory bus
        //     // carefully so both CPUs can see it simultaneously.
        //     std::mem::transmute::<&mut crate::m68k_cpu::CPU<GenesisMemory>, &mut GenesisMemory>(&mut m68k_cpu.memory)
        // };
        //
        // let mut z80_bus = memory::Z80Bus::new(shared_mem);
    */
    
    let mut z80_bus = Z80Bus { 
        z80_ram: [0; 0x2000], // 8KB for demonstration
    };

    let mut z80_cpu = Z80::new();

    // A dummy I/O device for the Z80
    let mut dummy_io = DummyIoDevice;

    // Create a 320x224 window to display the VDP output buffer:
    let mut display = Display::new(320, 224, 1.0);
    while display.is_open() {
        // Render one frame (all 262 NTSC scanlines):
        for line in 0..SCANLINES_PER_FRAME {
            // Accumulate enough CPU cycles to represent one scanline:
            let mut line_cycles = 0;
            while line_cycles < CYCLES_PER_SCANLINE {
                let cycles_used = m68k_cpu.step();
                line_cycles += cycles_used as u32;

                // Step the Z80 a fraction of that (Z80 ~3.58MHz vs 68k ~7.68MHz):
                let z80_steps = (cycles_used as f64 * 3.58 / 7.68).ceil() as i32;
                let mut used_z80 = 0;
                while used_z80 < z80_steps {
                    used_z80 += z80_cpu.step(&mut z80_bus, &mut dummy_io) as i32;
                }
            }

            // Now tell the VDP to render this scanline:
            m68k_cpu.memory.vdp.render_scanline(line as usize);
        }

        // After finishing all lines, present the result on screen:
        display.update(
            m68k_cpu.memory.vdp.get_screen_buffer(),
            320,
            224
        );
    }

    println!("Emulation Ended - Success!");
    println!("--------------------------");
/*
    println!("Final 68k SP: 0x{:08X}", m68k_cpu.a[7]);
    println!("Final 68k PC: 0x{:08X}", m68k_cpu.pc);
    println!("Total 68k Instruct: {}", total_instructions);
    println!("Final Z80 SP: 0x{:04X}", z80_cpu.get_sp());
    println!("Final Z80 PC: 0x{:04X}", z80_cpu.get_pc());
    println!("Total Z80 Instruct: {}", z80_cycles_used);
*/
}
