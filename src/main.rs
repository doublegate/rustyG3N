// src/main.rs
mod memory;
mod m68k_cpu;
mod z80_cpu;

use crate::memory::{GenesisMemory, Z80Bus, DummyIoDevice};
use crate::m68k_cpu::{CPU as M68K, Exception};
use crate::m68k_cpu::M68kMemory;
use crate::z80_cpu::{Z80, IoDevice};

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

    // Typically, you’d reset the Z80's PC, SP, etc. however the Genesis BIOS would do so.
    // The Z80 is initially held in reset on the real hardware until the 68k writes to certain regs.
    // For demonstration:
    z80_cpu.set_sp(0x0100);
    // PC is default 0x0000, or set as you like
    // z80_cpu.registers.pc = 0;

    // 5. Enter a main loop stepping both CPUs
    //   - Real Genesis code must synchronize them by cycles (the 68k runs ~7.6MHz, Z80 runs ~3.58MHz).
    //   - You’d also handle VBlank interrupts, line interrupts, bus arbitration, etc.
    //   - For now, we just run them in a simple loop.
    println!("Starting Emulation Loop (... incomplete). Press Ctrl+C to stop.");

    let mut total_instructions = 0u64;

    loop {
        // Step the 68000 by (for example) 200 cycles
        let mut cycles_used = 0;
        while cycles_used < 200 {
            let cycles = m68k_cpu.step();
            cycles_used += cycles;
            total_instructions += 1;
            // In a real emulator, you’d check for interrupts, do VDP checks, etc.
        }

        // Step the Z80 for some fraction of that (Z80 frequency is ~47% of 68k)
        let mut z80_cycles_used = 0;
        while z80_cycles_used < (200 * 47 / 100) {
            // Step 1 instruction
            let cyc = z80_cpu.step(&mut z80_bus, &mut dummy_io);
            z80_cycles_used += cyc as i32;
        }

        // For demonstration, break after some iteration:
        if total_instructions > 2_000_000 {
            println!("Stopping after 2,000,000 68k instructions (demo).");
            break;
        }

        // You might also insert a small sleep or check for user input, etc.
    }

    println!("Emulation Ended - Success!");
    println!("--------------------------");
    println!("Final 68k SP: 0x{:08X}", m68k_cpu.a[7]);
    println!("Final 68k PC: 0x{:08X}", m68k_cpu.pc);
    println!("Total 68k Instruct: {}", total_instructions);
    println!("Final Z80 SP: 0x{:04X}", z80_cpu.get_sp());
    println!("Final Z80 PC: 0x{:04X}", z80_cpu.get_pc());
    // println!("Total Z80 Instruct: {}", z80_cycles_used);
}
