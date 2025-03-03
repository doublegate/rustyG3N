// NTSC Genesis timing constants
pub const SCANLINES_PER_FRAME: u32 = 262;   // 224 visible + 38 VBlank
pub const CYCLES_PER_SCANLINE: u32 = 171;   // Base cycles per scanline (adjusted)
pub const VBLANK_START: u32 = 224;

pub struct Vdp {
    vram: [u8; 0x10000],     // 64 KB of Video RAM
    cram: [u16; 64],         // Color RAM for 64 palette entries (9-bit colors)
    vsram: [u8; 80],         // Vertical Scroll RAM
    registers: [u8; 24],     // VDP registers
    screen_buffer: Vec<u32>, // Pixel buffer in ARGB format
    width: usize,            // Screen width (e.g., 320 for H40 mode)
    height: usize,           // Screen height (e.g., 224)
    addr: u32,               // VDP address register
    code: u8,                // VDP code register (access mode)
    autoincrement: u8,       // Address autoincrement value
    plane_width: u32,        // Plane width in tiles
    plane_height: u32,       // Plane height in tiles
    current_scanline: u32,   // Current scanline for mid-scanline changes
    cycles: u32,             // Total cycles in the current frame (tracked externally)
    hblank_flag: bool,       // HBlank interrupt pending
    vblank_flag: bool,       // VBlank interrupt pending
    dma_active: bool,        // DMA active flag
}

impl Vdp {
    pub fn new() -> Self {
        let width = 320; // H40 mode for Sonic
        let height = 224; // NTSC visible lines
        Vdp {
            vram: [0; 0x10000],
            cram: [0; 64],
            vsram: [0; 80],
            registers: [0; 24],
            screen_buffer: vec![0; width * height],
            width,
            height,
            addr: 0,
            code: 0,
            autoincrement: 2,
            plane_width: 64,
            plane_height: 32,
            current_scanline: 0,
            cycles: 0,
            hblank_flag: false,
            vblank_flag: false,
            dma_active: false,
        }
    }

    /// Render a single scanline with cycle accuracy
    pub fn render_scanline(&mut self, scanline: usize) -> u32 {
        self.current_scanline = scanline as u32;
        let mut scanline_cycles = CYCLES_PER_SCANLINE;

        if scanline < self.height {
            let h40_mode = (self.registers[0x0C] & 0x81) != 0;
            self.width = if h40_mode { 320 } else { 256 };
            (self.plane_width, self.plane_height) = self.get_plane_size();

            let plane_b_base = ((self.registers[3] & 0x07) as u32) << 13;
            let plane_a_base = ((self.registers[2] & 0x38) as u32) << 10;
            let window_base = ((self.registers[4] & 0x07) as u32) << 13;
            let sprite_base = ((self.registers[5] & 0x7E) as u32) << 9;
            let hscroll_base = ((self.registers[0x0D] & 0x3F) as u32) << 10;

            self.render_plane_scanline(scanline, plane_b_base, hscroll_base, false);
            self.render_sprites_scanline(scanline, sprite_base, false);
            if self.is_window_enabled(scanline) {
                self.render_window_scanline(scanline, window_base);
            } else {
                self.render_plane_scanline(scanline, plane_a_base, hscroll_base, true);
            }
            self.render_sprites_scanline(scanline, sprite_base, true);

            self.hblank_flag = true; // Set HBlank after visible scanline
            scanline_cycles += 488; // Additional HBlank cycles
        } else if scanline == VBLANK_START as usize {
            self.vblank_flag = true; // Set VBlank at start of VBlank
            self.dma_active = true;  // DMA starts
        }

        if self.dma_active && scanline >= VBLANK_START as usize {
            scanline_cycles += 512; // DMA burst cycles for Sonic
            if scanline + 1 == SCANLINES_PER_FRAME as usize {
                self.dma_active = false; // DMA ends at frame end
            }
        }

        scanline_cycles
    }

    // Retained advanced feature methods
    fn get_plane_size(&self) -> (u32, u32) {
        let h_bits = self.registers[0x10] & 0x03;
        let v_bits = (self.registers[0x10] >> 4) & 0x03;
        let h_size = match h_bits {
            0 => 32,
            1 => 64,
            3 => 128,
            _ => 32,
        };
        let v_size = match v_bits {
            0 => 32,
            1 => 64,
            3 => 128,
            _ => 32,
        };
        (h_size, v_size)
    }

    fn is_window_enabled(&self, scanline: usize) -> bool {
        let h_pos_reg = self.registers[0x11];
        let v_pos_reg = self.registers[0x12];
        let h_pos = (h_pos_reg & 0x1F) as usize * 8;
        let v_pos = (v_pos_reg & 0x1F) as usize * 8;
        let right_aligned = (h_pos_reg & 0x80) != 0;

        if h_pos >= self.width || v_pos >= self.height {
            return false;
        }
        let above_window = scanline < v_pos;
        !above_window && (h_pos > 0 || v_pos > 0)
    }

    fn render_plane_scanline(&mut self, scanline: usize, tilemap_base: u32, hscroll_base: u32, is_plane_a: bool) {
        let vscroll_idx = if is_plane_a { 0 } else { 2 };
        let vscroll = u16::from_le_bytes([self.vsram[vscroll_idx], self.vsram[vscroll_idx + 1]]) as u32;
        let hscroll = u16::from_le_bytes([
            self.vram[(hscroll_base + (scanline as u32 * 4)) as usize],
            self.vram[(hscroll_base + (scanline as u32 * 4 + 1)) as usize],
        ]) as u32;

        let plane_y = (scanline as u32 + vscroll) % (self.plane_height * 8);
        let tile_row = plane_y / 8;
        let pixel_y_in_tile = plane_y % 8;

        for screen_x in 0..self.width {
            let plane_x = (screen_x as u32 + hscroll) % (self.plane_width * 8);
            let tile_col = plane_x / 8;
            let pixel_x_in_tile = plane_x % 8;

            let tilemap_addr = tilemap_base + (tile_row * self.plane_width * 2 + tile_col * 2) as u32;
            let entry = self.read_vram_u16(tilemap_addr);

            let pattern_index = entry & 0x7FF;
            let palette = (entry >> 13) & 0x3;
            let hflip = (entry & 0x0800) != 0;
            let vflip = (entry & 0x1000) != 0;
            let priority = (entry & 0x8000) != 0;

            let tile_x = if hflip { 7 - pixel_x_in_tile } else { pixel_x_in_tile };
            let tile_y = if vflip { 7 - pixel_y_in_tile } else { pixel_y_in_tile };

            let color = self.get_pixel_color(pattern_index, tile_x, tile_y, palette);
            if color != 0 {
                let idx = scanline * self.width + screen_x;
                if priority || self.screen_buffer[idx] == 0 {
                    self.screen_buffer[idx] = self.convert_color(self.cram[color as usize]);
                }
            }
        }
    }

    fn render_sprites_scanline(&mut self, scanline: usize, sprite_base: u32, high_priority: bool) {
        let mut sprite_count = 0;
        let mut current = 0;
        let mut processed = [false; 80];
    
        while sprite_count < 20 && current < 80 && !processed[current as usize] {
            let sprite_addr = sprite_base + current * 8;
            processed[current as usize] = true;
    
            let y_pos = self.read_vram_u16(sprite_addr) & 0x3FF;
            let size = self.read_vram_u16(sprite_addr + 2);
            let v_size = ((size >> 2) & 0x3) + 1;
            let h_size = (size & 0x3) + 1;
            let link = (size >> 8) & 0x7F;
            let attrib = self.read_vram_u16(sprite_addr + 4);
            let pattern_index = attrib & 0x7FF;
            let palette = (attrib >> 13) & 0x3;  // Fixed from 'entry'
            let hflip = (attrib & 0x0800) != 0;  // Fixed from 'entry'
            let vflip = (attrib & 0x1000) != 0;  // Fixed from 'entry'
            let priority = (attrib & 0x8000) != 0;  // Fixed from 'entry'
            let x_pos = self.read_vram_u16(sprite_addr + 6) & 0x3FF;
    
            if priority == high_priority {
                let sprite_top = ((y_pos as i32) - 128);
                let sprite_bottom = sprite_top + ((v_size * 8) as i32);
                if sprite_top <= (scanline as i32) && (scanline as i32) < sprite_bottom {
                    let row_in_sprite = ((scanline as i32) - sprite_top);
                    self.render_sprite_row(
                        ((x_pos as i32) - 128),
                        row_in_sprite,
                        h_size,
                        v_size,
                        pattern_index,
                        palette,
                        hflip,
                        vflip,
                        priority,
                        scanline
                    );
                    sprite_count += 1;
                }
            }
            current = link as u32;
            if current == 0 { break; }
        }
    }

    fn render_sprite_row(&mut self, x_pos: i32, row_in_sprite: i32, h_size: u16, v_size: u16, pattern_index: u16, palette: u16, hflip: bool, vflip: bool, priority: bool, scanline: usize) {
        let tile_y = if vflip {
            (((v_size as u32) * 8 - 1) - row_in_sprite as u32) as u16
        } else {
            row_in_sprite as u16
        };
        let tile_row = tile_y / 8;
        let pixel_y = tile_y % 8;

        for h in 0..h_size * 8 {
            let tile_x = if hflip { h_size * 8 - 1 - h } else { h };
            let tile_col = tile_x / 8;
            let pixel_x = tile_x % 8;

            let tile_index = pattern_index + tile_row * h_size + tile_col;
            let color = self.get_pixel_color(tile_index, pixel_x as u32, pixel_y as u32, palette);
            if color != 0 {
                let screen_x = x_pos + h as i32;
                if screen_x >= 0 && screen_x < self.width as i32 {
                    let idx = scanline * self.width + screen_x as usize;
                    if priority || self.screen_buffer[idx] == 0 {
                        self.screen_buffer[idx] = self.convert_color(self.cram[color as usize]);
                    }
                }
            }
        }
    }

    fn render_window_scanline(&mut self, scanline: usize, tilemap_base: u32) {
        let v_pos = (self.registers[0x12] & 0x1F) as usize * 8;
        let h_pos = (self.registers[0x11] & 0x1F) as usize * 8;
        let right_aligned = (self.registers[0x11] & 0x80) != 0;

        let window_y = (scanline - v_pos) as u32;
        if window_y >= self.plane_height * 8 { return; }
        let tile_row = window_y / 8;
        let pixel_y_in_tile = window_y % 8;

        for screen_x in 0..self.width {
            let in_window_h = if right_aligned { screen_x >= h_pos } else { screen_x < h_pos };
            if !in_window_h { continue; }

            let window_x = screen_x as u32 - if right_aligned { h_pos as u32 } else { 0 };
            let tile_col = window_x / 8;
            let pixel_x_in_tile = window_x % 8;

            let tilemap_addr = tilemap_base + (tile_row * self.plane_width * 2 + tile_col * 2) as u32;
            let entry = self.read_vram_u16(tilemap_addr);

            let pattern_index = entry & 0x7FF;
            let palette = (entry >> 13) & 0x3;
            let hflip = (entry & 0x0800) != 0;
            let vflip = (entry & 0x1000) != 0;
            let priority = (entry & 0x8000) != 0;

            let tile_x = if hflip { 7 - pixel_x_in_tile } else { pixel_x_in_tile };
            let tile_y = if vflip { 7 - pixel_y_in_tile } else { pixel_y_in_tile };

            let color = self.get_pixel_color(pattern_index, tile_x, tile_y, palette);
            if color != 0 {
                let idx = scanline * self.width + screen_x;
                if priority || self.screen_buffer[idx] == 0 {
                    self.screen_buffer[idx] = self.convert_color(self.cram[color as usize]);
                }
            }
        }
    }

    fn get_pixel_color(&self, pattern_index: u16, tile_x: u32, tile_y: u32, palette: u16) -> u16 {
        let pattern_addr = (pattern_index as u32 * 32 + tile_y * 4) as u32;
        let byte_index = (tile_x / 2) as u32;
        let nibble = if tile_x % 2 == 0 {
            self.vram[(pattern_addr + byte_index) as usize] >> 4
        } else {
            self.vram[(pattern_addr + byte_index) as usize] & 0xF
        };
        if nibble == 0 { 0 } else { palette * 16 + nibble as u16 }
    }

    fn convert_color(&self, color: u16) -> u32 {
        let b = ((color & 0x000E) >> 1) as u8;
        let g = ((color & 0x00E0) >> 5) as u8;
        let r = ((color & 0x0E00) >> 9) as u8;
        let r_8 = ((r as u32 * 255) / 7) as u8;
        let g_8 = ((g as u32 * 255) / 7) as u8;
        let b_8 = ((b as u32 * 255) / 7) as u8;
        0xFF000000 | ((r_8 as u32) << 16) | ((g_8 as u32) << 8) | b_8 as u32
    }

    fn read_vram_u16(&self, addr: u32) -> u16 {
        if addr + 1 < 0x10000 {
            (self.vram[addr as usize] as u16) | ((self.vram[(addr + 1) as usize] as u16) << 8)
        } else {
            0
        }
    }

    pub fn get_screen_buffer(&self) -> &[u32] {
        &self.screen_buffer
    }

    pub fn write_control(&mut self, value: u32) {
        if (value & 0xC000) == 0x8000 {
            let reg = (value >> 8) & 0x1F;
            let data = value & 0xFF;
            if reg < 24 {
                self.registers[reg as usize] = data as u8;
            }
        } else {
            self.code = ((value >> 14) & 0x3) as u8;
            self.addr = value & 0x3FFF;
        }
    }

    pub fn write_data(&mut self, value: u16) {
        match self.code {
            0 => {
                if (self.addr + 1) < 0x10000 {
                    self.vram[self.addr as usize] = (value & 0xFF) as u8;
                    self.vram[(self.addr + 1) as usize] = (value >> 8) as u8;
                }
            }
            1 => {
                if self.addr < 128 {
                    self.cram[(self.addr / 2) as usize] = value & 0x0EEE;
                }
            }
            2 => {
                if self.addr < 80 {
                    self.vsram[self.addr as usize] = (value & 0xFF) as u8;
                    self.vsram[(self.addr + 1) as usize] = (value >> 8) as u8;
                }
            }
            _ => {}
        }
        self.addr = (self.addr + self.autoincrement as u32) & 0xFFFF;
    }

    pub fn read_data(&self) -> u16 {
        match self.code {
            0 => self.read_vram_u16(self.addr),
            1 => if self.addr < 128 { self.cram[(self.addr / 2) as usize] } else { 0 },
            2 => if self.addr < 80 { u16::from_le_bytes([self.vsram[self.addr as usize], self.vsram[(self.addr + 1) as usize]]) } else { 0 },
            _ => 0,
        }
    }

    pub fn check_hblank_interrupt(&self) -> bool {
        self.hblank_flag && (self.registers[0] & 0x10) != 0
    }

    pub fn check_vblank_interrupt(&self) -> bool {
        self.vblank_flag && (self.registers[1] & 0x20) != 0
    }

    pub fn reset_interrupt_flags(&mut self) {
        self.hblank_flag = false;
        self.vblank_flag = false;
    }

    pub fn is_dma_active(&self) -> bool {
        self.dma_active
    }
}