use minifb::{Window, WindowOptions, Scale};

pub struct Display {
    window: Window,
    width: usize,
    height: usize,
}

impl Display {
    pub fn new(width: usize, height: usize, scale: f32) -> Self {
        let mut window = Window::new(
            "rustyGEN",
            width,
            height,
            WindowOptions {
                scale: match scale {
                    s if s <= 1.0 => Scale::X1,
                    s if s <= 2.0 => Scale::X2,
                    s if s <= 4.0 => Scale::X4,
                    _ => Scale::X8,
                },
                ..WindowOptions::default()
            },
        ).expect("Failed to create window");
        window.set_target_fps(60);
        Display { window, width, height }
    }

    pub fn update(&mut self, buffer: &[u32], width: usize, height: usize) {
        self.window.update_with_buffer(buffer, width, height).unwrap();
    }

    pub fn is_open(&self) -> bool {
        self.window.is_open()
    }

    pub fn is_key_down(&self, key: minifb::Key) -> bool {
        self.window.is_key_down(key)
    }
}
