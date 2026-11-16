//! The terminal colours of the REPL and the error messages: one palette,
//! Catppuccin Mocha on a dark background and Latte on a light one, with the
//! colour of each role chosen as in Catppuccin's style guide
//! (<https://github.com/catppuccin/catppuccin>, docs/reviews/SW-3635-palettes.html).
//!
//! Catppuccin is MIT licensed: Copyright (c) 2021 Catppuccin.
//!
//! Which theme and which colour depth are decided by the caller (the CLI
//! reads the environment and asks the terminal); this module holds the
//! tables, the pure decision rules and the parser of a terminal's answer.

use std::sync::OnceLock;

/// The terminal's background: [`Theme::Dark`] uses Catppuccin Mocha,
/// [`Theme::Light`] Latte.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Theme {
    Dark,
    Light,
}

/// How a colour is written: 24-bit (`38;2;r;g;b`) or the nearest of the
/// 256-colour palette (`38;5;n`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Depth {
    TrueColor,
    Indexed,
}

/// What a colour is for. The REPL's token classes and the error messages'
/// parts share these.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    Keyword,
    Number,
    Text,
    /// Type and constructor names, and the type of a REPL result.
    Type,
    Operator,
    Comment,
    Error,
    Warning,
    Goal,
    /// A report's secondary labels.
    Secondary,
    /// The `try:` of a suggested fix, and the expected row of a mismatch.
    Fix,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Palette {
    pub theme: Theme,
    pub depth: Depth,
}

/// Catppuccin Mocha, in the order of [`Role`].
const MOCHA: [(u8, u8, u8); 11] = [
    (0xcb, 0xa6, 0xf7), // Keyword: mauve
    (0xfa, 0xb3, 0x87), // Number: peach
    (0xa6, 0xe3, 0xa1), // Text: green
    (0xf9, 0xe2, 0xaf), // Type: yellow
    (0x89, 0xdc, 0xeb), // Operator: sky
    (0x93, 0x99, 0xb2), // Comment: overlay2
    (0xf3, 0x8b, 0xa8), // Error: red
    (0xf9, 0xe2, 0xaf), // Warning: yellow
    (0x94, 0xe2, 0xd5), // Goal: teal
    (0xb4, 0xbe, 0xfe), // Secondary: lavender
    (0xa6, 0xe3, 0xa1), // Fix: green
];

/// Catppuccin Latte, in the order of [`Role`].
const LATTE: [(u8, u8, u8); 11] = [
    (0x88, 0x39, 0xef), // Keyword: mauve
    (0xfe, 0x64, 0x0b), // Number: peach
    (0x40, 0xa0, 0x2b), // Text: green
    (0xdf, 0x8e, 0x1d), // Type: yellow
    (0x04, 0xa5, 0xe5), // Operator: sky
    (0x7c, 0x7f, 0x93), // Comment: overlay2
    (0xd2, 0x0f, 0x39), // Error: red
    (0xdf, 0x8e, 0x1d), // Warning: yellow
    (0x17, 0x92, 0x99), // Goal: teal
    (0x72, 0x87, 0xfd), // Secondary: lavender
    (0x40, 0xa0, 0x2b), // Fix: green
];

impl Default for Palette {
    fn default() -> Self {
        Palette {
            theme: Theme::Dark,
            depth: Depth::TrueColor,
        }
    }
}

impl Palette {
    /// The colour of `role` as red, green and blue.
    pub fn rgb(self, role: Role) -> (u8, u8, u8) {
        match self.theme {
            Theme::Dark => MOCHA[role as usize],
            Theme::Light => LATTE[role as usize],
        }
    }

    /// Whether `role` is also bold: on Latte, the roles whose colour is
    /// only 2.3 to 3.0 times as bright as the white it is on.
    pub fn bold(self, role: Role) -> bool {
        self.theme == Theme::Light
            && matches!(
                role,
                Role::Type | Role::Warning | Role::Operator | Role::Text
            )
    }

    /// The SGR parameters for `role`, after `extra` (`1;4` for bold and
    /// underlined) if any.
    pub fn sgr(self, role: Role, extra: &str) -> String {
        let (r, g, b) = self.rgb(role);
        let mut out = String::new();
        if !extra.is_empty() {
            out.push_str(extra);
            out.push(';');
        }
        if self.bold(role) && !extra.split(';').any(|p| p == "1") {
            out.push_str("1;");
        }
        match self.depth {
            Depth::TrueColor => out.push_str(&format!("38;2;{r};{g};{b}")),
            Depth::Indexed => out.push_str(&format!("38;5;{}", nearest_256(r, g, b))),
        }
        out
    }

    /// The escape sequence that starts `role`'s colour.
    pub fn open(self, role: Role) -> String {
        format!("\u{1b}[{}m", self.sgr(role, ""))
    }

    /// `role`'s colour for ariadne's labels (which can't be bold).
    pub fn ariadne(self, role: Role) -> ariadne::Color {
        let (r, g, b) = self.rgb(role);
        match self.depth {
            Depth::TrueColor => ariadne::Color::Rgb(r, g, b),
            Depth::Indexed => ariadne::Color::Fixed(nearest_256(r, g, b)),
        }
    }
}

/// The index in the 256-colour palette (the 6×6×6 cube and the 24 greys;
/// not the 16 terminal-defined colours, which vary) nearest to a colour.
pub fn nearest_256(r: u8, g: u8, b: u8) -> u8 {
    const LEVELS: [u8; 6] = [0, 95, 135, 175, 215, 255];
    let near = |v: u8| {
        (0..6)
            .min_by_key(|&i| (i32::from(LEVELS[i]) - i32::from(v)).abs())
            .expect("six levels")
    };
    let (ri, gi, bi) = (near(r), near(g), near(b));
    let cube = (
        16 + 36 * ri + 6 * gi + bi,
        (LEVELS[ri], LEVELS[gi], LEVELS[bi]),
    );
    let avg = (u32::from(r) + u32::from(g) + u32::from(b)) / 3;
    let step = ((avg.saturating_sub(8) + 5) / 10).min(23) as usize;
    let grey_level = (8 + 10 * step) as u8;
    let grey = (232 + step, (grey_level, grey_level, grey_level));
    let dist = |(cr, cg, cb): (u8, u8, u8)| {
        let d = |a: u8, b: u8| (i32::from(a) - i32::from(b)).pow(2);
        d(cr, r) + d(cg, g) + d(cb, b)
    };
    if dist(grey.1) < dist(cube.1) {
        grey.0 as u8
    } else {
        cube.0 as u8
    }
}

/// The colour depth: truecolor when `COLORTERM` says `truecolor` or `24bit`.
pub fn depth_from(colorterm: Option<&str>) -> Depth {
    match colorterm {
        Some("truecolor" | "24bit") => Depth::TrueColor,
        _ => Depth::Indexed,
    }
}

/// `dark` or `light` (any case), the values of `STITCHWORT_THEME` and
/// `--theme`; `auto` and anything else is `None`.
pub fn theme_named(name: &str) -> Option<Theme> {
    match name.to_ascii_lowercase().as_str() {
        "dark" => Some(Theme::Dark),
        "light" => Some(Theme::Light),
        _ => None,
    }
}

/// The theme `COLORFGBG` (`foreground;background` or
/// `foreground;default;background`, ANSI colour numbers) implies.
pub fn theme_from_colorfgbg(value: &str) -> Option<Theme> {
    let background: u8 = value.rsplit(';').next()?.trim().parse().ok()?;
    Some(if background < 7 || background == 8 {
        Theme::Dark
    } else {
        Theme::Light
    })
}

/// The theme a terminal's answer to the OSC 11 query (`ESC ] 11 ; ?`)
/// implies: `ESC ] 11 ; rgb:RRRR/GGGG/BBBB` and a terminator (BEL or
/// `ESC \`), each component one to four hex digits. `None` if it isn't
/// such an answer.
pub fn theme_from_osc11(reply: &[u8]) -> Option<Theme> {
    let text = std::str::from_utf8(reply).ok()?;
    let at = text.find("]11;")?;
    let body = text[at + 4..].strip_prefix("rgb:")?;
    let body = body.split(['\u{7}', '\u{1b}']).next()?;
    let mut parts = body.split('/');
    let mut channel = || -> Option<f64> {
        let hex = parts.next()?;
        if hex.is_empty() || hex.len() > 4 {
            return None;
        }
        let value = u32::from_str_radix(hex, 16).ok()?;
        Some(f64::from(value) / f64::from(16u32.pow(hex.len() as u32) - 1))
    };
    let (r, g, b) = (channel()?, channel()?, channel()?);
    if parts.next().is_some() {
        return None;
    }
    let luma = 0.299 * r + 0.587 * g + 0.114 * b;
    Some(if luma > 0.5 {
        Theme::Light
    } else {
        Theme::Dark
    })
}

/// The theme, in the order the CLI documents: the explicit setting, then
/// what the terminal says (`ask`, run only if needed), then `COLORFGBG`,
/// then dark.
pub fn choose_theme(
    explicit: Option<Theme>,
    ask: impl FnOnce() -> Option<Theme>,
    colorfgbg: Option<&str>,
) -> Theme {
    explicit
        .or_else(ask)
        .or_else(|| colorfgbg.and_then(theme_from_colorfgbg))
        .unwrap_or(Theme::Dark)
}

static CURRENT: OnceLock<Palette> = OnceLock::new();

/// Sets the palette the process colours with; the first call wins.
pub fn set(palette: Palette) {
    let _ = CURRENT.set(palette);
}

/// The palette in use: the one [`set`] was given, else dark and truecolor.
pub fn current() -> Palette {
    CURRENT.get().copied().unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    const LIGHT: Palette = Palette {
        theme: Theme::Light,
        depth: Depth::TrueColor,
    };

    #[test]
    fn dark_is_mocha_and_light_is_latte() {
        let dark = Palette::default();
        assert_eq!(dark.open(Role::Keyword), "\u{1b}[38;2;203;166;247m");
        assert_eq!(LIGHT.open(Role::Keyword), "\u{1b}[38;2;136;57;239m");
    }

    #[test]
    fn only_latte_makes_the_weak_roles_bold() {
        assert_eq!(
            Palette::default().sgr(Role::Operator, ""),
            "38;2;137;220;235"
        );
        assert_eq!(LIGHT.sgr(Role::Operator, ""), "1;38;2;4;165;229");
        assert_eq!(LIGHT.sgr(Role::Keyword, ""), "38;2;136;57;239");
        // Asking for bold twice doesn't repeat it.
        assert_eq!(LIGHT.sgr(Role::Type, "1;4"), "1;4;38;2;223;142;29");
    }

    #[test]
    fn indexed_depth_uses_the_nearest_256_colour() {
        let dark = Palette {
            theme: Theme::Dark,
            depth: Depth::Indexed,
        };
        // Mocha's mauve (203, 166, 247) is nearest the cube's (215, 175, 255).
        assert_eq!(dark.sgr(Role::Keyword, ""), "38;5;183");
        assert_eq!(nearest_256(0, 0, 0), 16);
        assert_eq!(nearest_256(255, 255, 255), 231);
        // A grey is nearer the grey ramp than the cube.
        assert_eq!(nearest_256(128, 128, 128), 244);
        assert_eq!(nearest_256(124, 127, 147), 102);
    }

    #[test]
    fn depth_follows_colorterm() {
        assert_eq!(depth_from(Some("truecolor")), Depth::TrueColor);
        assert_eq!(depth_from(Some("24bit")), Depth::TrueColor);
        assert_eq!(depth_from(Some("")), Depth::Indexed);
        assert_eq!(depth_from(None), Depth::Indexed);
    }

    #[test]
    fn theme_choice_order() {
        let never = || -> Option<Theme> { panic!("not asked") };
        // An explicit setting wins, and the terminal isn't asked.
        assert_eq!(
            choose_theme(Some(Theme::Light), never, Some("15;0")),
            Theme::Light
        );
        // Then the terminal, over COLORFGBG.
        assert_eq!(
            choose_theme(None, || Some(Theme::Light), Some("15;0")),
            Theme::Light
        );
        // Then COLORFGBG, then dark.
        assert_eq!(choose_theme(None, || None, Some("0;15")), Theme::Light);
        assert_eq!(
            choose_theme(None, || None, Some("15;default;0")),
            Theme::Dark
        );
        assert_eq!(choose_theme(None, || None, Some("nonsense")), Theme::Dark);
        assert_eq!(choose_theme(None, || None, None), Theme::Dark);
        assert_eq!(theme_named("Light"), Some(Theme::Light));
        assert_eq!(theme_named("auto"), None);
    }

    #[test]
    fn osc11_replies() {
        assert_eq!(
            theme_from_osc11(b"\x1b]11;rgb:1e1e/1e1e/2e2e\x07"),
            Some(Theme::Dark)
        );
        assert_eq!(
            theme_from_osc11(b"\x1b]11;rgb:eff1/f1f5/f5f5\x1b\\"),
            Some(Theme::Light)
        );
        assert_eq!(
            theme_from_osc11(b"\x1b]11;rgb:f/f/f\x07"),
            Some(Theme::Light)
        );
        assert_eq!(
            theme_from_osc11(b"\x1b]11;rgb:00/00/00\x07"),
            Some(Theme::Dark)
        );
        assert_eq!(theme_from_osc11(b"\x1b]11;rgb:ff/ff\x07"), None);
        assert_eq!(theme_from_osc11(b"\x1b]11;rgb:zz/00/00\x07"), None);
        assert_eq!(theme_from_osc11(b"garbage"), None);
        assert_eq!(theme_from_osc11(b""), None);
    }
}
