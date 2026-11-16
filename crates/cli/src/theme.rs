//! Which palette the terminal colours use: the theme (the explicit setting,
//! else what the terminal says its background is, else `COLORFGBG`, else
//! dark) and the colour depth (`COLORTERM`). The palette itself is
//! [`stitchwort_driver::palette`].

use std::io::IsTerminal;
use std::sync::Once;

use stitchwort_driver::palette::{self, Palette, Theme};

/// `--theme`'s value: 0 `auto`, 1 `dark`, 2 `light`.
pub static THEME_FLAG: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Fixes the process's palette, once, the first time something is to be
/// coloured. Asks the terminal only here, so a run that never colours
/// never does.
pub fn init() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let flag = match THEME_FLAG.load(std::sync::atomic::Ordering::Relaxed) {
            1 => Some(Theme::Dark),
            2 => Some(Theme::Light),
            _ => None,
        };
        let explicit = flag.or_else(|| {
            std::env::var("STITCHWORT_THEME")
                .ok()
                .and_then(|name| palette::theme_named(&name))
        });
        let colorfgbg = std::env::var("COLORFGBG").ok();
        let theme = palette::choose_theme(explicit, ask_terminal, colorfgbg.as_deref());
        let depth = palette::depth_from(std::env::var("COLORTERM").ok().as_deref());
        palette::set(Palette { theme, depth });
    });
}

/// How long to wait for the terminal's answer.
#[cfg(unix)]
const WAIT_TENTHS: u8 = 1;

/// Asks the terminal for its background colour (OSC 11), when stdin and
/// stdout are both terminals; `None` if it doesn't answer within about
/// 100 ms. The terminal is put in raw mode for the question and restored.
#[cfg(unix)]
fn ask_terminal() -> Option<Theme> {
    use nix::sys::termios::{self, LocalFlags, SetArg, SpecialCharacterIndices};
    use std::io::Write;

    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    if !stdin.is_terminal() || !stdout.is_terminal() {
        return None;
    }
    let saved = termios::tcgetattr(&stdin).ok()?;
    let mut raw = saved.clone();
    raw.local_flags
        .remove(LocalFlags::ICANON | LocalFlags::ECHO);
    // A read returns when something arrives, or after the wait with nothing.
    raw.control_chars[SpecialCharacterIndices::VMIN as usize] = 0;
    raw.control_chars[SpecialCharacterIndices::VTIME as usize] = WAIT_TENTHS;
    termios::tcsetattr(&stdin, SetArg::TCSAFLUSH, &raw).ok()?;
    let answer = (|| {
        let mut out = stdout.lock();
        out.write_all(b"\x1b]11;?\x07").ok()?;
        out.flush().ok()?;
        let mut reply = Vec::new();
        let mut byte = [0u8; 1];
        while reply.len() < 64 {
            if nix::unistd::read(&stdin, &mut byte).ok()? == 0 {
                break;
            }
            reply.push(byte[0]);
            if byte[0] == 0x07 || reply.ends_with(b"\x1b\\") {
                break;
            }
        }
        palette::theme_from_osc11(&reply)
    })();
    let _ = termios::tcsetattr(&stdin, SetArg::TCSAFLUSH, &saved);
    answer
}

#[cfg(not(unix))]
fn ask_terminal() -> Option<Theme> {
    None
}
