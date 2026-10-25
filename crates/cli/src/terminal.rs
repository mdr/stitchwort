//! Keys mode on a Unix terminal, for `stitchwort run` and `run --reference`
//! (docs/proposals/terminal-io.md §4.3, §5): what `IO.console` and
//! `IO.keysMode` do there, and putting the terminal back however the run
//! ends.
//!
//! - **Keys mode** turns off line editing, echo, `IEXTEN`, `IXON` and
//!   `ICRNL` on standard input, if it's a terminal, and the suspend
//!   character, but keeps `ISIG`, so Ctrl-C and Ctrl-\ still stop the program
//!   (D1248). On standard output, if it's a terminal, it switches to the
//!   alternate screen, hides the cursor and turns off line wrapping. Changes
//!   use `TCSANOW`, so typed-ahead keys survive a switch (§4.4).
//! - **What was changed** is kept in [`KEYS`], so that whatever ends the run
//!   can undo exactly that: [`Restore`] when `run_main` returns (an
//!   unhandled `Fail` or `E-IO` included) or unwinds from a panic, the panic
//!   hook before the message is shown, and the signal thread
//!   ([`catch_signals`]) for `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT`.

use std::io::{self, IsTerminal, Write};
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, MutexGuard};

use nix::sys::signal::{self, SigSet, Signal};
use nix::sys::termios::{
    self, InputFlags, LocalFlags, OutputFlags, SetArg, SpecialCharacterIndices, Termios,
};
use stitchwort_driver::run::{ConsoleInfo, RunError, Terminal};

/// Alternate screen, hidden cursor, no line wrapping.
const ENTER_SCREEN: &[u8] = b"\x1b[?1049h\x1b[?25l\x1b[?7l";
/// The reverse, in the reverse order.
const LEAVE_SCREEN: &[u8] = b"\x1b[?7h\x1b[?25h\x1b[?1049l";

/// What keys mode changed, to undo it.
struct Saved {
    /// Standard input's settings before, if it's a terminal.
    settings: Option<Termios>,
    /// Whether the screen setup was written to standard output.
    screen: bool,
}

/// Keys mode, while it's on. Shared with the signal thread.
static KEYS: Mutex<Option<Saved>> = Mutex::new(None);

fn keys() -> MutexGuard<'static, Option<Saved>> {
    // A panic while it was held changes nothing that matters here.
    KEYS.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Writes `bytes` to standard output's descriptor directly, past Rust's
/// buffer and lock: the program's output is flushed first, and the signal
/// thread can't wait for a lock the main thread holds.
fn write_raw(bytes: &[u8]) -> io::Result<()> {
    let mut rest = bytes;
    while !rest.is_empty() {
        match rustix::io::write(io::stdout(), rest) {
            Ok(n) => rest = &rest[n..],
            Err(rustix::io::Errno::INTR) => {}
            Err(e) => return Err(e.into()),
        }
    }
    Ok(())
}

/// Undoes `saved`, as far as it can: errors are ignored, since there's
/// nothing better to do after a crash or a signal.
fn undo(saved: Saved) {
    if saved.screen {
        let _ = write_raw(LEAVE_SCREEN);
    }
    if let Some(settings) = saved.settings {
        let _ = termios::tcsetattr(io::stdin(), SetArg::TCSANOW, &settings);
    }
}

/// Leaves keys mode if it's on.
pub fn restore() {
    if let Some(saved) = keys().take() {
        undo(saved);
    }
}

/// Leaves keys mode when dropped: when the run returns, however it ended,
/// or unwinds from a panic.
pub struct Restore;

impl Drop for Restore {
    fn drop(&mut self) {
        restore();
    }
}

/// Blocks `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` in this thread and so
/// in every thread started after it, and starts a thread that waits for
/// them: it leaves keys mode if it's on, then lets the signal end the
/// process as it would have (§5). Also puts the terminal back before a
/// panic's message is shown. Call before any other thread starts.
pub fn catch_signals() {
    let mut set = SigSet::empty();
    for s in [
        Signal::SIGINT,
        Signal::SIGTERM,
        Signal::SIGHUP,
        Signal::SIGQUIT,
    ] {
        set.add(s);
    }
    if set.thread_block().is_err() {
        return;
    }
    let started = std::thread::Builder::new()
        .name("signals".into())
        .spawn(move || {
            let Ok(caught) = set.wait() else { return };
            restore();
            // Unblocked in this thread only, with its default action, the
            // signal ends the process with the status a shell expects.
            let mut one = SigSet::empty();
            one.add(caught);
            let _ = one.thread_unblock();
            let _ = signal::raise(caught);
            std::process::exit(128 + caught as i32);
        });
    if started.is_err() {
        // Without the thread nothing would see the signals: unblock them.
        let _ = set.thread_unblock();
        return;
    }
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        // Not `restore`: a panic while this thread holds the lock would
        // wait for itself.
        let held = match KEYS.try_lock() {
            Ok(mut keys) => keys.take(),
            Err(std::sync::TryLockError::Poisoned(p)) => p.into_inner().take(),
            Err(std::sync::TryLockError::WouldBlock) => None,
        };
        if let Some(saved) = held {
            undo(saved);
        }
        previous(info);
    }));
}

/// The pid of the Node process of `run --js`, once started (0 before).
static NODE: AtomicU32 = AtomicU32::new(0);

/// Records the Node process that [`wait_for_node`]'s signal thread forwards
/// to.
pub fn set_node(pid: u32) {
    NODE.store(pid, Ordering::SeqCst);
}

/// For `run --js` (§4.7, §5): the terminal is Node's to put back, so this
/// process must outlive Node rather than die at the first Ctrl-C, or the
/// shell would get its prompt back before the terminal is restored. Blocks
/// `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` in this thread and so in the
/// threads after it (a child process starts with none blocked), and starts a
/// thread that swallows them: the terminal's own `SIGINT` and `SIGQUIT`
/// reach Node directly, and `SIGTERM` and `SIGHUP` sent to this process alone
/// are passed on to Node. Call before any other thread starts.
pub fn wait_for_node() {
    let mut set = SigSet::empty();
    for s in [
        Signal::SIGINT,
        Signal::SIGTERM,
        Signal::SIGHUP,
        Signal::SIGQUIT,
    ] {
        set.add(s);
    }
    if set.thread_block().is_err() {
        return;
    }
    let started = std::thread::Builder::new()
        .name("signals".into())
        .spawn(move || {
            while let Ok(caught) = set.wait() {
                let pid = NODE.load(Ordering::SeqCst);
                if matches!(caught, Signal::SIGTERM | Signal::SIGHUP)
                    && let Ok(pid) = i32::try_from(pid)
                    && pid > 0
                {
                    let _ = signal::kill(nix::unistd::Pid::from_raw(pid), caught);
                }
            }
        });
    if started.is_err() {
        let _ = set.thread_unblock();
    }
}

/// The host's terminal for `IO.console` and `IO.keysMode`.
pub struct UnixTerminal;

impl Terminal for UnixTerminal {
    fn console(&mut self) -> ConsoleInfo {
        let output_is_terminal = io::stdout().is_terminal();
        // 0 by 0 when the size isn't known: a fresh pseudo-terminal's.
        let (columns, rows) = if output_is_terminal {
            rustix::termios::tcgetwinsize(io::stdout())
                .map(|size| (size.ws_col.into(), size.ws_row.into()))
                .unwrap_or((0, 0))
        } else {
            (0, 0)
        };
        ConsoleInfo {
            input_is_terminal: io::stdin().is_terminal(),
            output_is_terminal,
            columns,
            rows,
        }
    }

    fn keys_mode(&mut self, on: bool, output: &mut dyn Write) -> Result<(), RunError> {
        if keys().is_some() == on {
            return Ok(());
        }
        // What the program wrote comes first.
        output.flush().map_err(RunError::Write)?;
        let mut keys = keys();
        if on {
            let settings = if io::stdin().is_terminal() {
                let before =
                    termios::tcgetattr(io::stdin()).map_err(|e| RunError::Terminal(e.into()))?;
                termios::tcsetattr(io::stdin(), SetArg::TCSANOW, &keys_settings(&before))
                    .map_err(|e| RunError::Terminal(e.into()))?;
                Some(before)
            } else {
                None
            };
            let screen = io::stdout().is_terminal();
            // Saved before writing, so a failed write is still undone.
            *keys = Some(Saved { settings, screen });
            if screen {
                write_raw(ENTER_SCREEN).map_err(RunError::Write)?;
            }
        } else if let Some(saved) = keys.take() {
            if saved.screen {
                write_raw(LEAVE_SCREEN).map_err(RunError::Write)?;
            }
            if let Some(settings) = saved.settings {
                termios::tcsetattr(io::stdin(), SetArg::TCSANOW, &settings)
                    .map_err(|e| RunError::Terminal(e.into()))?;
            }
        }
        Ok(())
    }
}

/// `before` with keys mode's changes (§4.3).
fn keys_settings(before: &Termios) -> Termios {
    let mut keys = before.clone();
    keys.local_flags
        .remove(LocalFlags::ICANON | LocalFlags::ECHO | LocalFlags::IEXTEN);
    keys.input_flags
        .remove(InputFlags::IXON | InputFlags::ICRNL);
    // Frames end their lines with CR LF themselves; the terminal must not
    // turn that LF into CR LF again (CR CR LF).
    keys.output_flags.remove(OutputFlags::ONLCR);
    // A read returns as soon as there's one byte.
    keys.control_chars[SpecialCharacterIndices::VMIN as usize] = 1;
    keys.control_chars[SpecialCharacterIndices::VTIME as usize] = 0;
    // Ctrl-Z is a key, `Ctrl 'z'`: a suspended program would leave the
    // shell's terminal in keys mode.
    keys.control_chars[SpecialCharacterIndices::VSUSP as usize] = termios::_POSIX_VDISABLE;
    keys
}
