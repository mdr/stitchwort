//! Live runs for the playground (docs/proposals/playground-live-keys.md):
//! a `Terminal` program that gets its keys as the page sees them. The run
//! returns to JavaScript whenever the program waits for a key, so the worker
//! is free between keys, and goes on when the page pushes the next one.
//!
//! The page drives it: `push` one message per key (Ctrl-C is the byte 3 and
//! stops the run, D1274), `advance` to run until the program waits again, and
//! `close` for the end of the input. The time limit is the page's, per
//! stretch (D1275): it starts a timer at each `advance` and stops it when the
//! answer is `waiting`. The output cap is the run's, per stretch too.

use std::io::{self, Write};
use std::rc::Rc;

use stitchwort_driver::driver::Session;
use stitchwort_driver::run::{Main, RunError};
use stitchwort_rt::host::{ConsoleInfo, Terminal};
use stitchwort_rt::{Advanced, LimitScope, LiveLimits, LiveRun};
use wasm_bindgen::prelude::wasm_bindgen;

use super::{OutputSink, failure, json_string, rendered, use_browser_entropy};

/// The size of the page's terminal grid, as `IO.console` reports it (and as
/// `Terminal.simulate` assumes).
pub const COLUMNS: u64 = 80;
pub const ROWS: u64 = 24;

/// How much a program may print in one stretch between waits (D1275).
pub const MAX_STRETCH_OUTPUT: usize = 256 * 1024;

/// Alternate screen, hidden cursor, no line wrapping; and the reverse, as
/// the native terminal writes them (crates/host/src/terminal.rs).
const ENTER_SCREEN: &[u8] = b"\x1b[?1049h\x1b[?25l\x1b[?7l";
const LEAVE_SCREEN: &[u8] = b"\x1b[?7h\x1b[?25h\x1b[?1049l";

/// The page's terminal: a terminal of 80 by 24 on both sides, whose keys
/// mode writes the screen codes for the page to act on, in order with the
/// program's output.
#[derive(Default)]
struct PageTerminal {
    keys: bool,
}

impl Terminal for PageTerminal {
    fn console(&mut self) -> ConsoleInfo {
        ConsoleInfo {
            input_is_terminal: true,
            output_is_terminal: true,
            columns: COLUMNS,
            rows: ROWS,
        }
    }

    fn keys_mode(&mut self, on: bool, output: &mut dyn Write) -> Result<(), RunError> {
        if self.keys == on {
            return Ok(());
        }
        // What the program wrote comes first.
        output.flush().map_err(RunError::Write)?;
        self.keys = on;
        let codes = if on { ENTER_SCREEN } else { LEAVE_SCREEN };
        output
            .write_all(codes)
            .and_then(|()| output.flush())
            .map_err(RunError::Write)
    }
}

/// What a stretch of the program wrote, handed on at each flush.
struct Passing<'a> {
    pass: &'a mut dyn FnMut(&str),
    pending: Vec<u8>,
}

impl Write for Passing<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.pending.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if !self.pending.is_empty() {
            (self.pass)(&String::from_utf8_lossy(&self.pending));
            self.pending.clear();
        }
        Ok(())
    }
}

/// A run of `main` that waits for keys by returning to JavaScript.
#[wasm_bindgen]
pub struct LiveSession {
    // Kept to render errors with.
    session: Session,
    main: Main,
    run: LiveRun,
}

/// Starts a live run of `source`'s `main`; the first `advance` runs it to
/// its first wait. A failure is the other entry points' answer:
/// `{"ok":false,"errors":"…"}`.
#[wasm_bindgen]
pub fn start_live(source: &str) -> Result<LiveSession, String> {
    let mut session = super::load(source)?;
    let main = session
        .main()
        .map_err(|error| failure(&rendered(&session, &[error])))?;
    live_from(session, main)
}

/// [`start_live`] for a loaded session and its `main`.
pub(crate) fn live_from(session: Session, main: Main) -> Result<LiveSession, String> {
    use_browser_entropy();
    let program = session
        .lower_fast(&main)
        .map_err(|error| failure(&rendered(&session, &[error.diagnostic(main.span)])))?;
    let limits = LiveLimits {
        machine: stitchwort_rt::Limits::from_core(session.elab.limits),
        max_output: Some(MAX_STRETCH_OUTPUT),
        scope: LimitScope::EachStretch,
    };
    let run = LiveRun::new(Rc::new(program), limits, Box::new(PageTerminal::default()))
        .map_err(|error| failure(&rendered(&session, &[error.diagnostic(main.span)])))?;
    Ok(LiveSession { session, main, run })
}

#[wasm_bindgen]
impl LiveSession {
    /// One key's bytes (or a typed line), as one read. Ctrl-C (3) stops the
    /// run at the next `advance`.
    pub fn push(&mut self, bytes: &[u8]) {
        self.run.push(bytes);
    }

    /// The end of the input (Ctrl-D on an empty line).
    pub fn close(&mut self) {
        self.run.close();
    }

    /// Runs until the program waits for a key, sending what it writes to
    /// `sink` (a `write(text)` method). Returns `{"state":"waiting"}`,
    /// `{"state":"finished"}`, `{"state":"interrupted"}`,
    /// `{"state":"ended"}` (it had ended already) or
    /// `{"state":"failed","errors":"…"}`.
    pub fn advance(&mut self, sink: &OutputSink) -> String {
        self.advance_to(&mut |text| sink.write(text))
    }
}

impl LiveSession {
    /// [`LiveSession::advance`] with a Rust function for the output.
    pub fn advance_to(&mut self, pass: &mut dyn FnMut(&str)) -> String {
        let mut output = Passing {
            pass,
            pending: Vec::new(),
        };
        let advanced = self.run.advance(&mut output);
        // Whatever an error left unflushed still shows.
        let _ = output.flush();
        let state = |name: &str| format!(r#"{{"state":"{name}"}}"#);
        match advanced {
            Ok(Advanced::Waiting) => state("waiting"),
            Ok(Advanced::Finished) => state("finished"),
            Ok(Advanced::Interrupted) => state("interrupted"),
            Ok(Advanced::Ended) => state("ended"),
            Err(error) => {
                let errors = match error {
                    // Unhandled `Fail` (D1048): shown like the CLI prints it.
                    RunError::Failed(msg) => format!("error: {msg}\n"),
                    error => rendered(&self.session, &[error.diagnostic(self.main.span)]),
                };
                format!(r#"{{"state":"failed","errors":{}}}"#, json_string(&errors))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const WALK: &str = include_str!("../../../examples/accept/terminal-walk.sw");

    /// Pushes `keys` one by one, collecting the output of each stretch;
    /// returns the stretches and the last state.
    fn play(source: &str, keys: &[&[u8]]) -> (Vec<String>, String) {
        let source = source.to_string();
        let keys: Vec<Vec<u8>> = keys.iter().map(|k| k.to_vec()).collect();
        // A big stack, as the other tests here have.
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || {
                let mut live = start_live(&source).unwrap_or_else(|e| panic!("{e}"));
                let mut stretches = Vec::new();
                let mut state = String::new();
                for step in 0..=keys.len() {
                    let mut out = String::new();
                    state = live.advance_to(&mut |t| out.push_str(t));
                    stretches.push(out);
                    if step < keys.len() {
                        live.push(&keys[step]);
                    }
                }
                (stretches, state)
            })
            .expect("a thread")
            .join()
            .expect("no panic")
    }

    /// Without the escape codes the grid would act on.
    fn plain(frame: &str) -> String {
        let mut out = String::new();
        let mut chars = frame.chars();
        while let Some(c) = chars.next() {
            if c == '\x1b' {
                for c in chars.by_ref() {
                    if c.is_ascii_alphabetic() || c == '~' {
                        break;
                    }
                }
            } else {
                out.push(c);
            }
        }
        out
    }

    #[test]
    fn the_walk_plays_key_by_key() {
        let (stretches, state) = play(WALK, &[b"l", b"\x1b[B", b"x", b"q"]);
        assert_eq!(state, r#"{"state":"finished"}"#);
        assert!(
            stretches[0].starts_with("\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[H"),
            "{:?}",
            stretches[0]
        );
        assert!(plain(&stretches[0]).contains("#@.........#"));
        assert!(plain(&stretches[1]).contains("#.@........#"));
        assert!(plain(&stretches[2]).contains("#.@........#"));
        // The last stretch leaves keys mode, then prints.
        let last = &stretches[4];
        assert!(last.contains("\x1b[?1049l"), "{last:?}");
        assert!(
            last.ends_with("The @ stopped at column 1, row 1.\n"),
            "{last:?}"
        );
    }

    #[test]
    fn ctrl_c_stops_the_run_and_leaves_keys_mode() {
        let (stretches, state) = play(WALK, &[b"l", &[3]]);
        assert_eq!(state, r#"{"state":"interrupted"}"#);
        assert!(stretches[2].contains("\x1b[?1049l"), "{:?}", stretches[2]);
    }

    #[test]
    fn read_line_waits_for_a_whole_line() {
        let source = "def main () : {IO} () :=\n  match IO.readLine () with\n    | None => IO.print \"none\"\n    | Some l => IO.print \"got ${l}\"\n";
        let (stretches, state) = play(source, &[b"ab", b"c\n"]);
        assert_eq!(state, r#"{"state":"finished"}"#);
        assert_eq!(stretches[0], "");
        assert_eq!(stretches[1], "");
        assert_eq!(stretches[2], "got abc\n");
    }
}
