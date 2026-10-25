//! What a runner of `main` shares with the host: how input is read, and the
//! errors a run can stop with. Used by both the reference runner
//! (`stitchwort_driver::run`) and the runtime's ([`crate::run`]), so that
//! they read input and report errors exactly alike.

use std::fmt;
use std::io::{self, BufRead, Write};

use stitchwort_core::ResourceError;
use stitchwort_syntax::{Diagnostic, Span};

/// Why a run stopped early.
#[derive(Debug)]
pub enum RunError {
    /// Evaluating the program ran out of resources.
    Resource(ResourceError),
    /// Reading standard input failed.
    Read(io::Error),
    /// Line `line` (counting from 1) of the input isn't valid UTF-8.
    /// For `readAll`, the first line that isn't.
    InvalidUtf8 { line: usize },
    /// Writing or flushing standard output failed.
    Write(io::Error),
    /// Changing the terminal's settings for keys mode failed.
    Terminal(io::Error),
    /// The program couldn't be lowered for the machine (`E-RESOURCE` for
    /// nesting too deep, or an internal error). Only the machine reports it.
    Lowering(Diagnostic),
    /// The program printed more than `max` bytes, its output limit: in the
    /// whole run, or since it last waited for input (a live run's
    /// [`crate::run::LimitScope`]).
    OutputLimit { max: usize },
    /// `main` failed with this message, and nothing handled it
    /// (`Fail`, docs/proposals/errors.md §3.5). The runner reports it as
    /// `error: <msg>` and exits with 1; it is not a runtime error.
    Failed(String),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Resource(e) => write!(f, "ran out of resources: {e}"),
            RunError::Read(e) => write!(f, "can't read standard input: {e}"),
            RunError::InvalidUtf8 { line } => {
                write!(f, "line {line} of standard input isn't valid UTF-8")
            }
            RunError::Write(e) => write!(f, "can't write standard output: {e}"),
            RunError::Terminal(e) => write!(f, "can't change the terminal's settings: {e}"),
            RunError::Lowering(d) => write!(f, "{}", d.message),
            RunError::OutputLimit { max } => {
                write!(f, "the program printed more than {max} bytes, its limit")
            }
            RunError::Failed(msg) => write!(f, "{msg}"),
        }
    }
}

impl RunError {
    /// The error to report: `E-RESOURCE`, pointing at where `main` is
    /// defined, or `E-IO`.
    pub fn diagnostic(&self, main: impl Into<Span>) -> Diagnostic {
        let main = main.into();
        match self {
            RunError::Resource(e) => {
                Diagnostic::from(*e).with_label(main, "while running this program")
            }
            RunError::Lowering(d) => d.clone(),
            RunError::OutputLimit { .. } => Diagnostic::error("E-OUTPUT", self.to_string())
                .with_label(main, "while running this program"),
            RunError::Failed(msg) => Diagnostic::error("E-FAIL", msg.clone()),
            _ => Diagnostic::error("E-IO", self.to_string()),
        }
    }
}

impl From<ResourceError> for RunError {
    fn from(e: ResourceError) -> RunError {
        RunError::Resource(e)
    }
}

/// The next line of input without its line ending, or `None` at the end.
/// `lines` counts the lines read so far.
pub fn read_line(input: &mut impl BufRead, lines: &mut usize) -> Result<Option<String>, RunError> {
    let mut bytes = Vec::new();
    if input
        .read_until(b'\n', &mut bytes)
        .map_err(RunError::Read)?
        == 0
    {
        return Ok(None);
    }
    *lines += 1;
    if bytes.last() == Some(&b'\n') {
        bytes.pop();
        if bytes.last() == Some(&b'\r') {
            bytes.pop();
        }
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| RunError::InvalidUtf8 { line: *lines })
}

/// What `IO.console` reports (docs/proposals/terminal-io.md §4.2).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConsoleInfo {
    pub input_is_terminal: bool,
    pub output_is_terminal: bool,
    /// The terminal's size; 0 by 0 when it isn't known.
    pub columns: u64,
    pub rows: u64,
}

/// The terminal side of the host: what `IO.console` and `IO.keysMode` do
/// (docs/proposals/terminal-io.md §4.6). `crates/rt` is also built for
/// WebAssembly, so the terminal implementation lives in `crates/cli`; here
/// there's only [`NoTerminal`].
pub trait Terminal {
    /// What `IO.console` gives.
    fn console(&mut self) -> ConsoleInfo;

    /// Enters (`on`) or leaves keys mode; nothing if it's already so. Any
    /// screen setup is written to `output`, which this flushes when it
    /// writes. `output` is the program's own, so the setup lands in order
    /// with what the program printed.
    fn keys_mode(&mut self, on: bool, output: &mut dyn Write) -> Result<(), RunError>;
}

impl<T: Terminal + ?Sized> Terminal for &mut T {
    fn console(&mut self) -> ConsoleInfo {
        (**self).console()
    }

    fn keys_mode(&mut self, on: bool, output: &mut dyn Write) -> Result<(), RunError> {
        (**self).keys_mode(on, output)
    }
}

/// A host without a terminal: `IO.console` says neither side is one, with
/// the size unknown, and keys mode changes nothing. The playground, the
/// tests, and every runner off Unix.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoTerminal;

impl Terminal for NoTerminal {
    fn console(&mut self) -> ConsoleInfo {
        ConsoleInfo::default()
    }

    fn keys_mode(&mut self, _on: bool, _output: &mut dyn Write) -> Result<(), RunError> {
        Ok(())
    }
}

/// The bytes of one read, for `IO.readBytes`: what `input` has buffered, or
/// one read if nothing is; `None` at the end. `lines` counts the line
/// endings taken, so that a later `readLine`'s errors name the right line.
pub fn read_bytes(
    input: &mut impl BufRead,
    lines: &mut usize,
) -> Result<Option<Vec<u8>>, RunError> {
    let bytes = input.fill_buf().map_err(RunError::Read)?.to_vec();
    input.consume(bytes.len());
    if bytes.is_empty() {
        return Ok(None);
    }
    *lines += bytes.iter().filter(|&&b| b == b'\n').count();
    Ok(Some(bytes))
}

/// `IO.write`: the text, with no line ending, then a flush.
pub fn write_text(output: &mut impl Write, text: &str) -> Result<(), RunError> {
    output
        .write_all(text.as_bytes())
        .and_then(|()| output.flush())
        .map_err(RunError::Write)
}

/// Everything that remains of the input. `lines` counts the lines read so
/// far, a last line without a line ending included.
pub fn read_all(input: &mut impl BufRead, lines: &mut usize) -> Result<String, RunError> {
    let mut bytes = Vec::new();
    input.read_to_end(&mut bytes).map_err(RunError::Read)?;
    match String::from_utf8(bytes) {
        Ok(text) => {
            *lines += text.lines().count();
            Ok(text)
        }
        Err(e) => {
            let valid = &e.as_bytes()[..e.utf8_error().valid_up_to()];
            let before = valid.iter().filter(|&&b| b == b'\n').count();
            Err(RunError::InvalidUtf8 {
                line: *lines + before + 1,
            })
        }
    }
}

/// Where a fresh random number comes from. A native build uses the
/// operating system's entropy (see [`random_seed`]); the browser, where the
/// standard library has none, installs `crypto.getRandomValues` with
/// [`set_random_source`].
static RANDOM_SOURCE: std::sync::OnceLock<fn() -> u64> = std::sync::OnceLock::new();

/// Replaces the source of [`random_seed`]. Only the first call has an effect.
pub fn set_random_source(source: fn() -> u64) {
    let _ = RANDOM_SOURCE.set(source);
}

/// A fresh 64-bit number for `IO.randomSeed`. By default it is the output of
/// a hasher keyed by `std`'s `RandomState`, whose keys the standard library
/// takes from the operating system's entropy (`getrandom` on Linux,
/// `arc4random_buf` on macOS): no new dependency.
pub fn random_seed() -> u64 {
    use std::hash::{BuildHasher, Hasher};
    match RANDOM_SOURCE.get() {
        Some(source) => source(),
        None => std::collections::hash_map::RandomState::new()
            .build_hasher()
            .finish(),
    }
}
