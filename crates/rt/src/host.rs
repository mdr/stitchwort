//! What a runner of `main` shares with the host: how input is read, and the
//! errors a run can stop with. Used by both the reference runner
//! (`stitchwort_driver::run`) and the runtime's ([`crate::run`]), so that
//! they read input and report errors exactly alike.

use std::fmt;
use std::io::{self, BufRead};

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
    /// The program couldn't be lowered for the machine (`E-RESOURCE` for
    /// nesting too deep, or an internal error). Only the machine reports it.
    Lowering(Diagnostic),
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
            RunError::Lowering(d) => write!(f, "{}", d.message),
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
