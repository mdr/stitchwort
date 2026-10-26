//! The runtime of a standalone executable (stage S3 of
//! docs/proposals/standalone-executables.md): what `stitchwort build` links
//! with the `program.o` it writes, as the static library
//! `libstitchwort_standalone.a`.
//!
//! The object provides the program, encoded by [`stitchwort_rt::encode`],
//! as two symbols: `sw_program`, its bytes, and `sw_program_len`, how many
//! there are. This library provides C `main`, which runs that program as
//! `stitchwort run` would run it, without the front end: no parser, checker
//! or source.
//!
//! - It catches the signals that would end the run (`catch_signals`) before
//!   any thread starts, so that Ctrl-C puts the terminal back.
//! - It decodes the program and runs it on the machine
//!   ([`stitchwort_rt::run_main_native`], with no native code until stage
//!   S5) on a thread with a big stack, with the Unix terminal, standard
//!   input locked and a `BufWriter` on standard output.
//! - It reports errors as `stitchwort run` does, without the excerpt of
//!   `main`'s source, which the binary doesn't have (§2.4), and exits with
//!   `run`'s statuses: 0, 1 for an unhandled `Fail`, 2 for a runtime error.

use std::io::{self, BufWriter, Write};

use stitchwort_rt::host::RunError;

/// The executable's allocator, as `stitchwort`'s: the machine allocates and
/// frees cells by the million.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// The exit status of a run that ended with an unhandled `Fail`.
pub const EXIT_FAIL: i32 = 1;
/// The exit status of a runtime error (`E-RESOURCE`, `E-IO`, `E-OUTPUT`),
/// and of a program this library can't read.
pub const EXIT_ERROR: i32 = 2;
/// The exit status of a panic, as for a Rust program.
pub const EXIT_PANIC: i32 = 101;

/// Runs the encoded program `bytes` as `stitchwort run` runs a program, on a
/// thread of [`stitchwort_host::NATIVE_STACK`] bytes, and reports how it
/// ended on standard error. Returns the exit status.
pub fn run_encoded(bytes: &'static [u8]) -> i32 {
    let ran = std::panic::catch_unwind(|| {
        stitchwort_host::with_stack(stitchwort_host::NATIVE_STACK, move || {
            run_on_this_thread(bytes)
        })
    });
    // The panic's message was shown by the panic hook, after it put the
    // terminal back.
    ran.unwrap_or(EXIT_PANIC)
}

fn run_on_this_thread(bytes: &[u8]) -> i32 {
    let (program, limits) = match stitchwort_rt::decode(bytes) {
        Ok(decoded) => decoded,
        Err(e) => {
            eprintln!("error: this executable's program can't be read: {}", e.0);
            return EXIT_ERROR;
        }
    };
    let mut input = io::stdin().lock();
    let mut output = BufWriter::new(io::stdout().lock());
    #[cfg(unix)]
    let (mut terminal, restore) = (
        stitchwort_host::terminal::UnixTerminal,
        stitchwort_host::terminal::Restore,
    );
    #[cfg(not(unix))]
    let (mut terminal, restore) = (stitchwort_rt::host::NoTerminal, ());
    // No native code until stage S5: the machine runs everything.
    let mut native = |_: &stitchwort_rt::Program, _: &stitchwort_rt::code::Image| None;
    let result = stitchwort_rt::run_main_native(
        &program,
        limits,
        &mut native,
        &mut input,
        &mut output,
        &mut terminal,
    );
    // Out of keys mode before an error is shown, so it's on the normal
    // screen.
    drop(restore);
    drop(output);
    match result {
        Ok(()) => 0,
        Err(e) => {
            let (status, text) = report(&e);
            let _ = io::stderr().write_all(text.as_bytes());
            status
        }
    }
}

/// The exit status for `error`, and what to print: `stitchwort run`'s
/// report without the excerpt of `main`'s source. An unhandled `Fail` is
/// `error: <msg>`; any other error is its diagnostic's code, message and
/// notes, as `stitchwort` renders a diagnostic with no source position.
pub fn report(error: &RunError) -> (i32, String) {
    if let RunError::Failed(msg) = error {
        return (EXIT_FAIL, format!("error: {msg}\n"));
    }
    let diagnostic = error.diagnostic(stitchwort_syntax::Span::NOWHERE);
    let mut text = format!("[{}] Error: {}\n", diagnostic.code, diagnostic.message);
    for note in &diagnostic.notes {
        text.push_str(&format!("  note: {note}\n"));
    }
    (EXIT_ERROR, text)
}

// The program, from the `program.o` that `stitchwort build` writes.
#[cfg(not(test))]
#[allow(unsafe_code)]
unsafe extern "C" {
    /// The encoded program's first byte.
    static sw_program: u8;
    /// How many bytes it has.
    static sw_program_len: usize;
}

/// The executable's entry point.
#[cfg(not(test))]
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub extern "C" fn main(
    _argc: std::ffi::c_int,
    _argv: *const *const std::ffi::c_char,
) -> std::ffi::c_int {
    // Rust's own start-up, which a C `main` skips, ignores `SIGPIPE`, so that
    // writing to a closed pipe is an error the program sees (`E-IO`) rather
    // than the end of the process; `stitchwort run` behaves so.
    #[cfg(unix)]
    // SAFETY: `SigIgn` installs no handler of ours, and no other thread has
    // started yet that could be changing signal dispositions.
    unsafe {
        let _ = nix::sys::signal::signal(
            nix::sys::signal::Signal::SIGPIPE,
            nix::sys::signal::SigHandler::SigIgn,
        );
    }
    #[cfg(unix)]
    stitchwort_host::terminal::catch_signals();
    // SAFETY: `program.o` defines `sw_program` as `sw_program_len` bytes of
    // read-only data, which live as long as the process; nothing writes them.
    let bytes = unsafe { std::slice::from_raw_parts(&raw const sw_program, sw_program_len) };
    run_encoded(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_fail_is_reported_with_status_1() {
        let (status, text) = report(&RunError::Failed("boom".into()));
        assert_eq!((status, text.as_str()), (1, "error: boom\n"));
    }

    #[test]
    fn a_runtime_error_is_its_code_and_message_with_status_2() {
        let (status, text) = report(&RunError::Deep("`Main.deep` (3 calls)".into()));
        assert_eq!(status, 2);
        assert!(
            text.starts_with("[E-RESOURCE] Error: ran out of resources: "),
            "{text}"
        );
        assert!(
            text.ends_with("\n  note: the recursion was deepest in `Main.deep` (3 calls)\n"),
            "{text}"
        );
    }

    #[test]
    fn bytes_that_arent_a_program_are_an_error() {
        assert_eq!(run_encoded(b"not a program"), EXIT_ERROR);
    }
}
