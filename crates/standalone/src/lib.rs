//! The runtime of a standalone executable (stage S3 of
//! docs/proposals/standalone-executables.md): what `stitchwort build` links
//! with the `program.o` it writes, as the static library
//! `libstitchwort_standalone.a`.
//!
//! The object defines `sw_native_manifest` (`stitchwort_rt::native_aot`),
//! which names one of this library's two ways of running the executable,
//! and gives it its data. This library provides C `main`, which calls that
//! way, and runs the program as `stitchwort run` would run it, without the
//! front end: no parser, checker or source.
//!
//! - It catches the signals that would end the run (`catch_signals`) before
//!   any thread starts, so that Ctrl-C puts the terminal back.
//! - Built with `--native`, the way is [`sw_run_native`]: it reads the
//!   tables and literals (`stitchwort_rt::linked`) and runs the program as
//!   `run --native` does ([`stitchwort_rt::run_main_linked`]): every body
//!   `main` reaches as native code, as `stitchwort build --native` compiled
//!   them (stage S5: [`aot`]; stage NO4 of native-only.md: the entry too),
//!   on a thread with the stack the build sized for them (stage NO5), with
//!   no program, image, codec or machine (stage NO6).
//! - Built without, the way is [`sw_run_machine`]: it decodes the program
//!   (`stitchwort_rt::decode`) and runs it on the machine.
//!
//! `main` refers to neither way itself, so the linker keeps only the one
//! the object names: an executable built with `--native` has no machine in
//! it. Either way it runs with the Unix terminal, standard input locked and
//! a `BufWriter` on standard output, and reports errors as `stitchwort run`
//! does, without the excerpt of `main`'s source, which the binary doesn't
//! have (§2.4), with `run`'s exit statuses: 0, 1 for an unhandled `Fail`, 2
//! for a runtime error.

use std::io::{self, BufWriter, Write};

use stitchwort_rt::host::RunError;
use stitchwort_rt::native_aot::Manifest;
#[cfg(not(test))]
use stitchwort_rt::native_aot::RunExecutable;

pub mod aot;

/// The executable's allocator, as `stitchwort`'s: the runtime allocates and
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

/// The stack an executable without native code runs the machine on: as
/// `stitchwort run`'s.
pub const MACHINE_STACK: usize = 64 * 1024 * 1024;

/// Runs `run` on a thread with a stack of `stack` bytes. Returns its exit
/// status, or, if the stack can't be reserved, says so and returns
/// [`EXIT_ERROR`] before running anything.
fn on_stack(stack: usize, run: impl FnOnce() -> i32 + Send) -> i32 {
    let ran = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        stitchwort_host::try_with_stack(stack, run)
    }));
    match ran {
        Ok(Ok(status)) => status,
        Ok(Err(e)) => {
            eprintln!("error: this executable can't reserve its stack of {stack} bytes: {e}");
            EXIT_ERROR
        }
        // The panic's message was shown by the panic hook, after it put the
        // terminal back.
        Err(_) => EXIT_PANIC,
    }
}

/// Runs the encoded program `bytes` on the machine as `stitchwort run`
/// runs a program, and reports how it ended on standard error. Returns the
/// exit status.
pub fn run_encoded(bytes: &'static [u8]) -> i32 {
    on_stack(MACHINE_STACK, move || {
        let (program, limits) = match stitchwort_rt::decode(bytes) {
            Ok(decoded) => decoded,
            Err(e) => {
                eprintln!("error: this executable's program can't be read: {}", e.0);
                return EXIT_ERROR;
            }
        };
        with_terminal(|input, output, terminal| {
            stitchwort_rt::run_main_on(&program, limits, input, output, terminal)
        })
    })
}

/// Runs the native code `manifest` describes, with its tables and literals,
/// as `stitchwort run --native` runs a program, on a thread with the stack
/// the build sized, and reports how it ended. Returns the exit status. If
/// the code can't run here, says so and returns [`EXIT_ERROR`] with nothing
/// run.
///
/// # Safety
/// `manifest` is `sw_native_manifest`, as the compiler wrote it, with its
/// data and code linked into this executable.
#[allow(unsafe_code)]
pub unsafe fn run_native(manifest: &'static Manifest) -> i32 {
    let stack = manifest.stack_size as usize;
    on_stack(stack, move || {
        // SAFETY: the caller's contract. A mismatch ends the process with
        // nothing done.
        let aot::Linked {
            islands,
            outline,
            limits,
        } = match unsafe { aot::AotIslands::read(manifest) } {
            Ok(linked) => linked,
            Err(aot::Mismatch(why)) => {
                eprintln!("internal error: this executable can't run: {why}");
                return EXIT_ERROR;
            }
        };
        with_terminal(|input, output, terminal| {
            stitchwort_rt::run_main_linked(
                outline,
                Box::new(islands),
                limits,
                stack,
                input,
                output,
                terminal,
            )
        })
    })
}

/// Runs `run` with standard input, a buffered standard output and the
/// terminal, then reports how it ended. Returns the exit status.
fn with_terminal(
    run: impl FnOnce(
        &mut io::StdinLock<'static>,
        &mut BufWriter<io::StdoutLock<'static>>,
        &mut dyn stitchwort_rt::host::Terminal,
    ) -> Result<(), RunError>,
) -> i32 {
    let mut input = io::stdin().lock();
    let mut output = BufWriter::new(io::stdout().lock());
    #[cfg(unix)]
    let (mut terminal, restore) = (
        stitchwort_host::terminal::UnixTerminal,
        stitchwort_host::terminal::Restore,
    );
    #[cfg(not(unix))]
    let (mut terminal, restore) = (stitchwort_rt::host::NoTerminal, ());
    let result = run(&mut input, &mut output, &mut terminal);
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

/// The way an executable built without `--native` runs: its encoded
/// program on the machine ([`run_encoded`]). Named by the object's
/// manifest (`native_aot::RUN_MACHINE`).
///
/// # Safety
/// `manifest` is `sw_native_manifest`, whose data is the encoded program.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_run_machine(manifest: &'static Manifest) -> i32 {
    // SAFETY: the caller's contract.
    run_encoded(unsafe { manifest.data() })
}

/// The way an executable built with `--native` runs ([`run_native`]).
/// Named by the object's manifest (`native_aot::RUN_NATIVE`).
///
/// # Safety
/// As [`run_native`].
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_run_native(manifest: &'static Manifest) -> i32 {
    // SAFETY: the caller's contract.
    unsafe { run_native(manifest) }
}

// The manifest, from the `program.o` that `stitchwort build` writes.
#[cfg(not(test))]
#[allow(unsafe_code)]
unsafe extern "C" {
    static sw_native_manifest: Manifest;
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
    // SAFETY: `program.o` defines `sw_native_manifest` as a manifest
    // (`stitchwort_rt::native_aot`), read-only for the process's life.
    let manifest = unsafe { &sw_native_manifest };
    if let Err(aot::Mismatch(why)) = aot::check_version(manifest) {
        eprintln!("internal error: this executable can't run: {why}");
        return EXIT_ERROR;
    }
    if manifest.run.is_null() {
        eprintln!("internal error: this executable can't run: its manifest names no way to run it");
        return EXIT_ERROR;
    }
    // SAFETY: the compiler wrote `run` as the address of `sw_run_native` or
    // `sw_run_machine`, which have this type.
    let run = unsafe { std::mem::transmute::<*const u8, RunExecutable>(manifest.run) };
    // SAFETY: `manifest` is the one `run` was written into, with its data.
    unsafe { run(manifest) }
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
