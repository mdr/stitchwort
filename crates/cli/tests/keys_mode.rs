//! `stitchwort run` in a pseudo-terminal (docs/proposals/terminal-io.md
//! §4.3, §5): `IO.keysMode` changes the terminal's settings, `print` leaves
//! keys mode (D1260), and the settings are put back however the run ends:
//! normally, by an unhandled `Fail`, by `E-IO`, and by Ctrl-C (which still
//! stops the program, D1248). The pseudo-terminal is `pty/mod.rs`'s.

#![cfg(unix)]

mod pty;

use std::ffi::OsStr;
use std::path::PathBuf;

use pty::{ENTER_SCREEN, LEAVE_SCREEN, Session, assert_keys_mode_settings};

fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-keys-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

/// `stitchwort run --no-cache` on `source`, in a pseudo-terminal of 100 by
/// 30. With `js`, the program runs under Node (`run --js`); with
/// `piped_output`, standard output is a pipe instead of the terminal.
fn start(name: &str, source: &str, piped_output: bool, js: bool) -> Option<Session> {
    let path = source_file(&format!("{}{name}", if js { "js-" } else { "" }), source);
    let mut command: Vec<&OsStr> = vec![
        OsStr::new(env!("CARGO_BIN_EXE_stitchwort")),
        OsStr::new("run"),
        OsStr::new("--no-cache"),
    ];
    if js {
        command.push(OsStr::new("--js"));
    }
    command.push(path.as_os_str());
    Session::start(&command, piped_output)
}

fn keys_mode_then_print_then_normal_exit(js: bool) {
    let Some(mut s) = start(
        "normal.sw",
        "import Std (IO, Console, Nat)\n\n\
         def main(): {IO} () :=\n  \
           let console := IO.console()\n  \
           IO.print \"size ${console.columns.toText}x${console.rows.toText} ${if console.inputIsTerminal && console.outputIsTerminal then \"terminals\" else \"not\"}\"\n  \
           IO.keysMode True\n  \
           IO.write \"frame\"\n  \
           let key := IO.readBytes()\n  \
           IO.print \"got ${if key == Some [97] then \"a\" else \"?\"}\"\n  \
           let line := IO.readLine()\n  \
           IO.print \"line ${if line == Some \"typed\" then \"ok\" else \"?\"}\"\n  \
           IO.keysMode True\n",
        false,
        js,
    ) else {
        return;
    };
    s.wait_for_keys_mode(true);
    assert_keys_mode_settings(&s.settings());
    s.wait_for_screen("frame");
    // One key, with no Enter.
    s.type_keys(b"a");
    // `print` left keys mode, so `readLine` reads an edited, echoed line.
    s.wait_for_screen("got a");
    s.wait_for_keys_mode(false);
    s.type_keys(b"typed\n");
    let (code, errors) = s.wait();
    assert_eq!(code, 0, "{errors}");
    // The program ended in keys mode; the runner left it.
    s.assert_restored();
    s.wait_for_screen("line ok");
    let screen = s.screen();
    assert!(screen.contains("size 100x30 terminals"), "{screen:?}");
    // Entered twice and left twice, in order.
    let enters: Vec<_> = screen.match_indices(ENTER_SCREEN).map(|(i, _)| i).collect();
    let leaves: Vec<_> = screen.match_indices(LEAVE_SCREEN).map(|(i, _)| i).collect();
    assert_eq!((enters.len(), leaves.len()), (2, 2), "{screen:?}");
    assert!(enters[0] < screen.find("frame").unwrap());
    assert!(leaves[0] < screen.find("got a").unwrap());
    assert!(enters[1] > screen.find("line ok").unwrap());
}

fn an_unhandled_fail_restores_the_terminal(js: bool) {
    let Some(mut s) = start(
        "fail.sw",
        "import Std (IO, Fail)\n\n\
         def main(): {IO, Fail} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           Fail.fail \"boom\"\n",
        false,
        js,
    ) else {
        return;
    };
    s.wait_for_keys_mode(true);
    s.type_keys(b"x");
    let (code, errors) = s.wait();
    assert_eq!(code, 1, "{errors}");
    assert!(errors.contains("error: boom"), "{errors}");
    s.assert_restored();
    s.wait_for_screen(LEAVE_SCREEN);
}

/// `IO.write` (which, unlike `print`, doesn't leave keys mode) to a pipe
/// with no reader, while standard input is in keys mode.
fn an_io_error_restores_the_terminal(js: bool) {
    let Some(mut s) = start(
        "eio.sw",
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.write \"no one reads this\"\n",
        true,
        js,
    ) else {
        return;
    };
    s.wait_for_keys_mode(true);
    drop(s.leader.stdout.take());
    s.type_keys(b"x");
    let (code, errors) = s.wait();
    assert_eq!(code, 2, "{errors}");
    assert!(errors.contains("E-IO"), "{errors}");
    s.assert_restored();
}

fn ctrl_c_stops_the_program_and_restores_the_terminal(js: bool) {
    let Some(mut s) = start(
        "interrupt.sw",
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.print \"not reached\"\n",
        false,
        js,
    ) else {
        return;
    };
    s.wait_for_keys_mode(true);
    // Ctrl-C: `ISIG` is on, so the terminal sends `SIGINT` rather than the
    // byte.
    s.type_keys(b"\x03");
    let (code, errors) = s.wait();
    // Ended by `SIGINT` (2), as the shell reports it.
    assert_eq!(code, 130, "{errors}");
    s.assert_restored();
    s.wait_for_screen(LEAVE_SCREEN);
    assert!(!s.screen().contains("not reached"));
}

/// `examples/accept/terminal-walk.sw` through `Terminal.toIO` on a real
/// terminal: each key arrives on its own, with no Enter, an arrow's escape
/// sequence is one key, and each key draws one frame on the alternate
/// screen.
fn the_walking_example_reads_one_key_at_a_time(js: bool) {
    let Some(mut s) = start(
        "terminal-walk.sw",
        include_str!("../../../examples/accept/terminal-walk.sw"),
        false,
        js,
    ) else {
        return;
    };
    let frames = |s: &Session| s.screen().matches("\x1b[H").count();
    s.wait_for_keys_mode(true);
    s.wait_for_screen("#\x1b[33m@");
    assert_eq!(frames(&s), 1);
    s.type_keys(b"l");
    s.wait_for_screen("#.\x1b[33m@");
    assert_eq!(frames(&s), 2);
    // Down, as a terminal sends it: one key.
    s.type_keys(b"\x1b[B");
    s.wait_for_screen("#..........#\x1b[K\r\n#.\x1b[33m@");
    assert_eq!(frames(&s), 3);
    s.type_keys(b"q");
    let (code, errors) = s.wait();
    assert_eq!(code, 0, "{errors}");
    s.assert_restored();
    s.wait_for_screen("The @ stopped at column 1, row 1.");
    let screen = s.screen();
    // The last line comes after leaving the alternate screen.
    assert!(screen.rfind(LEAVE_SCREEN).unwrap() < screen.find("The @ stopped").unwrap());
}

#[test]
fn keys_mode_then_print_then_normal_exit_native() {
    keys_mode_then_print_then_normal_exit(false);
}

#[test]
fn keys_mode_then_print_then_normal_exit_js() {
    keys_mode_then_print_then_normal_exit(true);
}

#[test]
fn an_unhandled_fail_restores_the_terminal_native() {
    an_unhandled_fail_restores_the_terminal(false);
}

#[test]
fn an_unhandled_fail_restores_the_terminal_js() {
    an_unhandled_fail_restores_the_terminal(true);
}

#[test]
fn an_io_error_restores_the_terminal_native() {
    an_io_error_restores_the_terminal(false);
}

#[test]
fn an_io_error_restores_the_terminal_js() {
    an_io_error_restores_the_terminal(true);
}

#[test]
fn ctrl_c_stops_the_program_and_restores_the_terminal_native() {
    ctrl_c_stops_the_program_and_restores_the_terminal(false);
}

#[test]
fn ctrl_c_stops_the_program_and_restores_the_terminal_js() {
    ctrl_c_stops_the_program_and_restores_the_terminal(true);
}

#[test]
fn the_walking_example_reads_one_key_at_a_time_native() {
    the_walking_example_reads_one_key_at_a_time(false);
}

#[test]
fn the_walking_example_reads_one_key_at_a_time_js() {
    the_walking_example_reads_one_key_at_a_time(true);
}
