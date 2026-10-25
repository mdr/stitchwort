//! `stitchwort run` in a pseudo-terminal (docs/proposals/terminal-io.md
//! §4.3, §5): `IO.keysMode` changes the terminal's settings, `print` leaves
//! keys mode (D1260), and the settings are put back however the run ends:
//! normally, by an unhandled `Fail`, by `E-IO`, and by Ctrl-C (which still
//! stops the program, D1248).
//!
//! Each test starts the built command with a pseudo-terminal's other end as
//! its standard input (and output) and controlling terminal, and reads the
//! settings from this end while it runs and after it ends. A shell is the
//! session's leader and runs the command: on macOS the terminal is taken
//! away from every open descriptor when the session's leader ends
//! (`tcgetattr` then fails with `ENOTTY`), so the leader stays until the
//! settings have been read.

#![cfg(unix)]

use std::io::{Read, Write};
use std::os::fd::{AsFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use nix::pty::{Winsize, openpty};
use nix::sys::termios::{InputFlags, LocalFlags, Termios, tcgetattr};

/// How long any one wait may take before the test gives up.
const PATIENCE: Duration = Duration::from_secs(20);

const ENTER_SCREEN: &str = "\x1b[?1049h\x1b[?25l\x1b[?7l";
const LEAVE_SCREEN: &str = "\x1b[?7h\x1b[?25h\x1b[?1049l";

/// The shell that leads the session: it runs `stitchwort run --no-cache
/// FILE` (`$0` and `$1`), reports its exit status on standard error, and
/// waits to be killed. `trap : INT` keeps the shell alive through Ctrl-C;
/// the command still gets `SIGINT` with its default action, since a trap's
/// handler isn't inherited.
const SHELL: &str = r#"trap : INT; "$0" run --no-cache "$1"; echo "exit $?" >&2; exec sleep 60"#;

/// Collects what `from` produces, as it arrives.
fn collect(mut from: impl Read + Send + 'static) -> Arc<Mutex<Vec<u8>>> {
    let sink = Arc::new(Mutex::new(Vec::new()));
    let into = Arc::clone(&sink);
    std::thread::spawn(move || {
        let mut buf = [0; 4096];
        while let Ok(n) = from.read(&mut buf) {
            if n == 0 {
                break;
            }
            into.lock().unwrap().extend_from_slice(&buf[..n]);
        }
    });
    sink
}

/// A pseudo-terminal of 100 by 30, and `stitchwort run` on a program inside
/// it.
struct Session {
    /// The terminal's end, kept open to read its settings.
    terminal: OwnedFd,
    /// The end this test types at.
    master: std::fs::File,
    /// What the program wrote to the terminal.
    screen: Arc<Mutex<Vec<u8>>>,
    /// What the program wrote to standard error, then the shell's
    /// `exit N` line.
    errors: Arc<Mutex<Vec<u8>>>,
    /// The shell.
    leader: Child,
    /// The settings before the program started.
    before: Termios,
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.leader.kill();
        let _ = self.leader.wait();
    }
}

fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-keys-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

impl Session {
    /// Starts the program. With `piped_output`, standard output is a pipe
    /// instead of the terminal. `None`, with a note, where there are no
    /// pseudo-terminals to be had (a build sandbox).
    fn start(name: &str, source: &str, piped_output: bool) -> Option<Session> {
        let path = source_file(name, source);
        let size = Winsize {
            ws_row: 30,
            ws_col: 100,
            ws_xpixel: 0,
            ws_ypixel: 0,
        };
        let pty = match openpty(&size, None) {
            Ok(pty) => pty,
            Err(e) => {
                eprintln!("skipped: no pseudo-terminal ({e})");
                return None;
            }
        };
        for fd in [&pty.master, &pty.slave] {
            rustix::io::fcntl_setfd(fd, rustix::io::FdFlags::CLOEXEC).expect("close on exec");
        }
        let before = tcgetattr(&pty.slave).expect("tcgetattr");
        let stdout: Stdio = if piped_output {
            Stdio::piped()
        } else {
            pty.slave.try_clone().expect("dup").into()
        };
        let mut command = Command::new("/bin/sh");
        command
            .args(["-c", SHELL, env!("CARGO_BIN_EXE_stitchwort")])
            .arg(&path)
            .stdin(pty.slave.try_clone().expect("dup"))
            .stdout(stdout)
            .stderr(Stdio::piped());
        // A new session whose controlling terminal is this one, so that
        // Ctrl-C there sends `SIGINT` to its foreground process group.
        #[allow(unsafe_code)]
        // SAFETY: the closure runs in the child between `fork` and `exec`,
        // where only async-signal-safe calls are allowed: it makes two system
        // calls through rustix, which neither allocates nor takes locks.
        unsafe {
            command.pre_exec(|| {
                rustix::process::setsid()?;
                rustix::process::ioctl_tiocsctty(std::io::stdin())?;
                Ok(())
            });
        }
        let mut leader = command.spawn().expect("start the shell");
        let master = std::fs::File::from(pty.master);
        let screen = collect(master.try_clone().expect("dup"));
        let errors = collect(leader.stderr.take().expect("stderr"));
        Some(Session {
            terminal: pty.slave,
            master,
            screen,
            errors,
            leader,
            before,
        })
    }

    fn settings(&self) -> Termios {
        tcgetattr(self.terminal.as_fd()).expect("tcgetattr")
    }

    fn errors(&self) -> String {
        String::from_utf8_lossy(&self.errors.lock().unwrap()).into_owned()
    }

    fn screen(&self) -> String {
        String::from_utf8_lossy(&self.screen.lock().unwrap()).into_owned()
    }

    /// Waits until the terminal is in keys mode (`true`) or not.
    fn wait_for_keys_mode(&self, on: bool) {
        let start = Instant::now();
        while is_keys_mode(&self.settings()) != on {
            assert!(
                start.elapsed() < PATIENCE,
                "keys mode never became {on}: {}",
                self.errors()
            );
            std::thread::sleep(Duration::from_millis(2));
        }
    }

    /// Types `bytes` at the terminal.
    fn type_keys(&mut self, bytes: &[u8]) {
        self.master.write_all(bytes).expect("type");
    }

    /// Waits for the program to end: its exit status, as the shell reports
    /// it (128 plus the signal's number for one ended by a signal), and what
    /// it wrote to standard error.
    fn wait(&self) -> (i32, String) {
        let start = Instant::now();
        loop {
            let errors = self.errors();
            if let Some(at) = errors.rfind("exit ")
                && errors.ends_with('\n')
                && let Ok(code) = errors[at + 5..].trim().parse()
            {
                return (code, errors[..at].to_string());
            }
            assert!(
                start.elapsed() < PATIENCE,
                "the program didn't end: {errors}"
            );
            std::thread::sleep(Duration::from_millis(2));
        }
    }

    /// Waits until the terminal has shown `text`.
    fn wait_for_screen(&self, text: &str) {
        let start = Instant::now();
        while !self.screen().contains(text) {
            assert!(
                start.elapsed() < PATIENCE,
                "never saw {text:?} in {:?}",
                self.screen()
            );
            std::thread::sleep(Duration::from_millis(2));
        }
    }

    /// Checks the settings are as they were before the program started.
    fn assert_restored(&self) {
        let after = self.settings();
        // `PENDIN` is the kernel's own state, not a setting: BSD kernels
        // (macOS) set it when `ICANON` is switched back on, to retype any
        // pending input.
        assert_eq!(
            after.local_flags - LocalFlags::PENDIN,
            self.before.local_flags - LocalFlags::PENDIN
        );
        assert_eq!(after.input_flags, self.before.input_flags);
        assert_eq!(after.output_flags, self.before.output_flags);
        assert_eq!(after.control_chars, self.before.control_chars);
    }
}

fn is_keys_mode(t: &Termios) -> bool {
    !t.local_flags.contains(LocalFlags::ICANON)
}

/// Keys mode's settings (§4.3): no line editing, echo, `IEXTEN`, `IXON` or
/// `ICRNL`; `ISIG` kept.
fn assert_keys_mode_settings(t: &Termios) {
    assert!(!t.local_flags.contains(LocalFlags::ICANON));
    assert!(!t.local_flags.contains(LocalFlags::ECHO));
    assert!(!t.local_flags.contains(LocalFlags::IEXTEN));
    assert!(t.local_flags.contains(LocalFlags::ISIG), "ISIG is kept");
    assert!(!t.input_flags.contains(InputFlags::IXON));
    assert!(!t.input_flags.contains(InputFlags::ICRNL));
}

#[test]
fn keys_mode_then_print_then_normal_exit() {
    let Some(mut s) = Session::start(
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

#[test]
fn an_unhandled_fail_restores_the_terminal() {
    let Some(mut s) = Session::start(
        "fail.sw",
        "import Std (IO, Fail)\n\n\
         def main(): {IO, Fail} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           Fail.fail \"boom\"\n",
        false,
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
#[test]
fn an_io_error_restores_the_terminal() {
    let Some(mut s) = Session::start(
        "eio.sw",
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.write \"no one reads this\"\n",
        true,
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

#[test]
fn ctrl_c_stops_the_program_and_restores_the_terminal() {
    let Some(mut s) = Session::start(
        "interrupt.sw",
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.print \"not reached\"\n",
        false,
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
