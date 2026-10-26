//! A command in a pseudo-terminal, for the tests of keys mode
//! (`keys_mode.rs`: `stitchwort run`; `build.rs`: a built executable).
//!
//! Each test starts the command with a pseudo-terminal's other end as its
//! standard input (and output) and controlling terminal, and reads the
//! settings from this end while it runs and after it ends. A shell is the
//! session's leader and runs the command: on macOS the terminal is taken
//! away from every open descriptor when the session's leader ends
//! (`tcgetattr` then fails with `ENOTTY`), so the leader stays until the
//! settings have been read.

#![allow(dead_code)]

use std::ffi::OsStr;
use std::io::{Read, Write};
use std::os::fd::{AsFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use nix::pty::{Winsize, openpty};
use nix::sys::termios::{InputFlags, LocalFlags, OutputFlags, Termios, tcgetattr};

/// How long any one wait may take before the test gives up.
pub const PATIENCE: Duration = Duration::from_secs(20);

pub const ENTER_SCREEN: &str = "\x1b[?1049h\x1b[?25l\x1b[?7l";
pub const LEAVE_SCREEN: &str = "\x1b[?7h\x1b[?25h\x1b[?1049l";

/// The shell that leads the session: it runs its arguments as the command,
/// reports its exit status on standard error, and waits to be killed.
/// `trap : INT` keeps the shell alive through Ctrl-C; the command still gets
/// `SIGINT` with its default action, since a trap's handler isn't inherited.
const SHELL: &str = r#"trap : INT; "$@"; echo "exit $?" >&2; exec sleep 60"#;

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

/// A pseudo-terminal of 100 by 30, and a command running inside it.
pub struct Session {
    /// The terminal's end, kept open to read its settings.
    pub terminal: OwnedFd,
    /// The end this test types at.
    pub master: std::fs::File,
    /// What the program wrote to the terminal.
    pub screen: Arc<Mutex<Vec<u8>>>,
    /// What the program wrote to standard error, then the shell's
    /// `exit N` line.
    pub errors: Arc<Mutex<Vec<u8>>>,
    /// The shell.
    pub leader: Child,
    /// The settings before the program started.
    pub before: Termios,
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.leader.kill();
        let _ = self.leader.wait();
    }
}

impl Session {
    /// Starts `command` (the program, then its arguments). With
    /// `piped_output`, standard output is a pipe instead of the terminal.
    /// `None`, with a note, where there are no pseudo-terminals to be had (a
    /// build sandbox).
    pub fn start(command: &[&OsStr], piped_output: bool) -> Option<Session> {
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
        let mut shell = Command::new("/bin/sh");
        shell
            .args(["-c", SHELL, "sh"])
            .args(command)
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
            shell.pre_exec(|| {
                rustix::process::setsid()?;
                rustix::process::ioctl_tiocsctty(std::io::stdin())?;
                Ok(())
            });
        }
        let mut leader = shell.spawn().expect("start the shell");
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

    pub fn settings(&self) -> Termios {
        tcgetattr(self.terminal.as_fd()).expect("tcgetattr")
    }

    pub fn errors(&self) -> String {
        String::from_utf8_lossy(&self.errors.lock().unwrap()).into_owned()
    }

    pub fn screen(&self) -> String {
        String::from_utf8_lossy(&self.screen.lock().unwrap()).into_owned()
    }

    /// Waits until the terminal is in keys mode (`true`) or not.
    pub fn wait_for_keys_mode(&self, on: bool) {
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
    pub fn type_keys(&mut self, bytes: &[u8]) {
        self.master.write_all(bytes).expect("type");
    }

    /// Waits for the program to end: its exit status, as the shell reports
    /// it (128 plus the signal's number for one ended by a signal), and what
    /// it wrote to standard error.
    pub fn wait(&self) -> (i32, String) {
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
    pub fn wait_for_screen(&self, text: &str) {
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
    pub fn assert_restored(&self) {
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
        assert_eq!(
            after.control_chars[..KERNEL_CONTROL_CHARS],
            self.before.control_chars[..KERNEL_CONTROL_CHARS]
        );
    }
}

/// How many control characters the kernel keeps. Linux keeps 19 (its
/// `NCCS`), fewer than the C library's array holds; musl's `tcgetattr`
/// leaves the rest as it found them.
const KERNEL_CONTROL_CHARS: usize = if cfg!(target_os = "linux") {
    19
} else {
    nix::libc::NCCS
};

pub fn is_keys_mode(t: &Termios) -> bool {
    !t.local_flags.contains(LocalFlags::ICANON)
}

/// Keys mode's settings (§4.3): no line editing, echo, `IEXTEN`, `IXON` or
/// `ICRNL`, `ONLCR`; `ISIG` kept.
pub fn assert_keys_mode_settings(t: &Termios) {
    assert!(!t.local_flags.contains(LocalFlags::ICANON));
    assert!(!t.local_flags.contains(LocalFlags::ECHO));
    assert!(!t.local_flags.contains(LocalFlags::IEXTEN));
    assert!(t.local_flags.contains(LocalFlags::ISIG), "ISIG is kept");
    assert!(!t.input_flags.contains(InputFlags::IXON));
    assert!(!t.input_flags.contains(InputFlags::ICRNL));
    assert!(!t.output_flags.contains(OutputFlags::ONLCR));
}
