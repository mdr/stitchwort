//! `stitchwort build`: standalone executables (stages S3 and S5 of
//! docs/proposals/standalone-executables.md). A built executable must do
//! exactly what `stitchwort run` does: the same output, errors and exit
//! statuses, and the terminal put back however it ends.
//!
//! The executables link the runtime library the test build made
//! (`libstitchwort_standalone.a`, built because this package depends on
//! `stitchwort-standalone` for its tests), found beside the test binary;
//! `STITCHWORT_RUNTIME` overrides that. Each test needs a C compiler to link
//! with (`$CC`, or `cc`), and is skipped with a note without one.
//!
//! The roguelike's tests (with and without `--native`) each check the whole
//! game twice (about 2 s), so they're left out of the lane tier
//! (`.config/nextest.toml`); the rest are quick.
//! The `--native` tests need a `stitchwort` with the `native` feature, which
//! the test tiers build.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

#[cfg(unix)]
mod pty;

/// The runtime library to link with: `STITCHWORT_RUNTIME`, or the newest
/// `libstitchwort_standalone*.a` beside this test binary (in `deps/`).
fn runtime_library() -> PathBuf {
    if let Some(path) = std::env::var_os("STITCHWORT_RUNTIME") {
        return path.into();
    }
    let exe = std::env::current_exe().expect("the test binary's path");
    let dir = exe.parent().expect("the test binary's folder");
    std::fs::read_dir(dir)
        .expect("read the test binary's folder")
        .filter_map(Result::ok)
        .filter(|entry| {
            let name = entry.file_name();
            let name = name.to_string_lossy();
            name.starts_with("libstitchwort_standalone") && name.ends_with(".a")
        })
        .max_by_key(|entry| entry.metadata().and_then(|m| m.modified()).ok())
        .map(|entry| entry.path())
        .unwrap_or_else(|| {
            panic!(
                "no libstitchwort_standalone*.a in {}: the dev-dependency on \
                 stitchwort-standalone should have built it",
                dir.display()
            )
        })
}

/// Whether there's a C compiler to link with; if not, says the test is
/// skipped.
fn have_cc() -> bool {
    let cc = std::env::var_os("CC")
        .filter(|cc| !cc.is_empty())
        .unwrap_or_else(|| "cc".into());
    let found = Command::new(&cc)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok();
    if !found {
        eprintln!("skipped: no C compiler (`{}`)", cc.to_string_lossy());
    }
    found
}

/// A fresh folder for one test.
fn work_dir(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("build-tests")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    dir
}

/// `stitchwort ARGS` in `dir`, linking with the test build's library.
fn stitchwort(dir: &Path, args: &[&str], input: &[u8]) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command
        .args(args)
        .current_dir(dir)
        .env("STITCHWORT_RUNTIME", runtime_library());
    run_with_input(command, input)
}

fn run_with_input(mut command: Command, input: &[u8]) -> Output {
    use std::io::Write;
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the command");
    // A program may end before reading it all.
    let _ = child.stdin.take().expect("stdin").write_all(input);
    child.wait_with_output().expect("wait for the command")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// Builds `args` (a target and options) in `dir`, which must succeed.
fn build(dir: &Path, args: &[&str]) {
    let mut all = vec!["build"];
    all.extend_from_slice(args);
    let output = stitchwort(dir, &all, b"");
    assert!(
        output.status.success(),
        "build failed: {}",
        text(&output.stderr)
    );
    // The linker said nothing: no warnings.
    assert_eq!(text(&output.stderr), "");
}

/// The executable `exe` on `input`.
fn run_executable(exe: &Path, input: &[u8]) -> Output {
    run_with_input(Command::new(exe), input)
}

/// Writes `source` as `name` in `dir`, builds it, and checks that the
/// executable's output, errors and exit status on each of `inputs` are
/// `stitchwort run`'s. Returns the executable and what it did on the first
/// input.
fn same_as_run(dir: &Path, name: &str, source: &str, inputs: &[&[u8]]) -> (PathBuf, Output) {
    std::fs::write(dir.join(name), source).expect("write the source");
    build(dir, &[name, "--no-cache", "-o", "program"]);
    let exe = dir.join("program");
    let mut first = None;
    for input in inputs {
        let ran = stitchwort(dir, &["run", "--no-cache", name], input);
        let built = run_executable(&exe, input);
        assert_eq!(text(&built.stdout), text(&ran.stdout), "standard output");
        assert_eq!(text(&built.stderr), text(&ran.stderr), "standard error");
        assert_eq!(built.status.code(), ran.status.code(), "exit status");
        first.get_or_insert(built);
    }
    (exe, first.expect("at least one input"))
}

/// Reads lines until the end, then all that's left is nothing: `readLine`,
/// `readAll` and `print`, as `run` does them.
const ECHO: &str = r#"import Std (IO, Nat, Text)

def echoLine: Option Text → (() → {IO, Partial | e} ()) → {IO, Partial | e} ()
  | None, more =>
    let rest := IO.readAll()
    IO.print "done, ${Nat.toText (Text.length rest)} left"
  | Some l, more =>
    IO.print "got ${l}"
    more()

def echo(): {IO, Partial} () := echoLine (IO.readLine()) echo

def main(): {IO, Partial} () := echo()
"#;

#[test]
fn an_io_program_runs_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("io");
    let (_, first) = same_as_run(
        &dir,
        "echo.sw",
        ECHO,
        &[b"one\ntwo\r\nthree", b"", b"bad \xff\n"],
    );
    assert_eq!(
        text(&first.stdout),
        "got one\ngot two\ngot three\ndone, 0 left\n"
    );
    assert_eq!(first.status.code(), Some(0));
}

/// The executable is named after the file by default, and signed on macOS,
/// where an unsigned one would be killed (§7.2).
#[test]
fn the_executable_is_named_after_its_file_and_signed() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("named");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    build(&dir, &["echo.sw", "--no-cache"]);
    let exe = dir.join("echo");
    assert_eq!(
        text(&run_executable(&exe, b"x\n").stdout),
        "got x\ndone, 0 left\n"
    );
    if cfg!(target_os = "macos") {
        match Command::new("codesign").arg("-v").arg(&exe).output() {
            Ok(verified) => assert!(verified.status.success(), "{}", text(&verified.stderr)),
            // A build sandbox without Apple's tools.
            Err(e) => eprintln!("skipped the signature check: no codesign ({e})"),
        }
    }
}

/// An unhandled `Fail`: what was printed, then `error: <msg>`, and status 1.
#[test]
fn a_failing_program_fails_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("fail");
    let (_, first) = same_as_run(
        &dir,
        "fail.sw",
        include_str!("../../../examples/accept/main-fail.sw"),
        &[b""],
    );
    assert_eq!(first.status.code(), Some(1));
    assert_eq!(text(&first.stdout), "reading the numbers\n");
    assert!(
        text(&first.stderr).starts_with("error: "),
        "{}",
        text(&first.stderr)
    );
}

/// Recursion past the frame limit: `E-RESOURCE`, as `run` reports it but for
/// the excerpt of `main`'s source, which the executable doesn't have, and
/// status 2.
#[test]
fn a_program_out_of_frames_reports_as_run_does() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("frames");
    let source = "import Std (Nat)\n\n\
                  def count : Nat -> Nat\n  \
                    | 0      => 0\n  \
                    | Succ n => 1 + count n\n\n\
                  def main () : {IO} () :=\n  \
                    IO.print \"before\"\n  \
                    IO.print (Nat.toText (count (5 * 1000 * 1000)))\n";
    std::fs::write(dir.join("runaway.sw"), source).expect("write the source");
    build(&dir, &["runaway.sw", "--no-cache"]);
    let built = run_executable(&dir.join("runaway"), b"");
    let ran = stitchwort(&dir, &["run", "--no-cache", "runaway.sw"], b"");
    assert_eq!(built.status.code(), Some(2));
    assert_eq!(ran.status.code(), Some(2));
    assert_eq!(text(&built.stdout), "before\n");
    assert_eq!(text(&built.stdout), text(&ran.stdout));
    let stderr = text(&built.stderr);
    let mut lines = stderr.lines();
    let first = lines.next().unwrap_or_default();
    assert!(
        first.starts_with("[E-RESOURCE] Error: ran out of resources: "),
        "{stderr}"
    );
    // The same message and notes as `run`'s report.
    let message = first.trim_start_matches("[E-RESOURCE] Error: ");
    let ran_stderr = text(&ran.stderr);
    assert!(ran_stderr.contains(message), "{ran_stderr}");
    let notes: Vec<&str> = lines.collect();
    assert!(
        notes.iter().any(
            |note| note.starts_with("  note: the recursion was deepest in")
                && note.contains("count")
        ),
        "{stderr}"
    );
    for note in notes {
        let note = note.trim_start_matches("  note: ");
        assert!(ran_stderr.contains(note), "{note:?} isn't in {ran_stderr}");
    }
}

/// `build` says what's wrong when it can't link: no library, no C compiler,
/// or a linker that fails, with what the linker said.
#[test]
fn link_failures_are_explained() {
    let dir = work_dir("link-errors");
    std::fs::write(dir.join("echo.sw"), ECHO).expect("write the source");
    let build_with = |variable: &str, value: &OsStr| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
        command
            .args(["build", "echo.sw", "--no-cache"])
            .current_dir(&dir)
            .env("STITCHWORT_RUNTIME", runtime_library())
            .env(variable, value);
        run_with_input(command, b"")
    };

    let missing = build_with(
        "STITCHWORT_RUNTIME",
        OsStr::new("/no/such/libstitchwort_standalone.a"),
    );
    assert_eq!(missing.status.code(), Some(1));
    assert_eq!(
        text(&missing.stderr),
        "error: there's no runtime library at /no/such/libstitchwort_standalone.a, which \
         STITCHWORT_RUNTIME names\n"
    );

    let no_cc = build_with("CC", OsStr::new("/no/such/cc"));
    assert_eq!(no_cc.status.code(), Some(1));
    let stderr = text(&no_cc.stderr);
    assert!(
        stderr.starts_with(
            "error: can't find a C compiler to link with: there's no `/no/such/cc` on the PATH\n"
        ),
        "{stderr}"
    );
    assert!(
        stderr.contains("  note: `build` links the executable"),
        "{stderr}"
    );

    if !have_cc() {
        return;
    }
    let bogus = dir.join("libbogus.a");
    std::fs::write(&bogus, "not an archive").expect("write the bogus library");
    let failed = build_with("STITCHWORT_RUNTIME", bogus.as_os_str());
    assert_eq!(failed.status.code(), Some(1));
    let stderr = text(&failed.stderr);
    // `$CC`, or `cc`.
    assert!(
        stderr.starts_with("error: linking failed: `") && stderr.contains("` ended with "),
        "{stderr}"
    );
    // Then what the linker said, which names the file it couldn't use.
    assert!(
        stderr.lines().count() > 1 && stderr.contains("libbogus.a"),
        "{stderr}"
    );
    assert!(!dir.join("echo").exists());
}

/// A project folder builds its one namespace with a `main`; one with none
/// says how to name the function instead.
#[test]
fn a_project_folder_builds_its_main() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("project");
    let project = dir.join("greeter");
    std::fs::create_dir_all(project.join("src/Greet")).expect("make the project");
    std::fs::write(project.join("stitchwort.yaml"), "sources: [src]\n").expect("write");
    std::fs::write(
        project.join("src/Greet/Greet.sw"),
        "namespace Greet\nimport Std (IO)\n\ndef main(): {IO} () := IO.print \"hello\"\n",
    )
    .expect("write");
    std::fs::write(
        project.join("src/Greet/Words.sw"),
        "namespace Greet.Words\n\ndef word: Text := \"hi\"\n",
    )
    .expect("write");
    // Named after the folder by default, which is here already.
    let clash = stitchwort(&dir, &["build", "greeter"], b"");
    assert_eq!(clash.status.code(), Some(1));
    assert_eq!(
        text(&clash.stderr),
        "error: can't write the executable to greeter: it's a folder\n  note: name the \
         executable with -o\n"
    );
    build(&dir, &["greeter", "-o", "greeter-app"]);
    assert_eq!(
        text(&run_executable(&dir.join("greeter-app"), b"").stdout),
        "hello\n"
    );
    // A function of the project, by its full name: named after its
    // namespace.
    build(&project, &["Greet.main"]);
    assert_eq!(
        text(&run_executable(&project.join("greet"), b"").stdout),
        "hello\n"
    );

    std::fs::remove_file(project.join("src/Greet/Greet.sw")).expect("remove main");
    let output = stitchwort(&dir, &["build", "greeter"], b"");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        text(&output.stderr),
        "error: no namespace of project greeter/ declares `main`\n  note: name the function \
         to build, as in `stitchwort build Name.main --project greeter`\n"
    );
}

/// A copy of the roguelike in `dir`, seeded with a constant instead of
/// `IO.randomSeed`, so that every run plays the same game.
fn seeded_rogue(dir: &Path) -> PathBuf {
    fn copy_tree(from: &Path, to: &Path) {
        std::fs::create_dir_all(to).expect("make a folder");
        for entry in std::fs::read_dir(from).expect("read a folder") {
            let entry = entry.expect("an entry");
            let target = to.join(entry.file_name());
            if entry.file_type().expect("its type").is_dir() {
                copy_tree(&entry.path(), &target);
            } else {
                std::fs::copy(entry.path(), &target).expect("copy a file");
            }
        }
    }
    let rogue = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../games/rogue");
    let copy = dir.join("rogue");
    copy_tree(&rogue.join("src"), &copy.join("src"));
    std::fs::copy(rogue.join("stitchwort.yaml"), copy.join("stitchwort.yaml")).expect("copy");
    let main = copy.join("src/Rogue/Rogue.sw");
    let source = std::fs::read_to_string(&main).expect("read Rogue.sw");
    let seeded = source.replace("IO.randomSeed() % 2147483648", "12345");
    assert_ne!(
        seeded, source,
        "Rogue.main no longer seeds itself as this test expects"
    );
    std::fs::write(&main, seeded).expect("write Rogue.sw");
    copy
}

/// Milestone M1: the roguelike, built from its folder, plays as `stitchwort
/// run Rogue.main` does on the same keys; and in a terminal, `q` quits it
/// with the terminal put back.
#[test]
fn the_roguelike_plays_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("rogue");
    let project = seeded_rogue(&dir);
    build(&dir, &["rogue", "-o", "rogue-game"]);
    let exe = dir.join("rogue-game");
    let built = run_executable(&exe, b"jjlq");
    let ran = stitchwort(&project, &["run", "Rogue.main"], b"jjlq");
    assert_eq!(built.status.code(), Some(0), "{}", text(&built.stderr));
    assert_eq!(ran.status.code(), Some(0), "{}", text(&ran.stderr));
    assert_eq!(text(&built.stderr), "");
    assert!(!built.stdout.is_empty());
    assert_eq!(text(&built.stdout), text(&ran.stdout));

    #[cfg(unix)]
    {
        let Some(mut s) = pty::Session::start(&[exe.as_os_str()], false) else {
            return;
        };
        s.wait_for_keys_mode(true);
        pty::assert_keys_mode_settings(&s.settings());
        s.wait_for_screen("\x1b[33m@");
        s.type_keys(b"jjl");
        s.type_keys(b"q");
        let (code, errors) = s.wait();
        assert_eq!(code, 0, "{errors}");
        s.assert_restored();
        let screen = s.screen();
        let left = screen
            .rfind(pty::LEAVE_SCREEN)
            .expect("left the alternate screen");
        // The ending is printed on the normal screen.
        assert!(left < screen.len() - pty::LEAVE_SCREEN.len(), "{screen:?}");
    }
}

/// In a terminal: `q` ends the walking example, and Ctrl-C a program waiting
/// for a key, and either way the terminal's settings are put back (the
/// runtime library's restore guard and signal thread, as for `run`).
#[cfg(unix)]
#[test]
fn the_terminal_is_put_back_after_q_and_after_ctrl_c() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("terminal");
    std::fs::write(
        dir.join("walk.sw"),
        include_str!("../../../examples/accept/terminal-walk.sw"),
    )
    .expect("write the source");
    build(&dir, &["walk.sw", "--no-cache"]);
    let walk = dir.join("walk");
    let Some(mut s) = pty::Session::start(&[walk.as_os_str()], false) else {
        return;
    };
    s.wait_for_keys_mode(true);
    pty::assert_keys_mode_settings(&s.settings());
    s.wait_for_screen("#\x1b[33m@");
    s.type_keys(b"l");
    s.wait_for_screen("#.\x1b[33m@");
    s.type_keys(b"q");
    let (code, errors) = s.wait();
    assert_eq!(code, 0, "{errors}");
    s.assert_restored();
    s.wait_for_screen("The @ stopped at column 1, row 0.");
    drop(s);

    std::fs::write(
        dir.join("interrupt.sw"),
        "import Std (IO)\n\n\
         def main(): {IO} () :=\n  \
           IO.keysMode True\n  \
           let _ := IO.readBytes()\n  \
           IO.print \"not reached\"\n",
    )
    .expect("write the source");
    build(&dir, &["interrupt.sw", "--no-cache"]);
    let interrupt = dir.join("interrupt");
    let Some(mut s) = pty::Session::start(&[interrupt.as_os_str()], false) else {
        return;
    };
    s.wait_for_keys_mode(true);
    // Ctrl-C: `ISIG` is on, so the terminal sends `SIGINT`.
    s.type_keys(b"\x03");
    let (code, errors) = s.wait();
    // Ended by `SIGINT` (2), as the shell reports it.
    assert_eq!(code, 130, "{errors}");
    s.assert_restored();
    s.wait_for_screen(pty::LEAVE_SCREEN);
    assert!(!s.screen().contains("not reached"));
}

// ------------------------------------------------------- build --native
//
// Stage S5: the bodies `main` reaches compiled into the executable, where
// they compile (every one but the entry, since stage N4), with the machine
// for the rest (D1287). These need a
// `stitchwort` with the `native` feature, which the test tiers build
// (`--features stitchwort-cli/native`).

/// A file of bench/native.
#[cfg(feature = "native")]
fn native_bench(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../bench/native")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The crossing's trampolines (`sw_cross_<number of arguments>`) the
/// executable `exe` defines: the native code linked into it.
#[cfg(feature = "native")]
fn native_trampolines(exe: &Path) -> Vec<String> {
    use object::{Object as _, ObjectSymbol as _};
    let bytes = std::fs::read(exe).expect("read the executable");
    let file = object::File::parse(&*bytes).expect("parse the executable");
    let mut trampolines: Vec<String> = file
        .symbols()
        .filter_map(|symbol| symbol.name().ok())
        .map(|name| name.trim_start_matches('_').to_string())
        .filter(|name| name.starts_with("sw_cross_"))
        .collect();
    trampolines.sort();
    trampolines
}

/// On macOS, `codesign -v` passes on `exe`.
#[cfg(feature = "native")]
fn assert_signed(exe: &Path) {
    if cfg!(target_os = "macos") {
        match Command::new("codesign").arg("-v").arg(exe).output() {
            Ok(verified) => assert!(verified.status.success(), "{}", text(&verified.stderr)),
            Err(e) => eprintln!("skipped the signature check: no codesign ({e})"),
        }
    }
}

/// Builds `source` as `name` in `dir` with `--native`, and checks that the
/// executable's output, errors and exit status on `input` are those of
/// `run --native` and of `run`, and that it's signed. Returns the
/// executable and what it did.
#[cfg(feature = "native")]
fn native_same_as_run(dir: &Path, name: &str, source: &str, input: &[u8]) -> (PathBuf, Output) {
    std::fs::write(dir.join(name), source).expect("write the source");
    build(dir, &[name, "--native", "--no-cache", "-o", "program"]);
    let exe = dir.join("program");
    let built = run_executable(&exe, input);
    for runner in [
        &["run", "--native", "--no-cache", name][..],
        &["run", "--no-cache", name],
    ] {
        let ran = stitchwort(dir, runner, input);
        assert_eq!(
            text(&built.stdout),
            text(&ran.stdout),
            "standard output, {runner:?}"
        );
        assert_eq!(
            text(&built.stderr),
            text(&ran.stderr),
            "standard error, {runner:?}"
        );
        assert_eq!(
            built.status.code(),
            ran.status.code(),
            "exit status, {runner:?}"
        );
    }
    assert_signed(&exe);
    (exe, built)
}

/// A native benchmark at its small size, `name` in bench/native: the same
/// as `run --native` and `run`, printing `expected`, with native code
/// linked in. One test each, so they run in parallel.
#[cfg(feature = "native")]
fn native_benchmark(name: &str, expected: &str) {
    if !have_cc() {
        return;
    }
    let dir = work_dir(&format!("native-{name}"));
    let (exe, built) = native_same_as_run(&dir, name, &native_bench(name), b"");
    assert_eq!(text(&built.stdout), expected, "{name}");
    assert_eq!(built.status.code(), Some(0), "{name}");
    assert!(
        !native_trampolines(&exe).is_empty(),
        "{name} has no native code"
    );
}

#[cfg(feature = "native")]
#[test]
fn native_micro_call_runs_as_it_does_under_run() {
    native_benchmark("micro_call.sw", "20000\n");
}

#[cfg(feature = "native")]
#[test]
fn native_micro_tail_runs_as_it_does_under_run() {
    native_benchmark("micro_tail.sw", "499500\n");
}

#[cfg(feature = "native")]
#[test]
fn native_set_nat_runs_as_it_does_under_run() {
    native_benchmark("set_nat.sw", "1000\n");
}

#[cfg(feature = "native")]
#[test]
fn native_closures_run_as_they_do_under_run() {
    native_benchmark("closures.sw", "36673290\n");
}

/// `--verbose` says how many bodies were compiled (every one `main`
/// reaches but its entry, effects included since stage N4), and, where
/// nothing compiles, why the run stays on the machine; the executable then
/// has no native code, and still runs.
#[cfg(feature = "native")]
#[test]
fn verbose_says_what_was_compiled() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-verbose");
    let build_verbose = |name: &str, source: &str| {
        std::fs::write(dir.join(name), source).expect("write");
        let output = stitchwort(
            &dir,
            &["build", name, "--native", "--verbose", "--no-cache"],
            b"",
        );
        assert!(output.status.success(), "{}", text(&output.stderr));
        text(&output.stderr)
    };
    let said = build_verbose("micro_call.sw", &native_bench("micro_call.sw"));
    assert!(
        said.starts_with("native: compiled 3 of the 3 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert_eq!(said.lines().count(), 1, "{said}");
    assert!(!native_trampolines(&dir.join("micro_call")).is_empty());

    // A function that performs effects.
    let said = build_verbose(
        "countdown.sw",
        "import Std (IO, Nat)\n\n\
         def countdown: Nat -> {IO} ()\n  \
           | 0 => IO.print \"go\"\n  \
           | Succ n =>\n    \
             IO.print (Nat.toText (Succ n))\n    \
             countdown n\n\n\
         def main(): {IO} () := countdown 2\n",
    );
    assert!(
        said.starts_with("native: compiled 3 of the 3 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert!(!native_trampolines(&dir.join("countdown")).is_empty());
    assert_eq!(
        text(&run_executable(&dir.join("countdown"), b"").stdout),
        "2\n1\ngo\n"
    );

    // Nothing but the entry, which is compiled too (stage NO4 of
    // native-only.md).
    let said = build_verbose(
        "hello.sw",
        "import Std (IO)\n\ndef main(): {IO} () := IO.print \"hello\"\n",
    );
    assert!(
        said.starts_with("native: compiled 1 of the 1 bodies `main` reaches (frames of at most "),
        "{said}"
    );
    assert!(!native_trampolines(&dir.join("hello")).is_empty());
    assert_eq!(
        text(&run_executable(&dir.join("hello"), b"").stdout),
        "hello\n"
    );
}

/// An unhandled `Fail`: as under `run`, built with `--native`.
#[cfg(feature = "native")]
#[test]
fn a_failing_program_built_native_fails_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-fail");
    let (_, failed) = native_same_as_run(
        &dir,
        "fail.sw",
        include_str!("../../../examples/accept/main-fail.sw"),
        b"",
    );
    assert_eq!(failed.status.code(), Some(1));
    assert!(text(&failed.stderr).starts_with("error: "));
}

/// Recursion past the frame limit in native code: as under `run` (the
/// out-of-frames report without the excerpt of `main`'s source, which the
/// executable doesn't have).
#[cfg(feature = "native")]
#[test]
fn native_code_out_of_frames_reports_as_run_does() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("native-frames");
    let source = "import Std (Nat)\n\n\
                  def count : Nat -> Nat\n  \
                    | 0      => 0\n  \
                    | Succ n => 1 + count n\n\n\
                  def main () : {IO} () :=\n  \
                    IO.print (Nat.toText (count (5 * 1000 * 1000)))\n";
    std::fs::write(dir.join("runaway.sw"), source).expect("write the source");
    build(&dir, &["runaway.sw", "--native", "--no-cache"]);
    let exe = dir.join("runaway");
    assert!(!native_trampolines(&exe).is_empty(), "`count` is compiled");
    let built = run_executable(&exe, b"");
    assert_eq!(built.status.code(), Some(2));
    assert_eq!(text(&built.stdout), "");
    let stderr = text(&built.stderr);
    assert!(
        stderr.starts_with("[E-RESOURCE] Error: ran out of resources: "),
        "{stderr}"
    );
    for runner in [
        &["run", "--native", "--no-cache", "runaway.sw"][..],
        &["run", "--no-cache", "runaway.sw"],
    ] {
        let ran = stitchwort(&dir, runner, b"");
        assert_eq!(ran.status.code(), Some(2), "{runner:?}");
        assert_eq!(text(&ran.stdout), text(&built.stdout), "{runner:?}");
        // The same message and notes as `run`'s report.
        let ran_stderr = text(&ran.stderr);
        for line in stderr.lines() {
            let line = line
                .trim_start_matches("[E-RESOURCE] Error: ")
                .trim_start_matches("  note: ");
            assert!(ran_stderr.contains(line), "{line:?} isn't in {ran_stderr}");
        }
    }
}

/// Milestone M2: the roguelike built with `--native` runs every body but
/// its entry natively (stage N4), and plays as under `run`.
#[cfg(feature = "native")]
#[test]
fn the_roguelike_built_native_plays_as_it_does_under_run() {
    if !have_cc() {
        return;
    }
    let dir = work_dir("rogue-native");
    let project = seeded_rogue(&dir);
    let output = stitchwort(
        &dir,
        &[
            "build",
            "rogue",
            "--native",
            "--verbose",
            "-o",
            "rogue-game",
        ],
        b"",
    );
    assert!(output.status.success(), "{}", text(&output.stderr));
    let said = text(&output.stderr);
    let counts = said
        .strip_prefix("native: compiled ")
        .and_then(|rest| rest.split_once(" bodies `main` reaches"))
        .and_then(|(counts, _)| counts.split_once(" of the "))
        .map(|(compiled, reached)| (compiled.parse::<usize>(), reached.parse::<usize>()));
    let Some((Ok(compiled), Ok(reached))) = counts else {
        panic!("{said}");
    };
    assert_eq!(compiled, reached, "every body, the entry included: {said}");
    // No note that the executable will run everything on the machine (its
    // frame bound fits the stack): the guard `the_roguelike_runs_natively`
    // checks under `run --native` too.
    assert!(!said.contains("on the machine"), "{said}");
    assert_eq!(said.lines().count(), 1, "{said}");
    let exe = dir.join("rogue-game");
    assert_signed(&exe);
    assert!(!native_trampolines(&exe).is_empty());
    let built = run_executable(&exe, b"jjlq");
    let ran = stitchwort(&project, &["run", "Rogue.main"], b"jjlq");
    assert_eq!(built.status.code(), Some(0), "{}", text(&built.stderr));
    assert_eq!(ran.status.code(), Some(0), "{}", text(&ran.stderr));
    assert_eq!(text(&built.stderr), "");
    assert!(!built.stdout.is_empty());
    assert_eq!(text(&built.stdout), text(&ran.stdout));
}

/// A guard (stage NO3 of docs/proposals/native-only.md): the roguelike's
/// frame bound times its frame limit must fit the native stack, or the
/// whole run silently falls back to the machine and every other test still
/// passes. Under `run --native --verbose`, nothing ran on the machine and
/// native code had the machine run nothing for it (no nested run); and
/// `build --native --verbose` doesn't say the executable will fall back.
/// The frames' bound and the limit are printed, so the margin is in the
/// test's output.
#[cfg(feature = "native")]
#[test]
fn the_roguelike_runs_natively() {
    let dir = work_dir("rogue-guard");
    let project = seeded_rogue(&dir);
    let ran = stitchwort(
        &project,
        &["run", "--native", "--verbose", "Rogue.main"],
        b"jjlq",
    );
    let said = text(&ran.stderr);
    assert_eq!(ran.status.code(), Some(0), "{said}");
    assert!(!said.contains("on the machine"), "fell back: {said}");
    assert!(
        said.contains("native: the machine executed 0 instructions"),
        "{said}"
    );
    let running = said
        .lines()
        .find(|line| line.starts_with("native: running "))
        .unwrap_or_else(|| panic!("nothing ran natively: {said}"));
    let bound = running
        .split_once("(frames of at most ")
        .and_then(|(_, rest)| rest.split_once(" bytes"))
        .and_then(|(bytes, _)| bytes.parse::<usize>().ok())
        .unwrap_or_else(|| panic!("no frame bound: {running}"));
    let limit = stitchwort_rt::Limits::from_core(Default::default()).frames;
    let room = stitchwort_host::NATIVE_STACK
        - stitchwort_rt::native_abi::HOST_ROOM
        - stitchwort_rt::native_abi::HELPER_ROOM;
    println!(
        "the roguelike's frames: at most {bound} bytes, {limit} of them: {} of {room} bytes",
        bound * limit
    );
    assert!(bound * limit <= room, "{running}");

    if !have_cc() {
        return;
    }
    let output = stitchwort(
        &dir,
        &[
            "build",
            "rogue",
            "--native",
            "--verbose",
            "-o",
            "rogue-guard",
        ],
        b"",
    );
    let said = text(&output.stderr);
    assert!(output.status.success(), "{said}");
    assert!(!said.contains("on the machine"), "fell back: {said}");
}
