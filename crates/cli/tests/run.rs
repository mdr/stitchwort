//! `stitchwort run`, end to end: the built command, with real standard input
//! and output (docs/proposals/text-and-io.md, "`main` and `stitchwort run`").
//! The runner's contract is tested in detail, in memory, in
//! `crates/driver/tests/run.rs`.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::Mutex;
use std::time::Duration;

use stitchwort_cli::driver::Session;

/// Held while creating pipes and spawning children. On macOS, std makes a
/// pipe with `pipe` and then sets close-on-exec on each end in a second step
/// (no `pipe2`; std/src/sys/pipe/unix.rs), so a child spawned by another test
/// thread in between inherits the pipe's ends. That broke
/// `a_write_error_is_an_error`, which needs a pipe with no reader: a child
/// that inherited the read end kept it open, and the write succeeded.
static SPAWN: Mutex<()> = Mutex::new(());

/// Spawns `command` while holding [`SPAWN`].
fn spawn(command: &mut Command) -> Child {
    let _guard = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
    command.spawn().expect("start stitchwort")
}

/// Writes `source` to a temporary file called `name`.
fn source_file(name: &str, source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-run-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(name);
    std::fs::write(&path, source).expect("write source");
    path
}

fn example(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples/accept")
        .join(name)
}

/// Runs `stitchwort run path` with `input` piped to it.
fn run(path: &Path, input: &[u8]) -> Output {
    run_in(Path::new("."), path.as_os_str(), input)
}

/// Runs `stitchwort run target` in `cwd` with `input` piped to it: a file,
/// or a function of the project `cwd` is in, by its full name.
fn run_in(cwd: &Path, target: &std::ffi::OsStr, input: &[u8]) -> Output {
    let mut child = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .arg(target)
            .current_dir(cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped()),
    );
    let mut stdin = child.stdin.take().unwrap();
    let input = input.to_vec();
    // A program that stops early doesn't read it all, so writing may fail.
    let writer = std::thread::spawn(move || {
        let _ = stdin.write_all(&input);
    });
    let output = child.wait_with_output().expect("run stitchwort");
    writer.join().unwrap();
    output
}

fn stdout(output: &Output) -> &str {
    std::str::from_utf8(&output.stdout).expect("output is UTF-8")
}

fn stderr(output: &Output) -> &str {
    std::str::from_utf8(&output.stderr).expect("errors are UTF-8")
}

/// Runs `path` with `input`, which must succeed: what it printed.
fn succeeds(path: &Path, input: &[u8]) -> String {
    let output = run(path, input);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stderr(&output), "");
    stdout(&output).to_string()
}

/// Runs `path` with `input`, which must fail with exit code `status` and
/// report `code`: what it printed before failing.
fn fails_with(path: &Path, input: &[u8], code: &str, status: i32) -> String {
    let output = run(path, input);
    assert_eq!(output.status.code(), Some(status), "{}", stderr(&output));
    assert!(
        stderr(&output).contains(&format!("[{code}]")),
        "expected {code}:\n{}",
        stderr(&output)
    );
    stdout(&output).to_string()
}

/// Runs `path` with `input`, which must fail while checking (exit code 1)
/// and report `code`: what it printed before failing.
fn fails(path: &Path, input: &[u8], code: &str) -> String {
    fails_with(path, input, code, 1)
}

/// Runs `path` with `input`, which must fail while running (exit code 2)
/// and report `code`: what it printed before failing.
fn fails_running(path: &Path, input: &[u8], code: &str) -> String {
    fails_with(path, input, code, 2)
}

#[test]
fn the_example_prints_what_simulate_records() {
    let path = example("adder.sw");
    let mut session = Session::new();
    session
        .load("adder.sw", &std::fs::read_to_string(&path).unwrap())
        .expect("the example checks");
    for lines in [
        &[][..],
        &["Ada"],
        &["Ada", "1", "2", "x", " 39 ", "", "5"],
        &["Ada", "1", "2"],
        &["", "", ""],
        &["\u{1F600}", "007"],
    ] {
        let expected: String = session
            .simulate(lines)
            .unwrap()
            .iter()
            .map(|p| format!("{p}\n"))
            .collect();
        for ending in ["\n", "\r\n"] {
            let input: String = lines.iter().map(|l| format!("{l}{ending}")).collect();
            assert_eq!(succeeds(&path, input.as_bytes()), expected, "{input:?}");
        }
    }
}

#[test]
fn the_example_session() {
    assert_eq!(
        succeeds(&example("adder.sw"), b"Ada\n1\n2\nx\n 39 \n\n"),
        "What's your name?\n\
         Hello, Ada! Type numbers to add, one per line, and an empty line to stop.\n  \
         total: 1\n  \
         total: 3\n\
         \"x\" isn't a number; skipped\n  \
         total: 42\n\
         The sum is 42. Goodbye, Ada.\n"
    );
}

/// The prompt appears before the program waits for input: output is flushed
/// before every read, even though standard output is a pipe.
#[test]
fn the_prompt_appears_before_the_program_reads() {
    let mut child = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .arg(example("adder.sw"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null()),
    );
    let mut stdout = BufReader::new(child.stdout.take().unwrap());
    let (send, receive) = std::sync::mpsc::channel();
    let reader = std::thread::spawn(move || {
        let mut line = String::new();
        stdout.read_line(&mut line).expect("read the prompt");
        send.send(line).unwrap();
        stdout
    });
    let prompt = receive.recv_timeout(Duration::from_secs(60));
    // Answer (or give up), so the program finishes either way.
    drop(child.stdin.take());
    child.wait().expect("run stitchwort");
    reader.join().unwrap();
    assert_eq!(prompt.as_deref(), Ok("What's your name?\n"));
}

/// Echoes each line in brackets, and keeps reading after the end of input.
const ECHO: &str = r#"
def showLine : Option Text -> Text
  | None => "<end>"
  | Some l  => "[" ++ l ++ "]"

def echo : Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    IO.print (showLine (IO.readLine ()))
    echo n

def main () : {IO} () := echo 3
"#;

#[test]
fn reading_real_standard_input() {
    let echo = source_file("echo.sw", ECHO);
    for (input, expected) in [
        (&b""[..], "<end>\n<end>\n<end>\n"),
        (b"a", "[a]\n<end>\n<end>\n"),
        (b"a\nb", "[a]\n[b]\n<end>\n"),
        (b"a\r\nb\r\n", "[a]\n[b]\n<end>\n"),
        (b"a\r\n\r\nb", "[a]\n[]\n[b]\n"),
        (b"\n", "[]\n<end>\n<end>\n"),
        (b"a\rb\r", "[a\rb\r]\n<end>\n<end>\n"),
        (
            "h\u{E9}llo \u{1F600}\n".as_bytes(),
            "[h\u{E9}llo \u{1F600}]\n<end>\n<end>\n",
        ),
        (b"x\0y\n", "[x\0y]\n<end>\n<end>\n"),
    ] {
        assert_eq!(succeeds(&echo, input), expected, "{input:?}");
    }
}

const READ_ALL: &str = r#"
def main () : {IO} () :=
  IO.print ("<" ++ IO.readAll () ++ ">")
"#;

const READ_MIXED: &str = r#"
def showLine : Option Text -> Text
  | None => "<end>"
  | Some l  => "[" ++ l ++ "]"

def main () : {IO} () :=
  IO.print (showLine (IO.readLine ()))
  IO.print ("<" ++ IO.readAll () ++ ">")
  IO.print (showLine (IO.readLine ()))
"#;

#[test]
fn read_all_gives_standard_input_verbatim() {
    let path = source_file("read-all.sw", READ_ALL);
    for (input, expected) in [
        (&b""[..], "<>\n"),
        (b"a\nb\n", "<a\nb\n>\n"),
        (b"a\r\nb\r\n", "<a\r\nb\r\n>\n"),
        (b"a\r\nb", "<a\r\nb>\n"),
        ("h\u{E9}llo\n".as_bytes(), "<h\u{E9}llo\n>\n"),
    ] {
        assert_eq!(succeeds(&path, input), expected, "{input:?}");
    }
}

#[test]
fn read_all_after_read_line_gives_the_rest_and_nothing_remains() {
    let path = source_file("read-mixed.sw", READ_MIXED);
    assert_eq!(succeeds(&path, b"a\r\nb\r\nc"), "[a]\n<b\r\nc>\n<end>\n");
    assert_eq!(succeeds(&path, b""), "<end>\n<>\n<end>\n");
}

#[test]
fn invalid_utf8_for_read_all_is_an_error() {
    let path = source_file("read-all-utf8.sw", READ_ALL);
    assert_eq!(fails_running(&path, b"a\nb\n\xff", "E-IO"), "");
    assert!(
        stderr(&run(&path, b"a\nb\n\xff")).contains("line 3 of standard input isn't valid UTF-8")
    );
}

#[test]
fn invalid_utf8_input_is_an_error() {
    let echo = source_file("echo-utf8.sw", ECHO);
    let printed = fails_running(&echo, b"ok\n\xff\nmore\n", "E-IO");
    assert_eq!(printed, "[ok]\n");
    assert!(
        stderr(&run(&echo, b"ok\n\xff\n")).contains("line 2 of standard input isn't valid UTF-8")
    );
}

#[test]
fn a_write_error_is_an_error() {
    let path = source_file("print.sw", "def main () : {IO} () := IO.print \"hello\"\n");
    // Standard output is a pipe that nobody reads.
    // The pipe and the spawn happen under `SPAWN`, so no other child can
    // inherit the read end before it's closed.
    let child = {
        let _guard = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
        let (reader, writer) = std::io::pipe().expect("a pipe");
        drop(reader);
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .arg(&path)
            .stdin(Stdio::null())
            .stdout(writer)
            .stderr(Stdio::piped())
            .spawn()
            .expect("start stitchwort")
    };
    let output = child.wait_with_output().expect("run stitchwort");
    assert_eq!(output.status.code(), Some(2));
    let errors = String::from_utf8(output.stderr).unwrap();
    assert!(
        errors.contains("[E-IO]") && errors.contains("can't write standard output"),
        "{errors}"
    );
}

#[test]
fn a_pure_main_runs() {
    let path = source_file("pure.sw", "def main () : () := ()\n");
    assert_eq!(succeeds(&path, b"unread\n"), "");
}

#[test]
fn a_program_that_doesnt_check_isnt_run() {
    let path = source_file("ill-typed.sw", "def main () : {IO} () := IO.print 3\n");
    assert_eq!(fails(&path, b"", "E-TYPE-MISMATCH"), "");
}

#[test]
fn a_program_needs_a_main() {
    let path = source_file("no-main.sw", "def start () : {IO} () := IO.print \"hi\"\n");
    assert_eq!(fails(&path, b"", "E-NO-MAIN"), "");
}

#[test]
fn main_must_have_the_right_type() {
    let path = source_file(
        "main-type.sw",
        "ability Abort where\n  \
         abort : () -> {Abort} ()\n\n\
         def main () : {IO, Abort} () := abort ()\n",
    );
    assert_eq!(fails(&path, b"", "E-MAIN-TYPE"), "");
    insta::assert_snapshot!(
        stderr(&run(&path, b"")).replace(path.to_str().unwrap(), "main-type.sw")
    );
}

/// A `main` that may fail, as every AoC day's does: it reads a line, and
/// fails on `bad`.
const FAILING_MAIN: &str = "import Std (Fail)

def main(): {IO, Fail} () :=
  let line := IO.readLine ()
  if line == Option.Some \"bad\" then Fail.fail \"the input was bad\" else IO.print \"fine\"
";

/// The failure's message is printed on standard error, and the exit code is 1.
fn fails_with_message(output: &Output) {
    assert_eq!(output.status.code(), Some(1), "{}", stderr(output));
    assert_eq!(stdout(output), "");
    assert_eq!(stderr(output), "error: the input was bad\n");
}

// SW-434: `run` refused every `{IO, Fail}` main, since the wrapper that
// handles `Fail` (`Std.Fail.recover (m => Some m) …`, `driver::run`) stopped
// checking: the pure handler's body fixed the row it shares with the
// program to `Empty`.
#[test]
fn a_main_that_may_fail_runs() {
    let path = source_file("may-fail.sw", FAILING_MAIN);
    assert_eq!(succeeds(&path, b"ok\n"), "fine\n");
    fails_with_message(&run(&path, b"bad\n"));
}

#[test]
fn a_project_function_that_may_fail_runs() {
    let dir = std::env::temp_dir().join(format!("stitchwort-run-{}-project", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src/Day")).expect("create project");
    std::fs::write(dir.join("stitchwort.yaml"), "").expect("write project file");
    std::fs::write(
        dir.join("src/Day/Day.sw"),
        format!("namespace Day\n\n{FAILING_MAIN}"),
    )
    .expect("write source");
    let name = std::ffi::OsStr::new("Day.main");
    let output = run_in(&dir, name, b"ok\n");
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(stdout(&output), "fine\n");
    fails_with_message(&run_in(&dir, name, b"bad\n"));
}

// SW-435: a `main` with `Fail` used to be wrapped in `Std.Fail.recover (m =>
// Some m) …`, which wrote `Option Text` with `Text` as the program saw it.
// The runner performs `Fail` itself now (docs/proposals/partial-stage-2.md),
// and the call it builds names nothing the program can shadow.
#[test]
fn a_main_that_may_fail_runs_whatever_the_program_declares() {
    let path = source_file(
        "shadowed-text.sw",
        "import Std (Fail)\n\ndef Text : Type := Nat\n\ndef main(): {IO, Fail} () := ()\n",
    );
    assert_eq!(succeeds(&path, b""), "");
}

/// `main` may be `{IO, Fail, Partial}`, or any part of it, but nothing more.
#[test]
fn a_main_may_have_fail_with_partial_and_nothing_else() {
    for (name, row) in [
        ("io-fail-partial.sw", "{IO, Fail, Partial}"),
        ("fail-partial.sw", "{Fail, Partial}"),
        ("partial-fail.sw", "{Partial, Fail}"),
    ] {
        let path = source_file(
            name,
            &format!("import Std (Fail)\n\ndef main(): {row} () := ()\n"),
        );
        assert_eq!(succeeds(&path, b""), "", "{row}");
    }
    let path = source_file(
        "fail-partial-log.sw",
        "import Std (Fail)\n\n\
         ability Log where\n  \
         log: Text -> {Log} ()\n\n\
         def main(): {IO, Fail, Partial, Log} () := Log.log \"hi\"\n",
    );
    let output = run(&path, b"");
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(
        stderr(&output).contains("[E-MAIN-TYPE]")
            && stderr(&output).contains("`() -> {IO, Fail, Partial} ()`"),
        "{}",
        stderr(&output)
    );
}

/// Runs `stitchwort run [flag] path` with `input` piped to it, for each of
/// the three runners: native, `--js` and `--reference`. Each run's stdout,
/// stderr and exit status.
fn run_three_ways(path: &Path, input: &[u8]) -> Vec<(&'static str, String, String, Option<i32>)> {
    ["", "--js", "--reference"]
        .into_iter()
        .map(|flag| {
            let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
            command.args(["run", "--no-cache"]);
            if !flag.is_empty() {
                command.arg(flag);
            }
            let mut child = spawn(
                command
                    .arg(path)
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::piped()),
            );
            let mut stdin = child.stdin.take().unwrap();
            let input = input.to_vec();
            let writer = std::thread::spawn(move || {
                let _ = stdin.write_all(&input);
            });
            let output = child.wait_with_output().expect("run stitchwort");
            writer.join().unwrap();
            (
                flag,
                stdout(&output).to_string(),
                stderr(&output).to_string(),
                output.status.code(),
            )
        })
        .collect()
}

/// Every runner prints `stdout`, then `stderr` on standard error, and exits
/// with `status`.
fn same_three_ways(path: &Path, input: &[u8], out: &str, err: &str, status: i32) {
    for (flag, got_out, got_err, got_status) in run_three_ways(path, input) {
        let what = format!(
            "{} {flag} with {:?}",
            path.display(),
            String::from_utf8_lossy(input)
        );
        assert_eq!(got_out, out, "{what}\n{got_err}");
        assert_eq!(got_err, err, "{what}");
        assert_eq!(got_status, Some(status), "{what}");
    }
}

// Partial stage 2 (docs/proposals/partial-stage-2.md): `main` may be
// `{IO, Fail, Partial}`, and the runner performs `Fail` itself, as it
// performs `IO.print`.

/// A partial read loop that fails on a bad line: what it printed stays, the
/// message goes to standard error, and the exit status is 1, alike on every
/// runner.
#[test]
fn a_partial_main_that_may_fail_runs_three_ways() {
    let path = example("main-fail-partial.sw");
    same_three_ways(
        &path,
        b"1\n2\n",
        "total so far 1\ntotal so far 3\nsum 3\n",
        "",
        0,
    );
    same_three_ways(
        &path,
        b"1\n2\nx\n4\n",
        "total so far 1\ntotal so far 3\n",
        "error: expected a whole number, got 'x'\n",
        1,
    );
    // Failing before printing anything.
    same_three_ways(
        &path,
        b"x\n",
        "",
        "error: expected a whole number, got 'x'\n",
        1,
    );
}

/// A failure a million calls deep in partial recursion, with a million
/// callers waiting on it, and one after a million iterations of a tail
/// loop: neither overflows, on any runner.
#[test]
fn a_failure_deep_in_partial_recursion_doesnt_overflow() {
    let path = example("main-fail-partial-deep.sw");
    same_three_ways(
        &path,
        b"descend\n1000000\n",
        "going 1000000 deep\n",
        "error: hit the bottom\n",
        1,
    );
    same_three_ways(
        &path,
        b"countdown\n1000000\n",
        "going 1000000 deep\n",
        "error: counted down to 0\n",
        1,
    );
}

/// The `{IO, Fail}` examples behave as before stage 2, now that the runner
/// performs `Fail` rather than a `Fail.recover` wrapper handling it.
#[test]
fn a_total_main_that_may_fail_runs_three_ways() {
    same_three_ways(
        &example("main-fail.sw"),
        b"",
        "reading the numbers\n",
        "error: expected a whole number, got 'x3'\n",
        1,
    );
    same_three_ways(
        &example("main-fail-ok.sw"),
        b"",
        "reading the numbers\ntotal 6\n",
        "",
        0,
    );
}

/// `Fail.toResult` takes a partial program, and is then partial itself: its
/// row `{Fail | e}` has a divergence index (lane D of
/// docs/proposals/partial-handlers.md, D1255). The native and JS runners
/// run a handler around partial code from lane C of that note; until then,
/// the reference runner.
#[test]
fn fail_can_be_handled_around_partial_code() {
    let path = source_file(
        "handled-partial.sw",
        "import Std (Fail, Result)\n\n\
         def search (n: Nat): {Fail, Partial} Nat :=\n  \
         if n > 1000 then Fail.fail \"gave up\" else if n * n == 1764 then n else search (n + 1)\n\n\
         def main(): {IO, Partial} () :=\n  \
         match Fail.toResult (() => search 0) with\n    \
         | Ok n => IO.print \"found ${n}\"\n    \
         | Err message => IO.print message\n",
    );
    let reference = run_three_ways(&path, b"")
        .into_iter()
        .find(|(flag, ..)| *flag == "--reference")
        .expect("the reference runner");
    assert_eq!(
        (reference.1.as_str(), reference.3),
        ("found 42\n", Some(0)),
        "{}",
        reference.2
    );
}

/// The same handler around total code is total: `main` needn't say
/// `Partial`, and every runner runs it.
#[test]
fn fail_handled_around_total_code_runs_everywhere() {
    let path = source_file(
        "handled-total.sw",
        "import Std (Fail, Result)\n\n\
         def step (n: Nat): {IO, Fail} Nat :=\n  \
         IO.print \"step ${n}\"\n  \
         if n > 2 then Fail.fail \"too big\" else n + 1\n\n\
         def main(): {IO} () :=\n  \
         match Fail.toResult (() => step 3) with\n    \
         | Ok n => IO.print \"ok ${n}\"\n    \
         | Err message => IO.print \"error: ${message}\"\n",
    );
    same_three_ways(&path, b"", "step 3\nerror: too big\n", "", 0);
}

#[test]
fn a_missing_file_is_an_error() {
    let output = run(Path::new("no/such/file.sw"), b"");
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).contains("can't read"));
}

// Partial programs (docs/proposals/partial.md): loops with no bound.

/// The adder reads until the end of its input, however long: five times
/// the bound its fuelled version (adder-fuel.sw) stops at.
#[test]
fn a_partial_main_reads_until_the_end_of_its_input() {
    let mut input = String::from("Ada\n");
    for n in 1..=5000 {
        input.push_str(&format!("{n}\n"));
    }
    let printed = succeeds(&example("adder.sw"), input.as_bytes());
    assert!(
        printed.ends_with("  total: 12502500\nThe sum is 12502500. Goodbye, Ada.\n"),
        "{}",
        &printed[printed.len().saturating_sub(200)..]
    );
    // The fuelled version stops counting after 1000 lines.
    let fuelled = succeeds(&example("adder-fuel.sw"), input.as_bytes());
    assert!(
        fuelled.ends_with("The sum is 500500. Goodbye, Ada.\n"),
        "{fuelled}"
    );
}

#[test]
fn cat_copies_its_input() {
    let input: String = (0..2000).map(|i| format!("line {i}\n\n")).collect();
    assert_eq!(succeeds(&example("cat.sw"), input.as_bytes()), input);
    assert_eq!(succeeds(&example("cat.sw"), b""), "");
    assert_eq!(
        succeeds(&example("cat.sw"), b"no line ending"),
        "no line ending\n"
    );
}

#[test]
fn collatz_counts_its_steps() {
    assert_eq!(
        succeeds(&example("collatz.sw"), b""),
        "27 reaches 1 in 111 steps\n"
    );
}

#[test]
fn a_match_in_a_partial_function_is_lifted() {
    assert_eq!(
        succeeds(&example("partial-match.sw"), b""),
        "found 4 from 2\n"
    );
}

/// A partial `main` that never finishes runs until it's stopped: the
/// runner has no limit on ticks, and each step between them has its own
/// budget.
#[test]
fn an_endless_partial_main_runs_until_stopped() {
    // Output is flushed before every read, so `started` shows.
    let path = source_file(
        "spin.sw",
        "import Std (Nat)\n\n\
         def spin (n : Nat) : {Partial} Nat := spin (n + 1)\n\n\
         def main () : {IO, Partial} () :=\n  \
         IO.print \"started\"\n  \
         let l := IO.readLine ()\n  \
         IO.print (Nat.toText (spin 0))\n",
    );
    let mut child = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .arg(&path)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped()),
    );
    let mut stdout = BufReader::new(child.stdout.take().unwrap());
    let mut line = String::new();
    stdout.read_line(&mut line).expect("read the first line");
    assert_eq!(line, "started\n");
    std::thread::sleep(Duration::from_secs(2));
    let running = child.try_wait().expect("check the child");
    child.kill().expect("stop it");
    child.wait().expect("wait for it");
    assert!(running.is_none(), "it stopped by itself: {running:?}");
}

/// SW-280: a program that imports none of the library files holding the
/// natives' definitions (`Text.length`, `Nat.toInt`, ...) runs. Binding the
/// natives asked the registry for those library built-ins, and the debug
/// assertion that library built-ins are reached only through the loader
/// panicked. A test binary is a debug build, so it exercises the assertion.
#[test]
fn a_program_that_loads_no_native_library_files_runs() {
    let path = source_file(
        "no-natives.sw",
        "import Std (IO, Nat)\n\ndef main(): {IO} () :=\n  IO.print (\"n: \" ++ Nat.toText 3)\n",
    );
    assert_eq!(succeeds(&path, b""), "n: 3\n");
}

/// Copies the directory `from` into `to`, recursively.
fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("create the copy");
    for entry in std::fs::read_dir(from).expect("read the directory") {
        let path = entry.expect("an entry").path();
        let target = to.join(path.file_name().unwrap());
        if path.is_dir() {
            copy_tree(&path, &target);
        } else {
            std::fs::copy(&path, &target).expect("copy a file");
        }
    }
}

/// SW-145: with `STITCHWORT_STD_DIR` set, `stitchwort run` reads the
/// standard library from that directory as it is now: an edit to a library
/// function's body is seen with no rebuild, also through the check cache
/// (its keys have the text read), and an error in a library file names the
/// file on disk.
#[test]
fn std_dir_reads_the_library_from_disk() {
    let std = std::env::temp_dir().join(format!("stitchwort-std-dir-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&std);
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("../elab/src/std"),
        &std,
    );
    let iterate = std.join("Nat/Iterate.sw");
    let original = std::fs::read_to_string(&iterate).unwrap();
    let with_probe = |body: &str| {
        let text = format!("{original}\ndef Nat.stdDirProbe (n: Nat): Nat := {body}\n");
        std::fs::write(&iterate, text).unwrap();
    };
    let program = source_file(
        "std-dir.sw",
        "import Std (IO, Nat)\n\ndef main(): {IO} () :=\n  IO.print (Nat.toText (Nat.stdDirProbe 41))\n",
    );
    let cache = std.with_extension("cache");
    let run_with_std = || {
        let _guard = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--cache-dir"])
            .arg(&cache)
            .arg(&program)
            .env("STITCHWORT_STD_DIR", &std)
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort")
    };
    with_probe("n + 1");
    let output = run_with_std();
    assert_eq!(stdout(&output), "42\n", "{}", stderr(&output));
    // The same cache directory: the edited file's entry is a miss.
    with_probe("n + 2");
    let output = run_with_std();
    assert_eq!(stdout(&output), "43\n", "{}", stderr(&output));
    with_probe("n + True");
    let output = run_with_std();
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let shown = iterate.display().to_string();
    assert!(
        stderr(&output).contains(&shown),
        "the error names {shown}:\n{}",
        stderr(&output)
    );
    let _ = std::fs::remove_dir_all(&std);
    let _ = std::fs::remove_dir_all(&cache);
}

/// `IO.randomSeed` gives a fresh 64-bit number each run.
#[test]
fn the_random_seed_is_fresh_each_run() {
    let path = source_file(
        "seed.sw",
        "import Std (IO, Nat)\ndef main () : {IO} () := IO.print (Nat.toText (IO.randomSeed ()))\n",
    );
    let seeds: Vec<u64> = (0..3)
        .map(|_| {
            let output = run(&path, b"");
            assert!(output.status.success(), "{}", stderr(&output));
            String::from_utf8(output.stdout)
                .unwrap()
                .trim()
                .parse()
                .expect("a 64-bit number")
        })
        .collect();
    assert!(seeds[0] != seeds[1] || seeds[1] != seeds[2], "{seeds:?}");
}

/// `IO.args` gives the arguments after `--`, flags among them; `run`'s own
/// flags come before it. On the machine and as native code.
#[test]
fn the_arguments_after_a_double_dash_are_the_programs() {
    let path = source_file(
        "args.sw",
        "import Std (IO, List, Text)\ndef main () : {IO} () := IO.print (Text.joinWith (IO.args ()) \"|\")\n",
    );
    let run_with = |flags: &[&str], args: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .args(flags)
            .arg(&path)
            .args(args)
            .output()
            .expect("run stitchwort");
        assert!(output.status.success(), "{}", stderr(&output));
        String::from_utf8(output.stdout).unwrap()
    };
    assert_eq!(run_with(&[], &[]), "\n");
    assert_eq!(run_with(&[], &["--", "11", "a b", "--js"]), "11|a b|--js\n");
    if cfg!(feature = "native") {
        assert_eq!(run_with(&["--native"], &["--", "x", "y"]), "x|y\n");
    }
}

/// SW-863: the list builders run in constant stack, so a list longer than the
/// 2,000,000-frame limit goes through them (calls modulo a constructor are
/// loops on the fast runtime, `stitchwort_rt::trmc`, and in the JS
/// generator's loops). A frame per element would be `E-RESOURCE` here. A
/// callback that performs abilities in a row such as `{IO}` isn't covered:
/// it still uses a frame per element on the fast runtime.
#[test]
fn list_builders_run_on_two_million_elements() {
    let path = source_file(
        "builders-deep.sw",
        "import Std (List, Nat)\n\
         def inc(x: Nat): Nat := x + 1\n\
         def even(x: Nat): Bool := if x % 2 == 0 then True else False\n\
         def n(xs: List Nat): Text := Nat.toText (List.length xs)\n\
         def main(): {IO} () :=\n  \
           let xs := List.range 2100000\n  \
           let _ := IO.print (n (List.map xs inc))\n  \
           let _ := IO.print (n (List.filter xs even))\n  \
           let _ := IO.print (n (xs ++ xs))\n  \
           IO.print (n (List.concat [xs, xs]))\n",
    );
    let want = "2100000\n1050000\n4200000\n4200000\n";
    let run_with = |flags: &[&str]| {
        let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["run", "--no-cache"])
            .args(flags)
            .arg(&path)
            .output()
            .expect("run stitchwort");
        assert!(output.status.success(), "{flags:?}: {}", stderr(&output));
        String::from_utf8(output.stdout).unwrap()
    };
    assert_eq!(run_with(&[]), want);
    if Command::new("node").arg("--version").output().is_ok() {
        assert_eq!(run_with(&["--js"]), want);
    }
    if cfg!(feature = "native") {
        assert_eq!(run_with(&["--native"]), want);
    }
}
