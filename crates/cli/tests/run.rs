//! `stitchwort run`, end to end: the built command, with real standard input
//! and output (docs/proposals/text-and-io.md, "`main` and `stitchwort run`").
//! The runner's contract is tested in detail, in memory, in
//! `crates/driver/tests/run.rs`.

use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::Duration;

use stitchwort_cli::driver::Session;

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
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("run")
        .arg(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start stitchwort");
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
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("run")
        .arg(example("adder.sw"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("start stitchwort");
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
def showLine : Maybe Text -> Text
  | Nothing => "<end>"
  | Just l  => "[" ++ l ++ "]"

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
def showLine : Maybe Text -> Text
  | Nothing => "<end>"
  | Just l  => "[" ++ l ++ "]"

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
    let (reader, writer) = std::io::pipe().expect("a pipe");
    drop(reader);
    let output = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("run")
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(writer)
        .stderr(Stdio::piped())
        .output()
        .expect("run stitchwort");
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

/// A partial `main` that never finishes runs until it's stopped: the
/// runner has no limit on ticks, and each step between them has its own
/// budget.
#[test]
fn an_endless_partial_main_runs_until_stopped() {
    // Output is flushed before every read, so `started` shows.
    let path = source_file(
        "spin.sw",
        "def spin (n : Nat) : {Partial} Nat := spin (n + 1)\n\n\
         def main () : {IO, Partial} () :=\n  \
         IO.print \"started\"\n  \
         let l := IO.readLine ()\n  \
         IO.print (Nat.toText (spin 0))\n",
    );
    let mut child = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .arg("run")
        .arg(&path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start stitchwort");
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
