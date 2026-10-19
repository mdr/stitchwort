//! Running `main` against real input and output (docs/proposals/text-and-io.md,
//! "`main` and `stitchwort run`"), with the input and output in memory. The
//! command itself is tested end to end in `crates/cli/tests/run.rs`.
//!
//! The reference is the prelude's `simulate`: a program run with some lines
//! of input must print exactly what `simulate` records, each payload followed
//! by LF.

use std::cell::RefCell;
use std::io::{self, BufRead, Read, Write};
use std::rc::Rc;

use stitchwort_core::{Limits, ResourceError};
use stitchwort_driver::driver::Session;
use stitchwort_driver::run::RunError;

fn load(source: &str) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load("test.sw", source) {
        panic!("{errors:#?}");
    }
    session
}

/// Runs `main` with `input`: what it printed, and how it ended.
fn run_session(session: &mut Session, input: &[u8]) -> (String, Result<(), RunError>) {
    let main = session.main().expect("`main` has the right type");
    let mut output = Vec::new();
    let result = session.run_main(&main, &mut &input[..], &mut output);
    (String::from_utf8(output).expect("output is UTF-8"), result)
}

fn run(source: &str, input: &[u8]) -> (String, Result<(), RunError>) {
    run_session(&mut load(source), input)
}

/// Runs `main` with `input`, which must succeed: what it printed.
fn output(source: &str, input: &[u8]) -> String {
    let (out, result) = run(source, input);
    result.unwrap_or_else(|e| panic!("{e}"));
    out
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

def main () : {IO} () := echo 4
"#;

/// Prints everything `readAll` gives in brackets.
const SLURP: &str = r#"
def main () : {IO} () :=
  let a := IO.readAll ()
  IO.print ("[" ++ a ++ "]")
"#;

/// A `readLine`, then `readAll`, then `readLine` and `readAll` again.
const MIXED: &str = r#"
def showLine : Maybe Text -> Text
  | Nothing => "<end>"
  | Just l  => "[" ++ l ++ "]"

def main () : {IO} () :=
  IO.print (showLine (IO.readLine ()))
  IO.print ("all=[" ++ IO.readAll () ++ "]")
  IO.print (showLine (IO.readLine ()))
  IO.print ("again=[" ++ IO.readAll () ++ "]")
"#;

/// Prints each line of `IO.readAllLines ()`.
const LINES: &str = r#"
def printAll : List Text -> {IO} ()
  | Nil       => ()
  | Cons l ls =>
    IO.print ("<" ++ l ++ ">")
    printAll ls

def main () : {IO} () := printAll (IO.readAllLines ())
"#;

const GREET: &str = r#"
def textOr (d : Text) : Maybe Text -> Text
  | Nothing => d
  | Just t  => t

def main () : {IO} () :=
  IO.print "Name?"
  let name := IO.readLine ()
  IO.print ("Hello, " ++ textOr "stranger" name ++ "!")
"#;

// The simulator and the runner agree

/// Programs to compare, as sources.
fn programs() -> Vec<(&'static str, String)> {
    let adder = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept/adder.sw"),
    )
    .expect("readable example");
    vec![
        ("echo", ECHO.to_string()),
        ("greet", GREET.to_string()),
        ("adder", adder),
        (
            "a payload with line feeds",
            "def main () : {IO} () :=\n  IO.print \"a\\nb\"\n  IO.print \"\"\n  IO.print \"\\r\"\n"
                .to_string(),
        ),
        ("readAllLines", LINES.to_string()),
        ("pure", "def main () : () := ()\n".to_string()),
        (
            "with State handled inside",
            r#"
ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

def runState (init : s) (prog : () -> {State s | e} a) : {e} Pair a s :=
  let run : s -> {e} Pair a s :=
    handle prog () with
      | return x       => \st => MkPair x st
      | get u, k       => \st => k st st
      | put st2, k     => \st => k () st2
  run init

def count () : {IO, State Nat} () :=
  let a := IO.readLine ()
  put (get () + 1)
  IO.print (Nat.toText (get ()))
  let b := IO.readLine ()
  put (get () + 1)
  IO.print (Nat.toText (get ()))

def main () : {IO} () :=
  let r := runState 10 count
  IO.print "done"
"#
            .to_string(),
        ),
    ]
}

/// Scripted inputs, as lines.
const INPUTS: &[&[&str]] = &[
    &[],
    &[""],
    &["", ""],
    &["Ada"],
    &["Ada", "1", "2", "x", " 39 ", "", "5"],
    &["h\u{E9}llo \u{1F600}", "e\u{301}", "tab\there", "nul\0x"],
    &["a\rb", "  spaced  "],
];

/// Ways of writing `lines` as input that the runner must read as the same
/// lines: LF or CRLF endings, and without the final line ending if that
/// doesn't lose a line.
fn encodings(lines: &[&str]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for ending in ["\n", "\r\n"] {
        let mut text: String = lines.iter().map(|l| format!("{l}{ending}")).collect();
        out.push(text.clone().into_bytes());
        if lines.last().is_some_and(|l| !l.is_empty()) {
            text.truncate(text.len() - ending.len());
            out.push(text.into_bytes());
        }
    }
    out
}

#[test]
fn the_runner_prints_what_simulate_records() {
    for (name, source) in programs() {
        let mut session = load(&source);
        for lines in INPUTS {
            let expected: String = session
                .simulate(lines)
                .unwrap_or_else(|e| panic!("{e:?}"))
                .iter()
                .map(|p| format!("{p}\n"))
                .collect();
            for input in encodings(lines) {
                let (out, result) = run_session(&mut session, &input);
                result.unwrap_or_else(|e| panic!("{name}: {e}"));
                assert_eq!(
                    out,
                    expected,
                    "{name}, input {:?}",
                    String::from_utf8_lossy(&input)
                );
            }
        }
    }
}

/// Programs that read with `readAll`, which keeps line endings: simulate
/// agrees with the runner when each line ends in LF.
#[test]
fn readall_under_the_runner_matches_simulate() {
    for source in [SLURP, MIXED] {
        let mut session = load(source);
        for lines in INPUTS {
            let expected: String = session
                .simulate(lines)
                .unwrap_or_else(|e| panic!("{e:?}"))
                .iter()
                .map(|p| format!("{p}\n"))
                .collect();
            let input: String = lines.iter().map(|l| format!("{l}\n")).collect();
            let (out, result) = run_session(&mut session, input.as_bytes());
            result.unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(out, expected, "input {input:?}");
        }
    }
}

// The interpreter's contract

#[test]
fn readall_gives_the_input_as_it_is() {
    assert_eq!(output(SLURP, b""), "[]\n");
    assert_eq!(output(SLURP, b"a\nb\n"), "[a\nb\n]\n");
    assert_eq!(output(SLURP, b"a\r\nb\r\n"), "[a\r\nb\r\n]\n");
    // The final line needs no line ending, and a final CR stays.
    assert_eq!(output(SLURP, b"a\nb"), "[a\nb]\n");
    assert_eq!(output(SLURP, b"a\r"), "[a\r]\n");
    assert_eq!(output(SLURP, b"\n\n"), "[\n\n]\n");
    let input = "h\u{E9}llo\n\u{1F600}\nx\0y";
    assert_eq!(output(SLURP, input.as_bytes()), format!("[{input}]\n"));
}

#[test]
fn readall_after_readline_gives_the_rest() {
    assert_eq!(
        output(MIXED, b"a\r\nb\r\nc"),
        "[a]\nall=[b\r\nc]\n<end>\nagain=[]\n"
    );
    assert_eq!(output(MIXED, b"a\n"), "[a]\nall=[]\n<end>\nagain=[]\n");
    assert_eq!(output(MIXED, b""), "<end>\nall=[]\n<end>\nagain=[]\n");
}

#[test]
fn readline_after_readall_is_end_of_input() {
    let source = r#"
def main () : {IO} () :=
  IO.print (IO.readAll ())
  match IO.readLine () with
    | Nothing => IO.print "<end>"
    | Just l  => IO.print l
"#;
    assert_eq!(output(source, b"a\nb\n"), "a\nb\n\n<end>\n");
}

#[test]
fn readall_lines_split_like_text_lines() {
    assert_eq!(output(LINES, b"a\r\nb"), "<a>\n<b>\n");
    assert_eq!(output(LINES, b"a\nb\n"), "<a>\n<b>\n");
    assert_eq!(output(LINES, b""), "");
    assert_eq!(output(LINES, b"\n"), "<>\n");
}

#[test]
fn invalid_utf8_in_readall_is_an_error_with_a_line_number() {
    // Lines already read, newlines before the bad byte, and one.
    for (input, line) in [(&b"\xff"[..], 1), (b"a\n\xff", 2), (b"a\nb\n\xc3\n", 3)] {
        let (out, result) = run(SLURP, input);
        assert_eq!(out, "", "{input:?}");
        assert!(
            matches!(result, Err(RunError::InvalidUtf8 { line: l }) if l == line),
            "{input:?}: {result:?}"
        );
    }
    let (out, result) = run(MIXED, b"x\ny\n\xff");
    assert_eq!(out, "[x]\n");
    assert!(
        matches!(result, Err(RunError::InvalidUtf8 { line: 3 })),
        "{result:?}"
    );
}

#[test]
fn empty_input_is_end_of_input() {
    assert_eq!(output(ECHO, b""), "<end>\n<end>\n<end>\n<end>\n");
}

#[test]
fn an_empty_line_is_not_end_of_input() {
    assert_eq!(output(ECHO, b"\n"), "[]\n<end>\n<end>\n<end>\n");
    assert_eq!(output(ECHO, b"\r\n\n"), "[]\n[]\n<end>\n<end>\n");
}

#[test]
fn a_final_line_without_a_line_ending_is_read_once() {
    assert_eq!(output(ECHO, b"a\nb"), "[a]\n[b]\n<end>\n<end>\n");
}

#[test]
fn only_a_trailing_lf_and_a_cr_before_it_are_removed() {
    assert_eq!(output(ECHO, b"a\r\nb\r\n"), "[a]\n[b]\n<end>\n<end>\n");
    // A CR anywhere else is part of the line.
    assert_eq!(output(ECHO, b"a\rb\n"), "[a\rb]\n<end>\n<end>\n<end>\n");
    assert_eq!(output(ECHO, b"a\r\r\n"), "[a\r]\n<end>\n<end>\n<end>\n");
    assert_eq!(output(ECHO, b"\ra\n"), "[\ra]\n<end>\n<end>\n<end>\n");
    // Without an LF, a final CR stays.
    assert_eq!(output(ECHO, b"a\r"), "[a\r]\n<end>\n<end>\n<end>\n");
    // Spaces aren't trimmed.
    assert_eq!(output(ECHO, b" a \t\n"), "[ a \t]\n<end>\n<end>\n<end>\n");
}

#[test]
fn text_is_read_and_written_as_utf8() {
    let input = "h\u{E9}llo\ne\u{301}\n\u{1F600}\nx\0y\n";
    assert_eq!(
        output(ECHO, input.as_bytes()),
        "[h\u{E9}llo]\n[e\u{301}]\n[\u{1F600}]\n[x\0y]\n"
    );
}

#[test]
fn invalid_utf8_is_an_error_not_end_of_input() {
    for bad in [
        &b"\xff"[..],
        b"\xc3",         // a truncated sequence
        b"\xed\xa0\x80", // an encoded surrogate
        b"\xc0\x80",     // an overlong NUL
    ] {
        let mut input = b"ok\n".to_vec();
        input.extend_from_slice(bad);
        input.extend_from_slice(b"\nnever read\n");
        let (out, result) = run(ECHO, &input);
        // What was printed before the error still appears.
        assert_eq!(out, "[ok]\n", "{bad:?}");
        assert!(
            matches!(result, Err(RunError::InvalidUtf8 { line: 2 })),
            "{bad:?}: {result:?}"
        );
    }
}

/// Input that fails once `data` is used up.
struct FailingInput {
    data: &'static [u8],
}

impl Read for FailingInput {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let data = self.fill_buf()?;
        let n = data.len().min(buf.len());
        buf[..n].copy_from_slice(&data[..n]);
        self.consume(n);
        Ok(n)
    }
}

impl BufRead for FailingInput {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.data.is_empty() {
            Err(io::Error::other("the disk is on fire"))
        } else {
            Ok(self.data)
        }
    }
    fn consume(&mut self, n: usize) {
        self.data = &self.data[n..];
    }
}

#[test]
fn a_read_error_is_an_error_not_end_of_input() {
    let mut session = load(ECHO);
    let main = session.main().unwrap();
    let mut output = Vec::new();
    let result = session.run_main(&main, &mut FailingInput { data: b"a\n" }, &mut output);
    assert_eq!(String::from_utf8(output).unwrap(), "[a]\n");
    assert!(matches!(result, Err(RunError::Read(_))), "{result:?}");
    assert_eq!(result.unwrap_err().diagnostic(&main).code, "E-IO");
}

/// Output that records what's written and flushed, in order, to `log`, and
/// fails to write or flush if asked to.
struct Output {
    log: Rc<RefCell<Vec<String>>>,
    fail_write: bool,
    fail_flush: bool,
}

impl Write for Output {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.fail_write {
            return Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "nobody's listening",
            ));
        }
        self.log
            .borrow_mut()
            .push(format!("write {}", String::from_utf8_lossy(buf)));
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        if self.fail_flush {
            return Err(io::Error::other("the disk is full"));
        }
        self.log.borrow_mut().push("flush".into());
        Ok(())
    }
}

/// Input that records each time it's asked for more to `log`.
struct Input {
    log: Rc<RefCell<Vec<String>>>,
    data: &'static [u8],
}

impl Read for Input {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let data = self.fill_buf()?;
        let n = data.len().min(buf.len());
        buf[..n].copy_from_slice(&data[..n]);
        self.consume(n);
        Ok(n)
    }
}

impl BufRead for Input {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.log.borrow_mut().push("read".into());
        Ok(self.data)
    }
    fn consume(&mut self, n: usize) {
        self.data = &self.data[n..];
    }
}

fn run_logged(
    source: &str,
    input: &'static [u8],
    fail_write: bool,
    fail_flush: bool,
) -> (Vec<String>, Result<(), RunError>) {
    let mut session = load(source);
    let main = session.main().unwrap();
    let log = Rc::new(RefCell::new(Vec::new()));
    let mut output = Output {
        log: log.clone(),
        fail_write,
        fail_flush,
    };
    let mut input = Input {
        log: log.clone(),
        data: input,
    };
    let result = session.run_main(&main, &mut input, &mut output);
    let log = log.borrow().clone();
    (log, result)
}

#[test]
fn output_is_flushed_before_every_read_and_at_the_end() {
    let (log, result) = run_logged(GREET, b"Ada\n", false, false);
    result.unwrap();
    assert_eq!(
        log,
        [
            "write Name?",
            "write \n",
            "flush",
            "read",
            "write Hello, Ada!",
            "write \n",
            "flush"
        ]
    );
}

#[test]
fn a_write_error_stops_the_program() {
    let (log, result) = run_logged(GREET, b"Ada\n", true, false);
    // Nothing was read: the program stopped at its first `print`. (What was
    // written before an error is flushed, as far as possible.)
    assert_eq!(log, ["flush"]);
    assert!(
        matches!(&result, Err(RunError::Write(e)) if e.kind() == io::ErrorKind::BrokenPipe),
        "{result:?}"
    );
}

#[test]
fn a_flush_error_stops_the_program() {
    // The flush before the read fails, so the program never reads.
    let (log, result) = run_logged(GREET, b"Ada\n", false, true);
    assert_eq!(log, ["write Name?", "write \n"]);
    assert!(matches!(result, Err(RunError::Write(_))), "{result:?}");
    // The flush at the end counts too.
    let (_, result) = run_logged(
        "def main () : {IO} () := IO.print \"x\"\n",
        b"",
        false,
        true,
    );
    assert!(matches!(result, Err(RunError::Write(_))), "{result:?}");
}

#[test]
fn a_payload_with_a_line_feed_is_written_as_it_is() {
    let source = "def main () : {IO} () :=\n  IO.print \"a\\nb\"\n  IO.print \"\"\n";
    assert_eq!(output(source, b""), "a\nb\n\n");
}

#[test]
fn a_pure_main_runs_and_prints_nothing() {
    assert_eq!(output("def main () : () := ()\n", b"unread\n"), "");
}

#[test]
fn many_operations_run_without_growing_the_stack() {
    let source = "def printMany : Nat -> {IO} ()\n  \
                  | 0      => ()\n  \
                  | Succ n =>\n    \
                  IO.print \"x\"\n    \
                  printMany n\n\n\
                  def main () : {IO} () := printMany 20000\n";
    assert_eq!(output(source, b""), "x\n".repeat(20000));
}

// Resources

const SLOW: &str = "
def replicate : Nat -> a -> List a
  | Zero,   x => Nil
  | Succ n, x => Cons x (replicate n x)

def main () : {IO} () :=
  IO.print \"before\"
  IO.print (Nat.toText (List.length (replicate 100000 1)))
";

#[test]
fn running_out_of_resources_stops_the_program() {
    let mut session = load(SLOW);
    session.elab.limits = Limits {
        work: 100_000,
        ..Limits::default()
    };
    let (out, result) = run_session(&mut session, b"");
    assert_eq!(out, "before\n");
    let Err(e) = result else {
        panic!("it should run out")
    };
    assert!(
        matches!(e, RunError::Resource(ResourceError::Work)),
        "{e:?}"
    );
    let main = session.main().unwrap();
    let diagnostic = e.diagnostic(&main);
    assert_eq!(diagnostic.code, "E-RESOURCE");
    assert_eq!(diagnostic.labels[0].span, main.span);
}

#[test]
fn each_step_between_operations_has_its_own_limits() {
    // 2,000 prints take more than 100,000 steps in all, but few each.
    let source = "def printMany : Nat -> {IO} ()\n  \
                  | 0      => ()\n  \
                  | Succ n =>\n    \
                  IO.print \"x\"\n    \
                  printMany n\n\n\
                  def main () : {IO} () := printMany 2000\n";
    let mut session = load(source);
    session.elab.limits = Limits {
        work: 100_000,
        ..Limits::default()
    };
    let main = session.main().unwrap();
    let mut out = Vec::new();
    session.run_main(&main, &mut &b""[..], &mut out).unwrap();
    assert_eq!(out.len(), 4000);
    // `simulate` runs the whole program as one operation, and doesn't finish.
    assert_eq!(session.simulate(&[]).unwrap_err().code, "E-RESOURCE");
}

// `main` itself

fn main_error(source: &str) -> &'static str {
    match load(source).main() {
        Ok(_) => panic!("`main` should be refused"),
        Err(d) => d.code,
    }
}

#[test]
fn main_must_exist() {
    assert_eq!(main_error("def notMain () : {IO} () := ()\n"), "E-NO-MAIN");
}

#[test]
fn main_must_have_the_right_type() {
    for source in [
        "def main : Nat := 3\n",
        "def main () : {IO} Nat := 3\n",
        "def main (n : Nat) : {IO} () := ()\n",
        "def main () : Nat := 3\n",
        "ability Abort where\n  \
         abort : () -> {Abort} ()\n\n\
         def main () : {IO, Abort} () := abort ()\n",
    ] {
        assert_eq!(main_error(source), "E-MAIN-TYPE", "{source}");
    }
}
