//! `Files` end to end (docs/proposals/file-io-and-text.md §2, §3, §6):
//! programs whose `main` uses the disk, run by the built command in a
//! temporary folder on each runner and compared with `Files.simulate`'s
//! disk; and the invariant that checking and testing a program never
//! performs its file operations, whatever it says.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use crate::common;

/// The check cache the runs here share, outside the folders the programs
/// see, so that a listing shows only what the test put there.
const CACHE: &str = concat!(env!("CARGO_TARGET_TMPDIR"), "/files-tests-cache");

/// A fresh, empty folder for one test.
fn work_dir(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join("files-tests")
        .join(name);
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("make the test's folder");
    dir
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}

/// `command`, in `dir`, with nothing on standard input.
fn output(mut command: Command, dir: &Path) -> Output {
    command
        .current_dir(dir)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("start stitchwort")
}

/// `stitchwort run FLAGS source ARGS` in `dir`.
fn run(dir: &Path, flags: &[&str], source: &Path, args: &[&str]) -> Output {
    let mut command = common::cli_with("run", flags);
    command
        .args(["--cache-dir", CACHE])
        .arg(source)
        .arg("--")
        .args(args);
    output(command, dir)
}

/// A small generator of pseudo-random numbers (xorshift), so each script is
/// the same on every run.
struct Seeded(u64);

impl Seeded {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

/// The paths a script touches, as Stitchwort expressions, each with whether
/// a script may write to it: missing ones, a folder, a file in it, a path
/// through a file, the starting folder; paths built by hand with parts that
/// hold `/` or are `""` or `.`, which both sides read through
/// `Path.normal`; and paths with `..`, which the host follows and the
/// pretend disk refuses, so they are only read, and their replies aren't
/// compared.
const PATHS: &[(&str, bool)] = &[
    ("\"a.txt\".toPath", true),
    ("\"b\".toPath", true),
    ("\"d\".toPath", true),
    ("\"d/x.txt\".toPath", true),
    ("\"d/y\".toPath", true),
    ("\"a.txt/z\".toPath", true),
    ("\"e/f\".toPath", true),
    ("\".\".toPath", true),
    ("{ parts = [\"d/y\"], absolute = False }", true),
    (
        "{ parts = [\"d\", \"\", \".\", \"z\"], absolute = False }",
        true,
    ),
    ("{ parts = [\".\"], absolute = False }", true),
    ("{ parts = [\"\", \"b\"], absolute = False }", true),
    ("\"..\".toPath", false),
    ("\"d/../d/x.txt\".toPath", false),
];

/// What the pretend disk says of a path with `..`.
const NO_CLIMBING: &str = "the pretend disk has no `..`";

/// What the folder holds before a script, as `Disk.fromList` and as files.
const START: &[(&str, &str)] = &[("d/x.txt", "x"), ("d/k/n", "")];

/// A script of `length` operations from `seed`: the lines of a `{Files}`
/// function that performs them and describes each reply as text.
fn script(seed: u64, length: usize) -> String {
    let mut random = Seeded(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1);
    let texts = ["", "one", "é → ∀", "two\nlines\n"];
    let mut lines = Vec::new();
    for i in 0..length {
        let path = random.below(PATHS.len());
        let writable = PATHS[path].1;
        let call = match random.below(4) {
            0 => format!("describe (Files.read p{path}) (t => t)"),
            1 if writable => {
                let t = texts[random.below(texts.len())].replace('\n', "\\n");
                format!("describe (Files.write (p{path}, \"{t}\")) (u => \"\")")
            }
            1 | 2 => format!("describe (Files.list p{path}) entries"),
            _ => format!("describe (Files.info p{path}) info"),
        };
        lines.push(format!("  let r{i} := \"${{p{path}}}: \" ++ {call}"));
    }
    let names: Vec<String> = (0..length).map(|i| format!("r{i}")).collect();
    lines.push(format!("  [{}]", names.join(", ")));
    lines.join("\n")
}

/// A program that runs [`script`] on the real disk, or, with the argument
/// `model`, on `Files.simulate`'s disk holding [`START`].
fn conformance_program(seed: u64, length: usize) -> String {
    let start: Vec<String> = START
        .iter()
        .map(|(path, contents)| format!("(\"{path}\".toPath, \"{contents}\")"))
        .collect();
    format!(
        r#"import Std (Disk, Entry, FileError, FileInfo, FileKind, Files, IO, List, Nat, Pair, Path, Result, Text)
import Std.FileKind (File, Folder, Other)

def kindName: (kind: FileKind) → Text
  | File => "file"
  | Folder => "folder"
  | Other => "other"

def entries (es: List Entry): Text := es.map (e => "${{e.name}} ${{kindName e.kind}}") |> .joinWith ", "

def info (i: FileInfo): Text := "${{kindName i.kind}} ${{i.size}}"

def describe (result: Result a FileError) (show: a → Text): Text := match result with
  | Ok x => "ok ${{show x}}"
  | Err error => "error ${{error}}"

{}

def script(): {{Files}} (List Text) :=
{}

def start: Disk := Disk.fromList [{}]

def main(): {{Files, IO}} () :=
  let lines := if IO.args() == ["model"] then (Files.simulate start script).snd else script()
  lines.forEach IO.print
"#,
        PATHS
            .iter()
            .enumerate()
            .map(|(i, (path, _))| format!("def p{i}: Path := {path}"))
            .collect::<Vec<_>>()
            .join("\n"),
        script(seed, length),
        start.join(", ")
    )
}

/// A folder holding [`START`].
fn start_folder(name: &str) -> PathBuf {
    let dir = work_dir(name);
    for (path, contents) in START {
        let file = dir.join(path);
        std::fs::create_dir_all(file.parent().expect("in a folder")).expect("make the folder");
        std::fs::write(file, contents).expect("write the file");
    }
    dir
}

/// Random scripts of operations give the same replies on the real disk, on
/// each runner, as on `Files.simulate`'s: the test that ties the proofs
/// about the model to the host (§3).
#[test]
fn files_scripts_agree_with_the_model_on_each_runner() {
    let sources = work_dir("conformance-sources");
    let mut runners: Vec<&[&str]> = vec![&[], &["--reference"]];
    if cfg!(feature = "native") {
        runners.push(&["--native"]);
    }
    for seed in 1..=4 {
        let source = sources.join(format!("script{seed}.sw"));
        std::fs::write(&source, conformance_program(seed, 24)).expect("write the program");
        let model = run(&work_dir("conformance-model"), &[], &source, &["model"]);
        assert!(
            model.status.success(),
            "the model's run failed: {}",
            text(&model.stderr)
        );
        let replies = text(&model.stdout);
        assert_eq!(replies.lines().count(), 24, "{replies}");
        assert!(
            replies.contains(": ok ") && replies.contains(": error "),
            "a script with successes and failures: {replies}"
        );
        for flags in &runners {
            let dir = start_folder(&format!("conformance-{seed}"));
            let real = run(&dir, flags, &source, &[]);
            assert!(
                real.status.success(),
                "{flags:?} failed: {}",
                text(&real.stderr)
            );
            // A path with `..` is followed by the host and refused by the
            // model: those replies aren't compared.
            let compared = |out: &str| -> Vec<String> { out.lines().map(str::to_string).collect() };
            let (real, model) = (compared(&text(&real.stdout)), compared(&replies));
            assert_eq!(real.len(), model.len(), "seed {seed}, {flags:?}");
            for (real, model) in real.iter().zip(&model) {
                if !model.contains(NO_CLIMBING) {
                    assert_eq!(
                        real, model,
                        "seed {seed}, {flags:?}: the real disk and the model differ"
                    );
                }
            }
        }
    }
}

/// Each kind of error on the real disk, from a program, with the message
/// `FileError.show` gives; and `IO.printError` writes to standard error.
#[test]
fn files_errors_are_values_and_print_error_writes_to_standard_error() {
    let dir = work_dir("errors");
    std::fs::write(dir.join("bytes.bin"), [0x66, 0xff]).expect("write");
    std::fs::create_dir(dir.join("folder")).expect("make the folder");
    std::fs::write(dir.join("plain.txt"), "plain").expect("write");
    let source = work_dir("errors-source").join("errors.sw");
    std::fs::write(
        &source,
        r#"import Std (FileError, Files, IO, Path, Result, Text)

def say (result: Result a FileError): {IO} () := match result with
  | Ok x => IO.print "ok"
  | Err error => IO.printError "${error}"

def main(): {Files, IO} () :=
  say (Files.read "missing.txt".toPath)
  say (Files.read "folder".toPath)
  say (Files.list "plain.txt".toPath)
  say (Files.read "plain.txt/inside".toPath)
  say (Files.read "bytes.bin".toPath)
  say (Files.write ("plain.txt".toPath, "replaced"))
"#,
    )
    .expect("write the program");
    let ran = run(&dir, &[], &source, &[]);
    assert!(ran.status.success(), "{}", text(&ran.stderr));
    assert_eq!(text(&ran.stdout), "ok\n");
    assert_eq!(
        text(&ran.stderr),
        "missing.txt: no such file or folder\n\
         folder: is a folder, not a file\n\
         plain.txt: is a file, not a folder\n\
         plain.txt/inside: is a file, not a folder\n\
         bytes.bin: isn't UTF-8 text\n"
    );
    assert_eq!(
        std::fs::read_to_string(dir.join("plain.txt")).expect("read"),
        "replaced"
    );
}

/// The program the invariant test checks: `main` overwrites its own source
/// and writes a marker file, and a test runs the same code, handled by
/// `Files.simulate`.
const VANDAL: &str = r#"import Std (Disk, Files, IO, Pair, Path, Result, Text)

def vandalise(): {Files} () :=
  Files.write ("vandal.sw".toPath, "gone")
  Files.write ("marker.txt".toPath, "here")
  ()

def main(): {Files, IO} () := vandalise()

test "vandalise writes the marker on a pretend disk" :=
  (Files.simulate Disk.empty vandalise).fst.read "marker.txt".toPath == Ok "here"
"#;

/// Checking and testing a program never perform its file operations
/// (§2.4): after `check` and `test` of a `main` that overwrites its own
/// source, the source is as it was and there's no marker. Running it does
/// both, which shows the program would have.
#[test]
fn checking_and_testing_never_touch_files() {
    let dir = work_dir("invariant");
    let source = dir.join("vandal.sw");
    std::fs::write(&source, VANDAL).expect("write the program");
    for subcommand in ["check", "test"] {
        let mut command = common::cli_plain(subcommand);
        command.args(["--cache-dir", CACHE]).arg("vandal.sw");
        let done = output(command, &dir);
        assert!(
            done.status.success(),
            "{subcommand}: {}{}",
            text(&done.stdout),
            text(&done.stderr)
        );
        assert_eq!(
            std::fs::read_to_string(&source).expect("read"),
            VANDAL,
            "{subcommand} changed the source"
        );
        assert!(
            !dir.join("marker.txt").exists(),
            "{subcommand} wrote the marker"
        );
    }
    let ran = run(&dir, &[], &source, &[]);
    assert!(ran.status.success(), "{}", text(&ran.stderr));
    assert_eq!(std::fs::read_to_string(&source).expect("read"), "gone");
    assert!(dir.join("marker.txt").exists());
}

/// `--js` can't perform `Files` yet: refused before anything runs.
#[test]
fn files_under_js_is_refused() {
    let dir = work_dir("js");
    let source = dir.join("vandal.sw");
    std::fs::write(&source, VANDAL).expect("write the program");
    let ran = run(&dir, &["--js"], &source, &[]);
    assert!(!ran.status.success());
    assert!(
        text(&ran.stderr).contains("E-JS-FILES"),
        "{}",
        text(&ran.stderr)
    );
    assert_eq!(std::fs::read_to_string(&source).expect("read"), VANDAL);
}

/// A `main` with every ability the runner performs: `Files` and `IO`, then
/// `Fail` from inside a `Partial` loop. Each operation must reach its own
/// ability through the row's layout (`MainRow::layout`).
pub const EVERY_ABILITY: &str = r#"import Std (Fail, FileError, Files, IO, Nat, Path, Result, Text)
import Std.Fail (fail)

def countdown (n: Nat): {Files, IO, Fail, Partial} () :=
  if n == 0 then fail "lift-off failed"
  else
    Files.write ("count.txt".toPath, "${n}")
    countdown (n - 1)

def main(): {Files, IO, Fail, Partial} () :=
  Files.write ("start.txt".toPath, "go")
  IO.print (Files.read "start.txt".toPath |> .getOrElse "?")
  IO.printError "counting"
  countdown 3
"#;

#[test]
fn a_main_with_files_io_fail_and_partial_runs_on_each_runner() {
    let source = work_dir("every-source").join("every.sw");
    std::fs::write(&source, EVERY_ABILITY).expect("write the program");
    let mut runners: Vec<&[&str]> = vec![&[], &["--reference"]];
    if cfg!(feature = "native") {
        runners.push(&["--native"]);
    }
    for flags in runners {
        let dir = work_dir("every");
        let ran = run(&dir, flags, &source, &[]);
        assert_eq!(
            ran.status.code(),
            Some(1),
            "{flags:?}: {}",
            text(&ran.stderr)
        );
        assert_eq!(text(&ran.stdout), "go\n", "{flags:?}");
        assert_eq!(
            text(&ran.stderr),
            "counting\nerror: lift-off failed\n",
            "{flags:?}"
        );
        assert_eq!(
            std::fs::read_to_string(dir.join("count.txt")).expect("written"),
            "1",
            "{flags:?}"
        );
    }
}
