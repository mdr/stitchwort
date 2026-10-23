//! `stitchwort fmt` (docs/proposals/formatter.md §5.1), end to end with the
//! built command.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

fn stitchwort(cwd: &Path, args: &[&str], input: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(args).current_dir(cwd);
    match input {
        Some(input) => {
            command
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped());
            let mut child = command.spawn().expect("run stitchwort");
            child
                .stdin
                .take()
                .expect("standard input")
                .write_all(input.as_bytes())
                .expect("write standard input");
            child.wait_with_output().expect("wait for stitchwort")
        }
        None => command
            .stdin(Stdio::null())
            .output()
            .expect("run stitchwort"),
    }
}

/// A fresh temporary folder for `name`.
fn temp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-fmt-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn text(output: &Output) -> String {
    String::from_utf8(output.stdout.clone()).unwrap()
}

const UNFORMATTED: &str = "def f (x : Nat) : Nat:=x+1\n";
const FORMATTED: &str = "def f (x: Nat): Nat := x + 1\n";

/// A file is formatted in place, its path printed, and a second run changes
/// nothing.
#[test]
fn formats_a_file_in_place() {
    let dir = temp("in-place");
    let file = dir.join("f.sw");
    std::fs::write(&file, UNFORMATTED).unwrap();
    let path = file.display().to_string();

    let first = stitchwort(&dir, &["fmt", &path], None);
    assert_eq!(first.status.code(), Some(0), "{first:?}");
    assert_eq!(text(&first), format!("{path}\n"));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), FORMATTED);

    let second = stitchwort(&dir, &["fmt", &path], None);
    assert_eq!(second.status.code(), Some(0), "{second:?}");
    assert_eq!(text(&second), "");

    let _ = std::fs::remove_dir_all(&dir);
}

/// `--check` lists what would change and exits 1, writing nothing; it says
/// nothing and exits 0 for a formatted file.
#[test]
fn check_lists_files_and_exits_one() {
    let dir = temp("check");
    let file = dir.join("f.sw");
    let path = file.display().to_string();
    std::fs::write(&file, UNFORMATTED).unwrap();

    let unfmt = stitchwort(&dir, &["fmt", "--check", &path], None);
    assert_eq!(unfmt.status.code(), Some(1), "{unfmt:?}");
    assert_eq!(text(&unfmt), format!("{path}\n"));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), UNFORMATTED);

    std::fs::write(&file, FORMATTED).unwrap();
    let fmt = stitchwort(&dir, &["fmt", "--check", &path], None);
    assert_eq!(fmt.status.code(), Some(0), "{fmt:?}");
    assert_eq!(text(&fmt), "");

    let _ = std::fs::remove_dir_all(&dir);
}

/// A file with a syntax error is refused: exit 2, and it is left unchanged.
#[test]
fn refuses_a_file_with_a_syntax_error() {
    let dir = temp("refused");
    let file = dir.join("bad.sw");
    let path = file.display().to_string();
    let broken = "def f :=\n";
    std::fs::write(&file, broken).unwrap();

    let output = stitchwort(&dir, &["fmt", &path], None);
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(text(&output), "");
    assert!(!String::from_utf8_lossy(&output.stderr).is_empty());
    assert_eq!(std::fs::read_to_string(&file).unwrap(), broken);

    let _ = std::fs::remove_dir_all(&dir);
}

/// `-` reads standard input and writes the formatted text.
#[test]
fn formats_standard_input() {
    let dir = temp("stdin");
    let output = stitchwort(&dir, &["fmt", "-"], Some(UNFORMATTED));
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), FORMATTED);
    // Already formatted text comes back whole, not as nothing.
    let output = stitchwort(&dir, &["fmt", "-"], Some(FORMATTED));
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), FORMATTED);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A folder is searched recursively; only the unformatted file is printed
/// and changed.
#[test]
fn formats_a_folder() {
    let dir = temp("folder");
    let formatted = dir.join("a.sw");
    let unformatted = dir.join("b.sw");
    std::fs::write(&formatted, FORMATTED).unwrap();
    std::fs::write(&unformatted, UNFORMATTED).unwrap();
    let folder = dir.display().to_string();

    let output = stitchwort(&dir, &["fmt", &folder], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{}\n", unformatted.display()));
    assert_eq!(std::fs::read_to_string(&formatted).unwrap(), FORMATTED);
    assert_eq!(std::fs::read_to_string(&unformatted).unwrap(), FORMATTED);

    let _ = std::fs::remove_dir_all(&dir);
}
