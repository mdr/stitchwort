//! `stitchwort fmt` (docs/proposals/formatter.md §5.1, still the interface), end to end with the
//! built command.

#[path = "../../../fmt/tests/it/support/repo_files.rs"]
mod repo_files;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use stitchwort_fmt::DELIBERATELY_UNFORMATTED;

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

/// A folder walk leaves hidden folders alone, but a hidden folder named
/// itself is still walked.
#[test]
fn a_folder_walk_skips_hidden_folders() {
    let dir = temp("hidden");
    let visible = dir.join("a.sw");
    let hidden = dir.join(".hidden/b.sw");
    std::fs::create_dir_all(hidden.parent().unwrap()).unwrap();
    std::fs::write(&visible, UNFORMATTED).unwrap();
    std::fs::write(&hidden, UNFORMATTED).unwrap();
    let folder = dir.display().to_string();

    let output = stitchwort(&dir, &["fmt", &folder], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{}\n", visible.display()));
    assert_eq!(std::fs::read_to_string(&visible).unwrap(), FORMATTED);
    assert_eq!(std::fs::read_to_string(&hidden).unwrap(), UNFORMATTED);

    let hidden_folder = hidden.parent().unwrap().display().to_string();
    let output = stitchwort(&dir, &["fmt", &hidden_folder], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{}\n", hidden.display()));
    assert_eq!(std::fs::read_to_string(&hidden).unwrap(), FORMATTED);

    let _ = std::fs::remove_dir_all(&dir);
}

/// A link back to a parent folder doesn't send the walk round for ever.
#[cfg(unix)]
#[test]
fn a_folder_walk_does_not_follow_a_symlink_to_a_parent() {
    let dir = temp("symlink");
    let file = dir.join("a.sw");
    std::fs::write(&file, UNFORMATTED).unwrap();
    let child = dir.join("child");
    std::fs::create_dir_all(&child).unwrap();
    std::os::unix::fs::symlink(&dir, child.join("up")).unwrap();
    let folder = dir.display().to_string();

    let check = stitchwort(&dir, &["fmt", "--check", &folder], None);
    assert_eq!(check.status.code(), Some(1), "{check:?}");
    assert_eq!(text(&check), format!("{}\n", file.display()));

    let output = stitchwort(&dir, &["fmt", &folder], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{}\n", file.display()));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), FORMATTED);

    let _ = std::fs::remove_dir_all(&dir);
}

/// A formatted file keeps its permissions, and is replaced rather than
/// rewritten in place.
#[cfg(unix)]
#[test]
fn a_formatted_file_keeps_its_permissions() {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    let dir = temp("permissions");
    let file = dir.join("f.sw");
    let path = file.display().to_string();
    std::fs::write(&file, UNFORMATTED).unwrap();
    std::fs::set_permissions(&file, std::fs::Permissions::from_mode(0o751)).unwrap();
    let before = std::fs::metadata(&file).unwrap().ino();

    let output = stitchwort(&dir, &["fmt", &path], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{path}\n"));
    assert_eq!(std::fs::read_to_string(&file).unwrap(), FORMATTED);
    let after = std::fs::metadata(&file).unwrap();
    assert_eq!(after.permissions().mode() & 0o777, 0o751);
    assert_ne!(
        after.ino(),
        before,
        "the file should be replaced, not rewritten"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A folder walk skips the paths the repository keeps as written (D1019),
/// saying how many it skipped; a file named explicitly is still formatted.
#[test]
fn a_folder_walk_skips_deliberately_unformatted_files() {
    let dir = temp("excluded");
    std::fs::create_dir_all(dir.join(".git")).unwrap();
    let excluded = dir.join("examples/reject/bad.sw");
    let formatted = dir.join("src/ok.sw");
    std::fs::create_dir_all(excluded.parent().unwrap()).unwrap();
    std::fs::create_dir_all(formatted.parent().unwrap()).unwrap();
    std::fs::write(&excluded, UNFORMATTED).unwrap();
    std::fs::write(&formatted, UNFORMATTED).unwrap();
    let folder = dir.display().to_string();

    let output = stitchwort(&dir, &["fmt", "--check", &folder], None);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(text(&output), format!("{}\n", formatted.display()));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(&format!(
            "1 file skipped as deliberately unformatted\n{}\n",
            excluded.display()
        )),
        "{stderr}"
    );
    assert_eq!(std::fs::read_to_string(&excluded).unwrap(), UNFORMATTED);
    assert_eq!(std::fs::read_to_string(&formatted).unwrap(), UNFORMATTED);

    // A file named explicitly is formatted: the user asked for it.
    let path = excluded.display().to_string();
    let output = stitchwort(&dir, &["fmt", &path], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), format!("{path}\n"));
    assert_eq!(std::fs::read_to_string(&excluded).unwrap(), FORMATTED);

    let _ = std::fs::remove_dir_all(&dir);
}

/// `--check` on a file named explicitly skips the paths the repository keeps
/// as written too, so a caller (the pre-commit hook) needn't filter; the skip
/// is reported, and without `--check` the named file is still formatted.
#[test]
fn check_skips_a_named_deliberately_unformatted_file() {
    let dir = temp("named-excluded");
    std::fs::create_dir_all(dir.join(".git")).unwrap();
    let excluded = dir.join("examples/reject/bad.sw");
    let formatted = dir.join("src/ok.sw");
    std::fs::create_dir_all(excluded.parent().unwrap()).unwrap();
    std::fs::create_dir_all(formatted.parent().unwrap()).unwrap();
    std::fs::write(&excluded, UNFORMATTED).unwrap();
    std::fs::write(&formatted, UNFORMATTED).unwrap();
    let excluded_path = excluded.display().to_string();
    let formatted_path = formatted.display().to_string();

    let output = stitchwort(&dir, &["fmt", "--check", &excluded_path], None);
    assert_eq!(output.status.code(), Some(0), "{output:?}");
    assert_eq!(text(&output), "");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(&format!(
            "1 file skipped as deliberately unformatted\n{}\n",
            excluded.display()
        )),
        "{stderr}"
    );

    // Alongside a file that does need formatting, only that one is listed.
    let output = stitchwort(
        &dir,
        &["fmt", "--check", &excluded_path, &formatted_path],
        None,
    );
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(text(&output), format!("{formatted_path}\n"));
    assert_eq!(std::fs::read_to_string(&excluded).unwrap(), UNFORMATTED);

    let _ = std::fs::remove_dir_all(&dir);
}

/// The repository's own `.sw` sources are formatted: every tracked one
/// outside the paths kept as written. The list is filtered here rather than
/// left to `fmt --check`, which finds those paths by their `.git` root and so
/// can't in the Nix build's source copy.
#[test]
fn the_repository_sources_are_formatted() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let files: Vec<String> = repo_files::repo_files(&root, &[".sw"])
        .into_iter()
        .filter(|path| {
            !DELIBERATELY_UNFORMATTED
                .iter()
                .any(|excluded| path.starts_with(excluded))
        })
        .collect();
    assert!(files.len() > 300, "found only {} files", files.len());
    let mut args = vec!["fmt", "--check"];
    args.extend(files.iter().map(String::as_str));
    let output = stitchwort(&root, &args, None);
    // `--check` lists what would change.
    let listed = text(&output);
    assert!(
        listed.is_empty() && output.status.code().is_some_and(|code| code <= 1),
        "unformatted (run `stitchwort fmt` on them):\n{listed}{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
