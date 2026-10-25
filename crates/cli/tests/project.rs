//! Projects on the command line, end to end with the built command
//! (docs/proposals/multi-file.md §7, §12). Each test writes its own project
//! to a temporary folder.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

/// The repository's own folder isn't a project, so running `stitchwort`
/// anywhere in it, an example included, never finds an accidental one
/// (§4.3).
#[test]
fn the_repository_root_is_not_a_project() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../stitchwort.yaml");
    assert!(!root.exists(), "{} must not exist", root.display());
}

/// A project folder named `proj` in a fresh temporary folder for `test`.
fn project(test: &str, files: &[(&str, &str)]) -> PathBuf {
    let base =
        std::env::temp_dir().join(format!("stitchwort-project-{}-{test}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let dir = base.join("proj");
    for (path, text) in files {
        let full = dir.join(path);
        std::fs::create_dir_all(full.parent().unwrap()).unwrap();
        std::fs::write(full, text).unwrap();
    }
    dir
}

/// `args`, with `--no-cache` for a command that checks: tests don't use the
/// check cache (docs/proposals/check-cache.md, D286) unless they say so.
fn without_caches<'a>(args: &[&'a str]) -> Vec<&'a str> {
    let mut args = args.to_vec();
    let checks = matches!(
        args.first(),
        Some(&("check" | "test" | "run" | "eval" | "build"))
    );
    if checks && !args.contains(&"--no-cache") {
        args.push("--no-cache");
    }
    args
}

/// Runs `stitchwort args` in `cwd`, without the caches.
fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    with_caches(cwd, &without_caches(args))
}

/// Runs `stitchwort args` in `cwd`, with the caches if it checks.
fn with_caches(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

fn out(output: &Output) -> &str {
    std::str::from_utf8(&output.stdout).unwrap()
}

fn err(output: &Output) -> &str {
    std::str::from_utf8(&output.stderr).unwrap()
}

fn succeeds(cwd: &Path, args: &[&str]) -> String {
    let output = stitchwort(cwd, args);
    assert!(output.status.success(), "{args:?}:\n{}", err(&output));
    out(&output).to_string()
}

fn fails(cwd: &Path, args: &[&str], code: &str) -> String {
    let output = stitchwort(cwd, args);
    assert_eq!(output.status.code(), Some(1), "{args:?}:\n{}", err(&output));
    assert!(
        err(&output).contains(&format!("[{code}]")),
        "{args:?}: expected {code}:\n{}",
        err(&output)
    );
    err(&output).to_string()
}

const LIB: &str = "namespace Lib

def greet(): {IO} () := IO.print \"lib\"

def answer: Nat := 2

test \"lib\" := 1 + 1 == 2
";

const DAY: &str = "namespace Day

import Lib (greet)

def main(): {IO} () :=
  IO.print \"day\"
  greet()

def quiet(): () := ()

def maybe(): {Partial} () := ()

def bad(n: Nat): Nat := n

test \"day\" := Lib.answer == 2
";

const OTHER: &str = "namespace Other\n\ndef x: Nat := 1\n\ntest \"x\" := x == 1\n";
const BROKEN: &str = "namespace Other\n\ndef x: Nat := True\n";
const SOLO: &str =
    "namespace Solo\n\ndef main(): {IO} () := IO.print \"solo\"\n\ntest \"solo\" := True\n";

fn files<'a>(day: &'a str, other: &'a str) -> Vec<(&'a str, &'a str)> {
    vec![
        ("stitchwort.yaml", ""),
        ("src/lib.sw", LIB),
        ("src/day.sw", day),
        ("src/other.sw", other),
        ("src/solo.sw", SOLO),
    ]
}

fn standard(test: &str) -> PathBuf {
    project(test, &files(DAY, OTHER))
}

#[test]
fn run_by_name() {
    let dir = standard("run_by_name");
    assert_eq!(succeeds(&dir, &["run", "Day.main"]), "day\nlib\n");
    // From a folder inside the project, and with the flag from outside.
    let sub = dir.join("src");
    assert_eq!(succeeds(&sub, &["run", "Day.main"]), "day\nlib\n");
    let outside = dir.parent().unwrap();
    assert_eq!(
        succeeds(outside, &["run", "Day.main", "--project", "proj"]),
        "day\nlib\n"
    );
}

#[test]
fn run_a_pure_function() {
    assert_eq!(succeeds(&standard("run_pure"), &["run", "Day.quiet"]), "");
}

#[test]
fn run_a_partial_function() {
    assert_eq!(
        succeeds(&standard("run_partial"), &["run", "Day.maybe"]),
        ""
    );
}

#[test]
fn run_the_wrong_type() {
    let message = fails(&standard("run_wrong"), &["run", "Day.bad"], "E-RUN-TYPE");
    assert!(message.contains("`Day.bad` can't be run"), "{message}");
    assert!(message.contains("IO, Fail and Partial"), "{message}");
}

#[test]
fn run_an_unknown_name() {
    let dir = standard("run_unknown");
    let message = fails(&dir, &["run", "Day.mian"], "E-RUN-UNKNOWN");
    assert!(message.contains("did you mean `Day.main`?"), "{message}");
    let message = fails(&dir, &["run", "Dya.main"], "E-RUN-UNKNOWN");
    assert!(message.contains("did you mean `Day.main`?"), "{message}");
    let message = fails(&dir, &["run", "Day"], "E-RUN-UNKNOWN");
    assert!(message.contains("`Day.main`"), "{message}");
}

#[test]
fn an_unrelated_broken_namespace_doesnt_stop_run() {
    let dir = project("unrelated_broken", &files(DAY, BROKEN));
    assert_eq!(succeeds(&dir, &["run", "Day.main"]), "day\nlib\n");
    fails(&dir, &["check"], "E-TYPE-MISMATCH");
}

#[test]
fn run_a_project_file_by_path() {
    let dir = standard("run_file");
    assert_eq!(succeeds(&dir, &["run", "src/solo.sw"]), "solo\n");
    assert_eq!(succeeds(&dir, &["run", "Solo.main"]), "solo\n");
}

#[test]
fn a_project_file_importing_the_project_is_file_mode() {
    let dir = standard("file_mode");
    let message = fails(&dir, &["run", "src/day.sw"], "E-FILE-MODE");
    assert!(message.contains("is run as a single file"), "{message}");
    assert!(message.contains("`stitchwort run Day.main`"), "{message}");
    let message = fails(&dir, &["check", "src/day.sw"], "E-FILE-MODE");
    assert!(message.contains("is checked as a single file"), "{message}");
    assert!(message.contains("`stitchwort check Day`"), "{message}");
}

#[test]
fn check_the_whole_project() {
    let good = standard("check_all");
    succeeds(&good, &["check"]);
    let broken = project("check_all_broken", &files(DAY, BROKEN));
    fails(&broken, &["check"], "E-TYPE-MISMATCH");
}

#[test]
fn check_one_namespace() {
    let dir = project("check_one", &files(DAY, BROKEN));
    succeeds(&dir, &["check", "Day"]);
}

#[test]
fn check_an_unknown_namespace() {
    let message = fails(
        &standard("check_unknown"),
        &["check", "Dya"],
        "E-NAMESPACE-UNKNOWN",
    );
    assert!(message.contains("did you mean `Day`?"), "{message}");
}

#[test]
fn check_mixed_targets() {
    let output = stitchwort(&standard("check_mixed"), &["check", "Day", "src/lib.sw"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        err(&output),
        "error: give either files or names in the project, not both\n"
    );
}

#[test]
fn no_project_found() {
    let empty = std::env::temp_dir().join(format!("stitchwort-noproject-{}", std::process::id()));
    std::fs::create_dir_all(&empty).unwrap();
    let output = stitchwort(&empty, &["check"]);
    assert_eq!(output.status.code(), Some(1));
    let message = err(&output);
    assert!(
        message.contains("error: there's no stitchwort.yaml in")
            && message.contains("or any folder above it"),
        "{message}"
    );
    assert!(
        message.contains(
            "note: to check a single file, pass its path, as in `stitchwort check hello.sw`"
        ),
        "{message}"
    );
    let output = stitchwort(&empty, &["run", "Day.main", "--project", "nowhere"]);
    assert!(err(&output).contains("error: there's no stitchwort.yaml in nowhere"));
}

#[test]
fn the_project_flag() {
    let dir = standard("flag");
    let outside = dir.parent().unwrap();
    succeeds(outside, &["check", "--project", "proj"]);
    let output = stitchwort(outside, &["check"]);
    assert!(!output.status.success());
}

#[test]
fn test_a_namespace_runs_its_dependencies_tests_grouped() {
    let dir = standard("test_grouped");
    let stdout = succeeds(&dir, &["test", "Day", "--no-cache"]);
    insta::assert_snapshot!("test_a_namespace_grouped", stdout);
}

#[test]
fn the_cache_is_in_the_project_folder() {
    let dir = standard("cache");
    let sub = dir.join("src");
    let output = with_caches(&sub, &["test"]);
    assert!(output.status.success(), "{}", err(&output));
    let cache = dir.join(".stitchwort/cache/tests");
    assert!(std::fs::read_dir(&cache).unwrap().count() > 0);
    // The check cache beside it (docs/proposals/check-cache.md, D281).
    assert!(dir.join(".stitchwort/cache/check/header").is_file());
    assert_eq!(
        std::fs::read_to_string(dir.join(".stitchwort/.gitignore")).unwrap(),
        "*\n"
    );
    assert!(!sub.join(".stitchwort").exists());
    let again = out(&with_caches(&sub, &["test"])).to_string();
    assert!(again.contains("(4 from the cache)"), "{again}");
    assert!(!again.contains(" ran"), "{again}");
}

const EXPORTS_LIB: &str = "namespace Lib

export def solve (n: Nat): Nat := n + 2

def greet(): {IO} () := IO.print \"lib\"
";

const EXPORTS_DAY: &str = "namespace Day

import Lib (greet)

export def solve (n: Nat): Nat := n + 1

def main(): {IO} () :=
  IO.print \"day\"
  greet()
";

fn exports_project(test: &str) -> PathBuf {
    project(
        test,
        &[
            ("stitchwort.yaml", ""),
            ("src/lib.sw", EXPORTS_LIB),
            ("src/day.sw", EXPORTS_DAY),
        ],
    )
}

/// What `solve(1n)` prints from `{namespace}.js` in `out`, under Node.
fn solve_in(out_dir: &Path, namespace: &str) -> String {
    let script =
        format!("import {{ solve }} from './{namespace}.js'; console.log(solve(1n).toString())");
    let output = Command::new("node")
        .current_dir(out_dir)
        .args(["--input-type=module", "-e", &script])
        .output()
        .expect("run node (it's in the nix dev shell)");
    assert!(output.status.success(), "{}", err(&output));
    out(&output).to_string()
}

/// Two namespaces export `solve`: building one gives that one's, and the
/// other's doesn't clash with it.
#[test]
fn build_one_namespace() {
    let dir = exports_project("build_one");
    let built = succeeds(&dir, &["build", "--js", "Day", "-o", "out"]);
    assert!(
        built.contains("Day.js") && built.contains("Day.d.ts"),
        "{built}"
    );
    let declarations = std::fs::read_to_string(dir.join("out/Day.d.ts")).unwrap();
    assert_eq!(
        declarations.matches("function solve(").count(),
        1,
        "{declarations}"
    );
    assert_eq!(solve_in(&dir.join("out"), "Day"), "2\n");
    succeeds(&dir, &["build", "--js", "Lib", "-o", "out"]);
    assert_eq!(solve_in(&dir.join("out"), "Lib"), "3\n");
    fails(&dir, &["build", "--js", "Dya"], "E-NAMESPACE-UNKNOWN");
}

#[test]
fn run_js_across_namespaces() {
    let dir = exports_project("run_js");
    assert_eq!(succeeds(&dir, &["run", "--js", "Day.main"]), "day\nlib\n");
    assert_eq!(succeeds(&dir, &["run", "Day.main"]), "day\nlib\n");
}

#[test]
fn file_mode_reports_the_import_once() {
    let dir = standard("file_mode_once");
    let message = fails(&dir, &["check", "src/day.sw"], "E-FILE-MODE");
    assert!(!message.contains("E-UNKNOWN-NAME"), "{message}");
}

#[test]
fn a_typo_in_the_files_own_namespace_is_not_file_mode() {
    let typo = "namespace Day\n\ndef x: Nat := 1\n\ndef y: Nat := Day.xx\n";
    let dir = project(
        "own_namespace_typo",
        &[
            ("stitchwort.yaml", ""),
            ("src/lib.sw", LIB),
            ("src/day.sw", typo),
        ],
    );
    let message = fails(&dir, &["check", "src/day.sw"], "E-UNKNOWN-NAME");
    assert!(!message.contains("E-FILE-MODE"), "{message}");
}

#[test]
fn a_qualified_declaration_in_the_files_own_namespace_is_refused_in_a_single_file() {
    let dir = project(
        "own_namespace_declaration",
        &[("day.sw", "namespace Day\n\ndef Day.f: Nat := 1\n")],
    );
    fails(&dir, &["check", "day.sw"], "E-FOREIGN-NAMESPACE");
}

#[test]
fn main_is_not_a_namespace_name() {
    let dir = project(
        "main_reserved",
        &[
            ("stitchwort.yaml", ""),
            ("src/m.sw", "namespace Main\n\ndef x: Nat := 1\n"),
        ],
    );
    fails(&dir, &["check"], "E-NAMESPACE-RESERVED");
}

#[test]
fn a_project_file_importing_everything_from_the_project_is_file_mode() {
    let day = "namespace Day\n\nimport Lib (..)\n\ndef x(): Nat := 1\n";
    let dir = project(
        "file_mode_wildcard",
        &[
            ("stitchwort.yaml", ""),
            ("src/lib.sw", LIB),
            ("src/day.sw", day),
        ],
    );
    let message = fails(&dir, &["check", "src/day.sw"], "E-FILE-MODE");
    assert!(
        message.contains("`Lib` is a namespace of the project"),
        "{message}"
    );
    assert!(!message.contains("E-IMPORT"), "{message}");
}

/// `Alpha` reaches `Zed` only through `import Zed (..)`, which makes the
/// dependency: testing `Alpha` runs `Zed`'s tests too.
#[test]
fn a_wildcard_makes_the_dependency() {
    let dir = project(
        "wildcard_dependency",
        &[
            ("stitchwort.yaml", ""),
            (
                "src/zed.sw",
                include_str!("../../../examples/projects/accept/wildcard-only-edge/src/zed.sw"),
            ),
            (
                "src/alpha.sw",
                include_str!("../../../examples/projects/accept/wildcard-only-edge/src/alpha.sw"),
            ),
        ],
    );
    let stdout = succeeds(&dir, &["test", "Alpha", "--no-cache"]);
    assert!(stdout.contains("zed"), "{stdout}");
    assert!(stdout.contains("client"), "{stdout}");
}

#[test]
fn test_a_namespace_includes_the_namespaces_under_it() {
    let dir = project(
        "test_children",
        &[
            ("stitchwort.yaml", ""),
            ("src/Day.sw", "namespace Day\n\ndef x: Nat := 1\n"),
            (
                "src/Day/Tests.sw",
                "namespace Day.Tests\n\nimport Day (x)\n\ntest \"x\" := x == 1\n",
            ),
            (
                "src/Day/Proofs.sw",
                "namespace Day.Proofs\n\ntest \"p\" := True\n",
            ),
            ("src/Other.sw", "namespace Other\n\ntest \"o\" := True\n"),
        ],
    );
    let stdout = succeeds(&dir, &["test", "Day"]);
    assert!(
        stdout.contains("Day.Tests") && stdout.contains("Day.Proofs"),
        "{stdout}"
    );
    assert!(!stdout.contains("Other"), "{stdout}");
    assert!(stdout.contains("2 test(s): 2 passed"), "{stdout}");
    // A name prefix isn't a parent: `Da` matches nothing.
    let output = stitchwort(&dir, &["test", "Da"]);
    assert_eq!(output.status.code(), Some(1));
}

#[test]
fn test_warns_when_a_target_matches_no_tests() {
    let dir = project(
        "test_none",
        &[
            ("stitchwort.yaml", ""),
            ("src/Bare.sw", "namespace Bare\n\ndef x: Nat := 1\n"),
        ],
    );
    let output = stitchwort(&dir, &["test", "Bare"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        err(&output).contains("warning: no tests matched 'Bare'"),
        "{}",
        err(&output)
    );
}

/// The roguelike's proofs (games/rogue/), with seven holes in `match`
/// branches on `isStairs` and `isWall` added: the goals show the calls as
/// the proofs wrote them, `isStairs state.player = False`, not the dungeon
/// map those read (games/rogue/NOTES.md item 14). The goals were about
/// 20 KB of output before the fix, and are about 4 KB with it.
#[test]
fn rogue_goals_keep_the_dungeon_folded() {
    let rogue = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../games/rogue");
    let dir = project("rogue-goals", &[]);
    copy_tree(&rogue.join("src"), &dir.join("src"));
    std::fs::copy(rogue.join("stitchwort.yaml"), dir.join("stitchwort.yaml")).unwrap();
    std::fs::write(dir.join("src/Rogue/Proofs/Holes.sw"), ROGUE_HOLES).unwrap();
    let output = stitchwort(&dir, &["check", "Rogue.Proofs"]);
    let text = format!("{}{}", out(&output), err(&output));
    assert_eq!(text.matches("[GOAL]").count(), 7, "{text}");
    assert!(
        text.contains("stairs: Rogue.isStairs state.level state.player = False"),
        "{text}"
    );
    assert!(
        text.contains(
            "wall: Rogue.isWall state.level (Rogue.Position.toward state.player direction) = True"
        ),
        "{text}"
    );
    assert!(!text.contains("['#'"), "the map is unfolded:\n{text}");
    assert!(text.len() < 6_000, "{} bytes of goals:\n{text}", text.len());
}

const ROGUE_HOLES: &str = "namespace Rogue.Proofs
import Rogue (..)
import Std (Nat)

theorem stairsHoles (dice: Dice) (state: State):
    (monstersTurn dice state).hitPoints ≤ maxHitPoints :=
  match stairs: isStairs state.level state.player with
    | True => ?
    | False => ?

theorem wallHoles (dice: Dice) (state: State) (direction: Direction):
    (playerMoves dice state direction).hitPoints ≤ maxHitPoints :=
  match found: monsterAt (state.player.toward direction) state.monsters with
    | Some monster => ?
    | None =>
      match wall: isWall state.level (state.player.toward direction) with
        | True => ?
        | False => ?

theorem clearHoles (dice: Dice) (state: State):
    Clear (monstersTurn dice state).player (monstersTurn dice state).monsters :=
  match stairs: isStairs state.level state.player with
    | True => ?
    | False => ?
";

fn copy_tree(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), target).unwrap();
        }
    }
}
