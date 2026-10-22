//! Every solved Advent of Code day, run on the real puzzle input (committed,
//! D119), must print the known answers. A new day adds one test here, and
//! its answers to [`ANSWERS`].

use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::Mutex;

/// Held while creating pipes and spawning children. On macOS, std makes a
/// pipe with `pipe` and then sets close-on-exec on each end in a second step
/// (no `pipe2`; std/src/sys/pipe/unix.rs), so a child spawned by another test
/// thread in between inherits the pipe's ends. That broke
/// `a_write_error_is_an_error`, which needs a pipe with no reader: a child
/// that inherited the read end kept it open, and the write succeeded.
static SPAWN: Mutex<()> = Mutex::new(());

/// Each day's answers: the day, part 1 and part 2.
const ANSWERS: &[(&str, &str, &str)] = &[
    ("01", "1076", "6379"),
    ("02", "16793817782", "27469417404"),
    ("03", "17263", "170731717900423"),
    ("04", "1397", "8758"),
    ("05", "525", "333892124923577"),
    ("06", "4722948564882", "9581313737063"),
    ("07", "1594", "15650261281478"),
    ("08", "42315", "8079278220"),
];

/// Spawns `command` while holding [`SPAWN`].
fn spawn(command: &mut Command) -> Child {
    let _guard = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
    command.spawn().expect("start stitchwort")
}

fn aoc_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc")
}

/// Runs day `day` on its real input, with the cache arguments `cache`: it
/// must print exactly the known answers.
fn check_with(day: &str, cache: &[&str]) {
    let (_, part1, part2) = ANSWERS
        .iter()
        .find(|(d, _, _)| *d == day)
        .expect("the day's answers");
    let dir = aoc_dir();
    let input = std::fs::File::open(dir.join(format!("inputs/day{day}.txt")))
        .expect("open the puzzle input");
    let output = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .arg("run")
            .args(cache)
            .arg(format!("Aoc.Day{day}.main"))
            .current_dir(&dir)
            .stdin(Stdio::from(input))
            .stdout(Stdio::piped())
            .stderr(Stdio::piped()),
    )
    .wait_with_output()
    .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "day {day} failed:\n{stderr}");
    let stdout = String::from_utf8(output.stdout).expect("output is UTF-8");
    assert_eq!(
        stdout,
        format!("Part 1: {part1}\nPart 2: {part2}\n"),
        "day {day}:\n{stderr}"
    );
}

fn check(day: &str) {
    check_with(day, &["--no-cache"]);
}

#[test]
fn day01() {
    check("01");
}

#[test]
fn day02() {
    check("02");
}

#[test]
fn day03() {
    check("03");
}

#[test]
fn day04() {
    check("04");
}

#[test]
fn day05() {
    check("05");
}

#[test]
fn day06() {
    check("06");
}

#[test]
fn day07() {
    check("07");
}

#[test]
fn day08() {
    check("08");
}

/// Each day run from the check cache a whole project `check` wrote, as
/// after checking in the editor (SW-255: `run` found every name of some
/// days defined twice).
#[test]
fn every_day_from_the_whole_projects_cache() {
    let cache = std::env::temp_dir().join(format!(
        "stitchwort-aoc-answers-cache-{}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&cache);
    let cache_dir = cache.to_str().unwrap();
    let output = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--cache-dir", cache_dir])
            .current_dir(aoc_dir())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped()),
    )
    .wait_with_output()
    .expect("run stitchwort");
    assert!(
        output.status.success(),
        "check failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    for (day, _, _) in ANSWERS {
        check_with(day, &["--cache-dir", cache_dir]);
    }
    let _ = std::fs::remove_dir_all(&cache);
}
