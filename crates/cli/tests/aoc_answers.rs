//! Every solved Advent of Code day, run on the real puzzle input (committed,
//! in `aoc/inputs/YYYY/`), must print the known answers. A new day adds one
//! test here, and its answers to [`ANSWERS`].

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

/// Each day's answers: the year, the day, part 1 and part 2.
const ANSWERS: &[(&str, &str, &str, &str)] = &[
    ("2024", "01", "2066446", "24931009"),
    ("2024", "02", "534", "577"),
    ("2024", "03", "174960292", "56275602"),
    ("2024", "04", "2524", "1873"),
    ("2024", "05", "4569", "6456"),
    ("2024", "06", "4967", "1789"),
    ("2024", "07", "66343330034722", "637696070419031"),
    ("2024", "08", "344", "1182"),
    ("2024", "09", "6242766523059", "6272188244509"),
    ("2024", "10", "461", "875"),
    ("2025", "01", "1076", "6379"),
    ("2025", "02", "16793817782", "27469417404"),
    ("2025", "03", "17263", "170731717900423"),
    ("2025", "04", "1397", "8758"),
    ("2025", "05", "525", "333892124923577"),
    ("2025", "06", "4722948564882", "9581313737063"),
    ("2025", "07", "1594", "15650261281478"),
    ("2025", "08", "42315", "8079278220"),
    ("2025", "09", "4756718172", "1665679194"),
];

/// Spawns `command` while holding [`SPAWN`].
fn spawn(command: &mut Command) -> Child {
    let _guard = SPAWN.lock().unwrap_or_else(|e| e.into_inner());
    command.spawn().expect("start stitchwort")
}

fn aoc_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc")
}

/// Runs day `day` of `year` on its real input, with the cache arguments
/// `cache`: it must print exactly the known answers.
fn check_with(year: &str, day: &str, cache: &[&str]) {
    let (_, _, part1, part2) = ANSWERS
        .iter()
        .find(|(y, d, _, _)| *y == year && *d == day)
        .expect("the day's answers");
    let dir = aoc_dir();
    let input = std::fs::File::open(dir.join(format!("inputs/{year}/day{day}.txt")))
        .expect("open the puzzle input");
    let output = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .arg("run")
            .args(cache)
            .arg(format!("Aoc.Year{year}.Day{day}.main"))
            .current_dir(&dir)
            .stdin(Stdio::from(input))
            .stdout(Stdio::piped())
            .stderr(Stdio::piped()),
    )
    .wait_with_output()
    .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{year} day {day} failed:\n{stderr}"
    );
    let stdout = String::from_utf8(output.stdout).expect("output is UTF-8");
    assert_eq!(
        stdout,
        format!("Part 1: {part1}\nPart 2: {part2}\n"),
        "{year} day {day}:\n{stderr}"
    );
}

fn check(year: &str, day: &str) {
    check_with(year, day, &["--no-cache"]);
}

#[test]
fn year2024_day01() {
    check("2024", "01");
}

#[test]
fn year2024_day02() {
    check("2024", "02");
}

#[test]
fn year2024_day03() {
    check("2024", "03");
}

#[test]
fn year2024_day04() {
    check("2024", "04");
}

#[test]
fn year2024_day05() {
    check("2024", "05");
}

#[test]
fn year2024_day06() {
    check("2024", "06");
}

#[test]
fn year2024_day07() {
    check("2024", "07");
}

#[test]
fn year2024_day08() {
    check("2024", "08");
}

#[test]
fn year2024_day09() {
    check("2024", "09");
}

#[test]
fn year2024_day10() {
    check("2024", "10");
}

#[test]
fn year2025_day01() {
    check("2025", "01");
}

#[test]
fn year2025_day02() {
    check("2025", "02");
}

#[test]
fn year2025_day03() {
    check("2025", "03");
}

#[test]
fn year2025_day04() {
    check("2025", "04");
}

#[test]
fn year2025_day05() {
    check("2025", "05");
}

#[test]
fn year2025_day06() {
    check("2025", "06");
}

#[test]
fn year2025_day07() {
    check("2025", "07");
}

#[test]
fn year2025_day08() {
    check("2025", "08");
}

#[test]
fn year2025_day09() {
    check("2025", "09");
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
    for (year, day, _, _) in ANSWERS {
        check_with(year, day, &["--cache-dir", cache_dir]);
    }
    let _ = std::fs::remove_dir_all(&cache);
}
