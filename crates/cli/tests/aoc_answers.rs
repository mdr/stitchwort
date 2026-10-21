//! Every solved Advent of Code day, run on the real puzzle input (committed,
//! D119), must print the known answers. A new day adds one test here.

use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::sync::Mutex;

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

/// Runs day `day` on its real input: it must print exactly the known answers.
fn check(day: &str, part1: &str, part2: &str) {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let input = std::fs::File::open(dir.join(format!("inputs/day{day}.txt")))
        .expect("open the puzzle input");
    let output = spawn(
        Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .arg("run")
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

#[test]
fn day01() {
    check("01", "1076", "6379");
}

#[test]
fn day02() {
    check("02", "16793817782", "27469417404");
}

#[test]
fn day03() {
    check("03", "17263", "170731717900423");
}

#[test]
fn day04() {
    check("04", "1397", "8758");
}

#[test]
fn day05() {
    check("05", "525", "333892124923577");
}

#[test]
fn day06() {
    check("06", "4722948564882", "9581313737063");
}

#[test]
fn day07() {
    check("07", "1594", "15650261281478");
}
