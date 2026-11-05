//! The language server's live heap on aoc, measured in one thread
//! and without timing (SW-1179; docs/proposals/elaborator-state.md
//! §4.8.12): a `LiveProject` set up as the server (`crates/lsp`) sets one up,
//! checked to the end, then edited as `lsp.rs`'s `state_edit_loop` edits,
//! with the heap and `JournalStats` after each step. The edit loop samples
//! while the server may still be checking in the background, so its heap
//! depends on how far that check got; this one doesn't.
//!
//! `LIVE_MEM_PROJECT=$PWD/aoc cargo test --release -p stitchwort-cli --test
//! live_memory -- --ignored --nocapture` (about 2.5 minutes on aoc, and the
//! first time a minute more to fill a copy's check cache;
//! `LIVE_MEM_REUSE=1` keeps the copy).

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::rc::Rc;
use std::time::Instant;

use stitchwort_driver::check_cache::CheckCache;
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::{LiveProject, Progress};
use stitchwort_driver::project::DiskFiles;

const STACK: usize = 64 * 1024 * 1024;

fn copy_dir(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).unwrap();
    for entry in std::fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let path = entry.path();
        let target = to.join(entry.file_name());
        if path.is_dir() {
            if entry.file_name() == ".stitchwort" {
                continue;
            }
            copy_dir(&path, &target);
        } else {
            std::fs::copy(&path, &target).unwrap();
        }
    }
}

fn sources(root: &Path) -> BTreeMap<String, String> {
    let mut files = BTreeMap::new();
    let mut dirs = vec![root.join("src")];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "sw") {
                let relative = path.strip_prefix(root).unwrap();
                files.insert(
                    relative.to_string_lossy().to_string(),
                    std::fs::read_to_string(&path).unwrap(),
                );
            }
        }
    }
    files
}

fn mb(bytes: usize) -> f64 {
    bytes as f64 / 1e6
}

fn sample(what: &str, live: &mut LiveProject, t: Instant) {
    let j = live.session.elab.journal_stats();
    eprintln!(
        "live_memory\t{what}\theap {:.1} MB\t{:.1} s\tjournal held {} bytes_held {} open {} entries {}",
        mb(stitchwort_bench::alloc::live()),
        t.elapsed().as_secs_f64(),
        j.held,
        j.bytes_held,
        j.open,
        j.entries
    );
}

/// Steps until the focus is checked (`until_focus`) or everything is,
/// answering as the server does.
fn run(live: &mut LiveProject, until_focus: bool) {
    loop {
        match live.step().expect("not cancelled") {
            Progress::Done => return,
            Progress::Checked { focus, done } => {
                let _ = live.take_outlines();
                if focus || done {
                    drop(live.answers());
                }
                if done || (focus && until_focus) {
                    return;
                }
            }
        }
    }
}

fn measure() {
    let source = PathBuf::from(std::env::var("LIVE_MEM_PROJECT").expect("LIVE_MEM_PROJECT"));
    let project = Path::new(env!("CARGO_TARGET_TMPDIR")).join("live_memory/aoc");
    if std::env::var("LIVE_MEM_REUSE").is_err() || !project.exists() {
        let _ = std::fs::remove_dir_all(&project);
        copy_dir(&source, &project);
        let warm = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--project"])
            .arg(&project)
            .output()
            .unwrap();
        assert!(warm.status.success(), "{warm:?}");
    }
    let t = Instant::now();
    eprintln!(
        "live_memory\tstart\theap {:.1} MB",
        mb(stitchwort_bench::alloc::live())
    );
    let mut session = Session::navigable_for_stack(STACK);
    session.elab.enable_expression_types();
    session
        .elab
        .set_check_cache(Rc::new(CheckCache::at(&project.join(".stitchwort/cache"))));
    session.include_from(Rc::new(DiskFiles {
        root: project.clone(),
    }));
    let files = sources(&project);
    let config = std::fs::read_to_string(project.join("stitchwort.yaml")).ok();
    let mut live = LiveProject::new(session, "aoc", config, files);
    sample("libraries loaded", &mut live, t);
    let early = "src/Aoc/Common/Range.sw";
    let late = "src/Aoc/Year2025/Day09/Proofs/Part2.sw";
    live.set_focus(early);
    run(&mut live, false);
    sample("first check", &mut live, t);
    for (path, cycles, to_end) in [(early, 4, false), (late, 4, true)] {
        let original = live.text(path).unwrap().to_string();
        live.set_focus(path);
        for i in 0..cycles {
            let text = if i % 2 == 0 {
                format!("{original}\ndef stateLoopProbe: Nat := {i} + 1\n")
            } else {
                original.clone()
            };
            live.set_text(path, Some(text));
            run(&mut live, !to_end);
            sample(&format!("{path} cycle {i}"), &mut live, t);
        }
    }
}

#[test]
#[ignore]
fn live_memory() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(measure)
        .unwrap()
        .join()
        .unwrap();
}
