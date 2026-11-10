//! The trial check of edits (docs/proposals/refactoring.md §3.1): a small
//! project of two namespaces, one using the other, edited by hand-made
//! renames.

use std::collections::BTreeMap;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::live::{
    Edit, LiveProject, Place, Problems, Progress, Promise, Refusal, Trial, TrialOutcome,
};
use stitchwort_driver::nav::Range;

const STACK: usize = 16 * 1024 * 1024;

const SHOP: &str = "\
namespace Shop

def limit: Nat := 100

def cap (n: Nat): Nat := n + limit

def step (count: Nat): Nat :=
  let next := count + 1
  next * 2
";

const REPORT: &str = "\
namespace Shop.Report

import Shop (cap, step)

def report: Nat := cap (step 3)

test \"report\" := report == 108
";

fn project() -> LiveProject {
    let mut session = Session::navigable_for_stack(STACK);
    session.use_test_std_cache();
    let files = BTreeMap::from([
        ("src/shop.sw".to_string(), SHOP.to_string()),
        ("src/report.sw".to_string(), REPORT.to_string()),
    ]);
    let mut live = LiveProject::new(session, "shop", Some("sources: [src]\n".to_string()), files);
    finish(&mut live);
    live
}

fn finish(live: &mut LiveProject) {
    while let Progress::Checked { .. } = live.step().expect("not cancelled") {}
}

/// The range of the `nth` (from 0) `word` in the file's text, on one line.
fn at(text: &str, word: &str, nth: usize) -> Range {
    let start = text.match_indices(word).nth(nth).expect("the word").0;
    let line = text[..start].matches('\n').count() as u32;
    let column = (start - text[..start].rfind('\n').map_or(0, |i| i + 1)) as u32;
    [line, column, line, column + word.len() as u32]
}

fn edit(path: &str, range: Range, new_text: &str) -> Edit {
    Edit {
        place: Place::Program(path.to_string()),
        range,
        new_text: new_text.to_string(),
    }
}

fn same_meaning() -> Promise {
    Promise::SameMeaning {
        renames: BTreeMap::new(),
    }
}

fn checked(outcome: TrialOutcome) -> Trial {
    match outcome {
        TrialOutcome::Checked(trial) => trial,
        TrialOutcome::Refused(refusals) => panic!("refused: {refusals:?}"),
    }
}

fn run<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    with_stack(STACK, f)
}

#[test]
fn a_rename_of_a_local_passes_and_is_kept() {
    run(|| {
        let mut live = project();
        let edits = [
            edit("src/shop.sw", at(SHOP, "next", 0), "after"),
            edit("src/shop.sw", at(SHOP, "next", 1), "after"),
        ];
        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        assert_eq!(trial.problems, Problems::default());
        live.keep(trial);
        assert!(!live.pending(), "kept as checked");
        assert!(
            live.text("src/shop.sw")
                .unwrap()
                .contains("let after := count + 1")
        );
    });
}

#[test]
fn a_rename_of_a_function_passes_through_the_rename_map() {
    run(|| {
        let mut live = project();
        let edits = [
            edit("src/shop.sw", at(SHOP, "step", 0), "advance"),
            edit("src/report.sw", at(REPORT, "step", 0), "advance"),
            edit("src/report.sw", at(REPORT, "step", 1), "advance"),
        ];
        let promise = Promise::SameMeaning {
            renames: BTreeMap::from([("Shop.step".to_string(), "Shop.advance".to_string())]),
        };
        let trial = checked(live.trial(&edits, &promise).unwrap());
        assert_eq!(trial.problems, Problems::default());
        // Without the map, the function counts as gone and a new one come.
        live.restore(trial).unwrap();
        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        assert!(!trial.problems.changed.is_empty());
        live.restore(trial).unwrap();
    });
}

#[test]
fn a_new_error_is_a_problem() {
    run(|| {
        let mut live = project();
        // The binder renamed, its use left behind.
        let edits = [edit("src/shop.sw", at(SHOP, "next", 0), "after")];
        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        let problems = &trial.problems;
        assert_eq!(problems.diagnostics.len(), 1, "{problems:?}");
        let error = &problems.diagnostics[0];
        assert_eq!(error.code, "E-UNKNOWN-NAME");
        assert_eq!(error.path, "src/shop.sw");
        assert_eq!(error.declaration.as_deref(), Some("step"));
        assert_eq!(error.range, at(SHOP, "next", 1));
        let words = problems.describe("renaming `next` to `after`");
        assert!(
            words[0].starts_with(
                "renaming `next` to `after` would cause an error in `step` (src/shop.sw, line 9): "
            ),
            "{words:?}"
        );
        live.restore(trial).unwrap();
    });
}

#[test]
fn a_silent_change_of_meaning_is_a_problem() {
    run(|| {
        let mut live = project();
        // `n` renamed to `limit`: the use of the global `limit` now means
        // the parameter. Everything still checks.
        let edits = [
            edit("src/shop.sw", at(SHOP, "n", 1), "limit"),
            edit("src/shop.sw", at(SHOP, "n +", 0), "limit +"),
        ];
        assert_eq!(
            &SHOP[..SHOP.find("n +").unwrap()],
            &SHOP[..SHOP.match_indices("n").nth(2).unwrap().0],
            "the edits are of `cap`'s parameter and its use"
        );
        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        let problems = &trial.problems;
        assert!(problems.diagnostics.is_empty(), "{problems:?}");
        let first = &problems.changed[0];
        assert_eq!(first.name, "cap");
        assert_eq!(first.namespace, "Shop");
        assert_eq!(first.uses, None);
        assert_eq!(first.path.as_deref(), Some("src/shop.sw"));
        assert_eq!(first.range, Some(at(SHOP, "cap", 0)));
        // `report` changes only because `cap` did.
        let report = (problems.changed.iter())
            .find(|c| c.name == "report")
            .expect("report changes too");
        assert_eq!(report.uses.as_deref(), Some("Shop.cap"));
        let words = problems.describe("renaming `n` to `limit`");
        assert_eq!(
            words[0],
            "renaming `n` to `limit` would change what `cap` means (src/shop.sw, line 5)"
        );
        live.restore(trial).unwrap();
    });
}

#[test]
fn a_file_that_does_not_parse_is_refused() {
    run(|| {
        let mut live = project();
        let broken = format!("{REPORT}\ndef broken: Nat :=\n");
        live.set_text("src/report.sw", Some(broken));
        finish(&mut live);
        let edits = [edit("src/shop.sw", at(SHOP, "next", 0), "after")];
        let TrialOutcome::Refused(refusals) = live.trial(&edits, &same_meaning()).unwrap() else {
            panic!("checked");
        };
        assert!(
            matches!(&refusals[..], [Refusal::Unparsed { path, .. }] if path == "src/report.sw"),
            "{refusals:?}"
        );
        assert_eq!(
            refusals[0].describe("renaming `next` to `after`"),
            "can't check renaming `next` to `after`: `src/report.sw` doesn't parse (line 9)"
        );
        assert_eq!(live.text("src/shop.sw"), Some(SHOP), "nothing applied");
    });
}

#[test]
fn other_edits_that_cannot_be_checked_are_refused() {
    run(|| {
        let mut live = project();
        let library = Edit {
            place: Place::Library("List.sw".to_string()),
            range: [0, 0, 0, 1],
            new_text: String::new(),
        };
        let refused = |live: &mut LiveProject, edits: &[Edit]| match live
            .trial(edits, &same_meaning())
            .unwrap()
        {
            TrialOutcome::Refused(refusals) => refusals,
            TrialOutcome::Checked(_) => panic!("checked"),
        };
        assert!(matches!(
            &refused(&mut live, &[library])[..],
            [Refusal::Library { .. }]
        ));
        let past_the_end = edit("src/shop.sw", [2, 0, 2, 200], "x");
        assert!(matches!(
            &refused(&mut live, &[past_the_end])[..],
            [Refusal::BadEdit { .. }]
        ));
        live.set_text("src/shop.sw", Some(format!("{SHOP}\n")));
        assert_eq!(
            refused(&mut live, &[edit("src/shop.sw", at(SHOP, "next", 0), "x")]),
            [Refusal::NotChecked]
        );
    });
}

#[test]
fn restore_gives_back_the_answers_from_before() {
    run(|| {
        let mut live = project();
        // The first answers include the library's; compare later ones.
        live.answers();
        let before = format!("{:?}", live.answers());
        let edits = [edit("src/shop.sw", at(SHOP, "next", 0), "after")];
        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        assert!(!trial.problems.is_empty());
        assert!(before.contains("next"));
        live.restore(trial).unwrap();
        assert!(!live.pending());
        assert_eq!(live.text("src/shop.sw"), Some(SHOP));
        assert_eq!(format!("{:?}", live.answers()), before);
    });
}

/// How long trials take on the AoC project (docs/proposals/refactoring.md
/// §3.1): a rename of a local inside a day, and the same kind of rename in
/// `Aoc.Common`, which most days use. Not part of any tier; run it by hand:
/// `task test:one -- --run-ignored only --no-capture trial_timings_on_aoc`.
/// `AOC_TRIAL_KEEP=src/Aoc/Common,src/Aoc/Year2021` (the default) keeps only
/// the files under those folders, so that the first check, which isn't
/// what is measured, stays short; empty keeps the whole project. The
/// project's namespaces go through a check cache in `AOC_TRIAL_CACHE` (a
/// folder of the system's temporary one by default), as in the editor.
#[test]
#[ignore = "a measurement, by hand"]
fn trial_timings_on_aoc() {
    use std::time::Instant;
    use stitchwort_driver::project::{DiskFiles, Files};

    const AOC_STACK: usize = 64 * 1024 * 1024;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let keep = std::env::var("AOC_TRIAL_KEEP")
        .unwrap_or_else(|_| "src/Aoc/Common,src/Aoc/Year2021".to_string());
    let keep: Vec<&str> = keep.split(',').filter(|k| !k.is_empty()).collect();
    let cache = std::env::var("AOC_TRIAL_CACHE")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| std::env::temp_dir().join("stitchwort-aoc-trial"));
    let mut files = BTreeMap::new();
    let mut dirs = vec![root.join("src")];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|e| e == "sw") {
                let relative = path
                    .strip_prefix(&root)
                    .unwrap()
                    .to_string_lossy()
                    .to_string();
                if keep.is_empty() || keep.iter().any(|k| relative.starts_with(k)) {
                    files.insert(relative, std::fs::read_to_string(&path).unwrap());
                }
            }
        }
    }
    let day = "src/Aoc/Year2021/Day05/Day05.sw";
    let common = "src/Aoc/Common/Range.sw";
    let (day_text, common_text) = (files[day].clone(), files[common].clone());
    let config = std::fs::read_to_string(root.join("stitchwort.yaml")).ok();
    let count = files.len();
    with_stack(AOC_STACK, move || {
        let mut session = Session::navigable_for_stack(AOC_STACK);
        session.use_check_cache(&cache);
        session.include_from(DiskFiles { root: root.clone() }.include_files().unwrap());
        let started = Instant::now();
        let mut live = LiveProject::new(session, "aoc", config, files);
        finish(&mut live);
        eprintln!(
            "first check: {count} files, {} namespaces, {:.1?}",
            live.order().len(),
            started.elapsed()
        );
        // `lines` in `main`: its binder and two uses.
        let local: Vec<Edit> = (0..3)
            .map(|n| edit(day, at(&day_text, "lines", n), "vents"))
            .collect();
        // `range` in `Range.size`, the parameter and its two uses.
        let size = common_text.find("def Range.size").unwrap();
        let line = common_text[..size].matches('\n').count() as u32;
        let size_line = common_text[size..].lines().next().unwrap();
        let in_common: Vec<Edit> = size_line
            .match_indices("range")
            .map(|(i, _)| edit(common, [line, i as u32, line, i as u32 + 5], "span"))
            .collect();
        for (what, edits) in [
            ("a local in a day", local),
            ("a local in Aoc.Common", in_common),
        ] {
            let started = Instant::now();
            let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
            let tried = started.elapsed();
            let problems = trial.problems.describe(what);
            let started = Instant::now();
            live.restore(trial).unwrap();
            eprintln!(
                "{what} ({} edits): trial {tried:.1?}, restore {:.1?}, problems {problems:?}",
                edits.len(),
                started.elapsed()
            );
        }
    });
}
