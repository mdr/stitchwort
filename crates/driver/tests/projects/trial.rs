//! The trial check of edits (docs/proposals/refactoring.md §3.1): a small
//! project of two namespaces, one using the other, edited by hand-made
//! renames.

use std::collections::BTreeMap;

use stitchwort_core::hash::ContentHash;
use stitchwort_driver::declhash::{self, DeclHash, DeclKind};
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

const LAWS: &str = "\
namespace Laws

import Std (Nat)

def limit: Nat := 100

def twice (n: Nat): Nat := n + n

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero

theorem again: ∀ (n: Nat) => n + 0 = n := addZ
";

fn laws() -> LiveProject {
    let mut session = Session::navigable_for_stack(STACK);
    session.use_test_std_cache();
    let files = BTreeMap::from([("src/laws.sw".to_string(), LAWS.to_string())]);
    let mut live = LiveProject::new(session, "laws", Some("sources: [src]\n".to_string()), files);
    finish(&mut live);
    live
}

fn same_statement() -> Promise {
    Promise::SameStatement {
        renames: BTreeMap::new(),
    }
}

/// An edit of the whole of the line starting with `start`.
fn line_edit(start: &str, new_line: &str) -> Edit {
    let from = LAWS.find(start).expect("the line");
    let line = LAWS[..from].matches('\n').count() as u32;
    let width = LAWS[from..].lines().next().unwrap().encode_utf16().count() as u32;
    edit("src/laws.sw", [line, 0, line, width], new_line)
}

/// The statement moved before the colon and the proof applied to it: the
/// same theorem, another proof term (docs/proposals/theorem-binders.md §7).
fn eta_edit() -> Edit {
    line_edit(
        "theorem addZ",
        "theorem addZ (n: Nat): n + 0 = n := Nat.addZero n",
    )
}

#[test]
fn edits_that_keep_meaning_pass_both_promises() {
    run(|| {
        let mut live = laws();
        // A docs comment added and a parameter renamed: no hash moves.
        let edits = [
            line_edit("def twice", "def twice (m: Nat): Nat := m + m"),
            edit("src/laws.sw", [2, 0, 2, 0], "-- Not a doc.\n"),
        ];
        for promise in [same_meaning(), same_statement()] {
            let trial = checked(live.trial(&edits, &promise).unwrap());
            assert_eq!(trial.problems, Problems::default());
            assert!(trial.proofs_changed.is_empty());
            live.restore(trial).unwrap();
        }
    });
}

#[test]
fn a_changed_definition_body_is_refused_by_both_promises() {
    run(|| {
        let mut live = laws();
        let edits = [line_edit("def limit", "def limit: Nat := 101")];
        for promise in [same_meaning(), same_statement()] {
            let trial = checked(live.trial(&edits, &promise).unwrap());
            let names: Vec<&str> = trial
                .problems
                .changed
                .iter()
                .map(|c| c.name.as_str())
                .collect();
            assert_eq!(names, ["limit"], "{:?}", trial.problems);
            live.restore(trial).unwrap();
        }
    });
}

#[test]
fn a_changed_statement_is_refused_by_the_statement_promise() {
    run(|| {
        let mut live = laws();
        let edits = [line_edit(
            "theorem addZ",
            "theorem addZ: ∀ (n: Nat) => 0 + n = n := n => omega",
        )];
        let trial = checked(live.trial(&edits, &same_statement()).unwrap());
        let names: Vec<&str> = trial
            .problems
            .changed
            .iter()
            .map(|c| c.name.as_str())
            .collect();
        assert!(names.contains(&"addZ"), "{:?}", trial.problems);
        live.restore(trial).unwrap();
    });
}

#[test]
fn an_eta_change_of_a_proof_keeps_the_statement_not_the_meaning() {
    run(|| {
        let mut live = laws();
        let edits = [eta_edit()];

        let trial = checked(live.trial(&edits, &same_meaning()).unwrap());
        let changed: Vec<&str> = trial
            .problems
            .changed
            .iter()
            .map(|c| c.name.as_str())
            .collect();
        assert_eq!(changed, ["addZ", "again"], "{:?}", trial.problems);
        assert_eq!(trial.problems.changed[1].uses.as_deref(), Some("addZ"));
        live.restore(trial).unwrap();

        // `again` uses `addZ`, so its hash moves too; both statements held.
        let trial = checked(live.trial(&edits, &same_statement()).unwrap());
        assert_eq!(trial.problems, Problems::default());
        assert_eq!(trial.proofs_changed, ["Laws.addZ", "Laws.again"]);
        live.keep(trial);
        assert!(live.text("src/laws.sw").unwrap().contains("Nat.addZero n"));
    });
}

#[test]
fn the_project_lists_its_declarations_hashes() {
    run(|| {
        let live = laws();
        let hashes = live.declaration_hashes();
        let find = |name: &str| hashes.iter().find(|d| d.name == name).expect(name);
        assert_eq!(find("Laws.limit").kind, DeclKind::Def);
        assert_eq!(find("Laws.addZ").kind, DeclKind::Theorem);
        assert!(find("Laws.addZ").hash.is_some() && find("Laws.addZ").type_hash.is_some());
        // The statement alone: the same for two theorems that state the same.
        assert_eq!(find("Laws.addZ").type_hash, find("Laws.again").type_hash);
        assert_ne!(find("Laws.addZ").hash, find("Laws.again").hash);
        let text = declhash::show(find("Laws.limit").hash);
        assert_eq!(declhash::parse_hash(&text), find("Laws.limit").hash);
    });
}

fn hash_of(byte: u8) -> Option<ContentHash> {
    Some(ContentHash([byte; 32]))
}

fn listed(kind: DeclKind, name: &str, hash: u8, ty: u8) -> DeclHash {
    DeclHash {
        kind,
        name: name.to_string(),
        hash: hash_of(hash),
        type_hash: hash_of(ty),
        proofless: None,
        uses: Vec::new(),
    }
}

fn using(mut decl: DeclHash, uses: &[&str]) -> DeclHash {
    decl.uses = uses.iter().map(|u| u.to_string()).collect();
    decl
}

/// Two libraries' hash lists (what `trial-edits --std-dir` compares), by
/// the two promises.
#[test]
fn two_hash_lists_compare_by_the_promise() {
    let before = [
        listed(DeclKind::Def, "Std.f", 1, 10),
        listed(DeclKind::Theorem, "Std.f.ok", 2, 20),
        listed(DeclKind::Theorem, "Std.g.ok", 3, 30),
    ];
    // `f` untouched; `f.ok` has another proof; `g.ok` another statement; a
    // new declaration.
    let after = [
        listed(DeclKind::Def, "Std.f", 1, 10),
        listed(DeclKind::Theorem, "Std.f.ok", 5, 20),
        listed(DeclKind::Theorem, "Std.g.ok", 6, 31),
        listed(DeclKind::Def, "Std.h", 7, 70),
    ];
    let meaning = declhash::compare(&before, &after, &same_meaning());
    let names =
        |d: &declhash::HashDiff| d.changed.iter().map(|c| c.name.clone()).collect::<Vec<_>>();
    assert_eq!(names(&meaning), ["Std.f.ok", "Std.g.ok"]);
    assert_eq!(meaning.added, ["Std.h"]);

    let statement = declhash::compare(&before, &after, &same_statement());
    assert_eq!(names(&statement), ["Std.g.ok"]);
    assert_eq!(statement.proofs_changed, ["Std.f.ok"]);

    // A definition may not move its hash under the statement promise, even
    // with its type hash held.
    let mut moved = after.clone();
    moved[0] = listed(DeclKind::Def, "Std.f", 9, 10);
    let diff = declhash::compare(&before, &moved, &same_statement());
    assert!(names(&diff).contains(&"Std.f".to_string()), "{diff:?}");
}

/// A definition that mentions a proof (a structure's invariant, a
/// `decreasing` proof) moves when the proof does: the comparison names the
/// re-proved theorem where the change starts, and what moved only because
/// of another change says so.
#[test]
fn a_moved_definition_names_the_proof_it_mentions() {
    let before = [
        listed(DeclKind::Theorem, "Std.base", 1, 10),
        listed(DeclKind::Theorem, "Std.t", 2, 20),
        listed(DeclKind::Def, "Std.t.%match1", 3, 30),
        listed(DeclKind::Theorem, "Std.u", 4, 40),
        listed(DeclKind::Def, "Std.d", 5, 50),
        listed(DeclKind::Def, "Std.e", 6, 60),
    ];
    // `t` has another proof, with its lifted `match` (which calls `t`
    // back); `u` is re-proved only because it uses `t`; `d` mentions `u`;
    // `e` mentions `d`.
    let after = [
        listed(DeclKind::Theorem, "Std.base", 1, 10),
        using(
            listed(DeclKind::Theorem, "Std.t", 7, 20),
            &["Std.t.%match1", "Std.base"],
        ),
        using(listed(DeclKind::Def, "Std.t.%match1", 8, 31), &["Std.t"]),
        using(listed(DeclKind::Theorem, "Std.u", 9, 40), &["Std.t"]),
        using(listed(DeclKind::Def, "Std.d", 10, 50), &["Std.u"]),
        using(listed(DeclKind::Def, "Std.e", 11, 60), &["Std.d"]),
    ];
    let diff = declhash::compare(&before, &after, &same_statement());
    let moved: Vec<(&str, Option<&str>, Vec<&str>)> = diff
        .changed
        .iter()
        .map(|c| {
            (
                c.name.as_str(),
                c.uses.as_deref(),
                c.reproved.iter().map(String::as_str).collect(),
            )
        })
        .collect();
    assert_eq!(
        moved,
        [
            ("Std.d", None, vec!["Std.t", "Std.t.%match1"]),
            ("Std.e", Some("Std.d"), vec![]),
        ]
    );
    assert_eq!(declhash::owner("Std.t.%match1"), "Std.t");
}

/// A definition that mentions a proof moves with it: the trial names the
/// re-proved theorem where the change starts, through the theorems
/// between.
#[test]
fn a_definition_that_mentions_a_reproved_theorem_names_it() {
    run(|| {
        let mut live = laws();
        let add = [line_edit(
            "def twice",
            "def proofOf (n: Nat): n + 0 = n := again n",
        )];
        let trial = checked(live.trial(&add, &same_meaning()).unwrap());
        live.keep(trial);
        let trial = checked(live.trial(&[eta_edit()], &same_statement()).unwrap());
        let changed: Vec<(&str, Option<&str>, &[String])> = trial
            .problems
            .changed
            .iter()
            .map(|c| (c.name.as_str(), c.uses.as_deref(), c.reproved.as_slice()))
            .collect();
        assert_eq!(
            changed,
            [("proofOf", None, &["Laws.addZ".to_string()][..])],
            "{:?}",
            trial.problems
        );
        live.restore(trial).unwrap();
    });
}

const PROOFS: &str = "\
namespace Proofs

import Std (Nat)

theorem addZ: ∀ (n: Nat) => n + 0 = n := Nat.addZero

def keep (n: Nat) (same: n + 0 = n): Nat := n

def five: Nat := keep 5 (addZ 5)

def user: Nat := five + 1
";

/// A project whose definitions embed a proof: `five` passes `addZ 5` to a
/// parameter whose type is a proposition.
fn proofs() -> LiveProject {
    let mut session = Session::navigable_for_stack(STACK);
    session.use_test_std_cache();
    let files = BTreeMap::from([("src/proofs.sw".to_string(), PROOFS.to_string())]);
    let mut live = LiveProject::new(
        session,
        "proofs",
        Some("sources: [src]\n".to_string()),
        files,
    );
    finish(&mut live);
    live
}

fn proofs_only() -> Promise {
    Promise::ProofsOnly {
        renames: BTreeMap::new(),
    }
}

fn proofs_edit(start: &str, new_line: &str) -> Edit {
    let from = PROOFS.find(start).expect("the line");
    let line = PROOFS[..from].matches('\n').count() as u32;
    let width = PROOFS[from..]
        .lines()
        .next()
        .unwrap()
        .encode_utf16()
        .count() as u32;
    edit("src/proofs.sw", [line, 0, line, width], new_line)
}

fn changed_names(trial: &Trial) -> Vec<&str> {
    trial
        .problems
        .changed
        .iter()
        .map(|c| c.name.as_str())
        .collect()
}

/// Re-proving a theorem that a definition embeds moves the definition's
/// hash, and its callers': refused by "same statement", accepted by
/// "proofs only", which names the definitions that moved.
#[test]
fn an_embedded_proof_that_changes_passes_only_the_proofs_promise() {
    run(|| {
        let mut live = proofs();
        let edits = [proofs_edit(
            "theorem addZ",
            "theorem addZ (n: Nat): n + 0 = n := Nat.addZero n",
        )];
        let trial = checked(live.trial(&edits, &same_statement()).unwrap());
        assert_eq!(
            changed_names(&trial),
            ["five", "user"],
            "{:?}",
            trial.problems
        );
        assert_eq!(trial.problems.changed[0].reproved, ["Proofs.addZ"]);
        live.restore(trial).unwrap();

        let trial = checked(live.trial(&edits, &proofs_only()).unwrap());
        assert_eq!(trial.problems, Problems::default());
        assert_eq!(trial.proofs_changed, ["Proofs.addZ"]);
        assert_eq!(trial.proofs_only, ["Proofs.five", "Proofs.user"]);
        live.restore(trial).unwrap();
    });
}

/// A change to what a definition computes is refused by both promises,
/// even next to a proof that changed with it.
#[test]
fn a_computational_change_fails_both_promises() {
    run(|| {
        let mut live = proofs();
        let edits = [proofs_edit("def five", "def five: Nat := keep 6 (addZ 6)")];
        for promise in [same_statement(), proofs_only()] {
            let trial = checked(live.trial(&edits, &promise).unwrap());
            assert_eq!(
                changed_names(&trial),
                ["five", "user"],
                "{:?}",
                trial.problems
            );
            assert_eq!(trial.problems.changed[1].uses.as_deref(), Some("five"));
            live.restore(trial).unwrap();
        }
    });
}

/// A definition whose type changes is refused, even where only a
/// proposition in it changed and its body is the same: its statement says
/// something else.
#[test]
fn a_changed_type_fails_the_proofs_promise() {
    run(|| {
        let mut live = proofs();
        let edits = [
            proofs_edit("def keep", "def keep (n: Nat) (same: n = n): Nat := n"),
            proofs_edit("def five", "def five: Nat := keep 5 rfl"),
        ];
        let trial = checked(live.trial(&edits, &proofs_only()).unwrap());
        assert_eq!(
            changed_names(&trial),
            ["keep", "five", "user"],
            "{:?}",
            trial.problems
        );
        assert_eq!(trial.problems.changed[0].uses, None);
        assert_eq!(trial.problems.changed[1].uses.as_deref(), Some("keep"));
        live.restore(trial).unwrap();
    });
}

/// The hash without proofs is listed, and is a theorem's statement: two
/// theorems that state the same have the same one. A definition with no
/// proofs in it or in what it mentions has the same hash both ways.
#[test]
fn the_hash_without_proofs_of_a_theorem_is_its_statement() {
    run(|| {
        let live = laws();
        let hashes = live.declaration_hashes();
        let find = |name: &str| hashes.iter().find(|d| d.name == name).expect(name);
        assert!(find("Laws.limit").proofless.is_some());
        assert_eq!(find("Laws.limit").proofless, find("Laws.limit").hash);
        assert_ne!(find("Laws.addZ").proofless, find("Laws.addZ").hash);
        assert_eq!(find("Laws.addZ").proofless, find("Laws.again").proofless);
        assert_ne!(find("Laws.addZ").proofless, find("Laws.twice").proofless);
    });
}

/// Two hash lists under "proofs only": a definition whose hash without
/// proofs held is accepted and listed apart from the theorems; one whose
/// hash without proofs moved is refused; a list without those hashes
/// accepts nothing.
#[test]
fn two_hash_lists_compare_by_the_proofs_promise() {
    let with = |mut d: DeclHash, proofless: u8| {
        d.proofless = hash_of(proofless);
        d
    };
    let before = [
        with(listed(DeclKind::Theorem, "Std.t", 1, 10), 100),
        with(listed(DeclKind::Def, "Std.d", 2, 20), 101),
        with(listed(DeclKind::Def, "Std.e", 3, 30), 102),
        listed(DeclKind::Def, "Std.old", 4, 40),
    ];
    let after = [
        with(listed(DeclKind::Theorem, "Std.t", 5, 10), 100),
        with(listed(DeclKind::Def, "Std.d", 6, 20), 101),
        with(listed(DeclKind::Def, "Std.e", 7, 30), 103),
        listed(DeclKind::Def, "Std.old", 8, 40),
    ];
    let diff = declhash::compare(&before, &after, &proofs_only());
    let names: Vec<&str> = diff.changed.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(names, ["Std.e", "Std.old"]);
    assert_eq!(diff.proofs_changed, ["Std.t"]);
    assert_eq!(diff.proofs_only, ["Std.d"]);
}
