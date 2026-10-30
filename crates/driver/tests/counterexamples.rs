//! Counterexample search, stage 1 (docs/proposals/counterexample-search.md
//! §10): what each acceptance example's search did, from the session's log;
//! the fast runtime and the reference evaluator agreeing on every
//! counterexample (acceptance test 11); and no search for a theorem that
//! checks (test 9). The notes themselves are in the examples' snapshots
//! (`examples/reject/counterexample-*.sw`, `examples/goals/counterexample-*.sw`).

use std::path::Path;

use stitchwort_driver::counterexample::Verdict;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_elab::counterexample::{Budget, MAX_INPUTS, Phase, RANDOM_SIZE, Runner, SearchLog};

const STACK: usize = 16 * 1024 * 1024;

fn example(name: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// Loads example `name` (it may fail), with the fast runtime or without:
/// the notes on its diagnostics, and the searches' log.
fn search(name: &str, fast: bool) -> (Vec<String>, Vec<SearchLog>) {
    let text = example(name);
    let name = name.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        if !fast {
            session.elab.counterexample_runner = None;
        }
        let diagnostics = match session.load(&name, &text) {
            Ok(_) => session.warnings.clone(),
            Err(diagnostics) => diagnostics,
        };
        let notes = diagnostics
            .iter()
            .flat_map(|d| d.notes.iter())
            .filter(|n| n.contains("this statement is false") || n.contains("internal error"))
            .cloned()
            .collect();
        let log = session.elab.counterexample_log.borrow().clone();
        (notes, log)
    })
}

/// The only search of example `name`, run on the fast runtime.
fn only(name: &str) -> SearchLog {
    let (_, log) = search(name, true);
    assert_eq!(log.len(), 1, "{name}: {log:?}");
    log.into_iter().next().unwrap()
}

fn found(log: &SearchLog) -> Vec<&str> {
    log.found
        .as_ref()
        .unwrap_or_else(|| panic!("no counterexample: {log:?}"))
        .iter()
        .map(String::as_str)
        .collect()
}

#[test]
fn reverse_append_is_false_at_the_smallest_lists() {
    let log = only("reject/counterexample-reverse-append.sw");
    assert_eq!(log.runner, Some(Runner::Fast));
    assert_eq!(found(&log), ["xs = [0]", "ys = [1]"]);
}

#[test]
fn a_missing_hypothesis_is_found_and_adding_it_silences_the_search() {
    let (notes, log) = search("reject/counterexample-sub-add.sw", true);
    assert_eq!(log.len(), 2, "{log:?}");
    assert_eq!(found(&log[0]), ["a = 0", "b = 1"]);
    // With `b <= a`: inputs are discarded, and none is a counterexample.
    assert!(log[1].found.is_none(), "{:?}", log[1]);
    assert!(log[1].discarded > 0, "{:?}", log[1]);
    assert_eq!(log[1].tried, MAX_INPUTS, "{:?}", log[1]);
    assert_eq!(notes.len(), 1, "{notes:?}");
}

#[test]
fn a_true_statement_gets_no_note() {
    let log = only("reject/counterexample-true-statement.sw");
    assert!(log.found.is_none(), "{log:?}");
    assert_eq!(log.tried, MAX_INPUTS, "{log:?}");
    assert_eq!(log.discarded, 0, "{log:?}");
}

/// SW-900: random trees holding a `List` or a `Vec` of themselves, up to
/// the largest random size, are made without running out of memory (the
/// test tier's memory cap), and every one is drawn: none gives up at
/// `MAX_RANDOM_VALUES`.
#[test]
fn random_trees_share_their_size_among_their_children() {
    let (notes, log) = search("reject/counterexample-nested-trees.sw", true);
    assert!(notes.is_empty(), "{notes:?}");
    let searched: Vec<&str> = log.iter().map(|l| l.theorem.as_str()).collect();
    assert_eq!(searched, ["rose", "smaller", "pair", "grid"], "{log:?}");
    for l in &log {
        assert!(l.out_of_scope.is_none() && l.found.is_none(), "{l:?}");
        assert_eq!(l.tried, MAX_INPUTS, "{l:?}");
        assert!(l.random > 0, "{l:?}");
        assert_eq!(l.random_size, RANDOM_SIZE, "{l:?}");
    }
}

#[test]
fn a_data_type_is_enumerated_from_its_constructors() {
    let log = only("reject/counterexample-data-type.sw");
    assert_eq!(found(&log), ["shape = Square 1"]);
}

#[test]
fn a_record_is_shown_as_a_record() {
    let log = only("reject/counterexample-record.sw");
    assert_eq!(found(&log), ["point = { x = 0, y = 1 }"]);
}

#[test]
fn a_polymorphic_statement_is_tried_at_nat() {
    let (notes, log) = search("reject/counterexample-polymorphic.sw", true);
    assert_eq!(found(&log[0]), ["xs = [0]", "ys = [1]"]);
    assert!(notes[0].contains("(with a := Nat)"), "{notes:?}");
}

#[test]
fn a_hypothesis_never_true_gives_up_silently() {
    let (notes, log) = search("reject/counterexample-gave-up.sw", true);
    assert!(notes.is_empty(), "{notes:?}");
    let log = &log[0];
    assert!(log.found.is_none(), "{log:?}");
    assert!(log.tried > 0 && log.discarded == log.tried, "{log:?}");
}

#[test]
fn out_of_scope_statements_are_not_searched() {
    let (notes, log) = search("reject/counterexample-out-of-scope.sw", true);
    assert!(notes.is_empty(), "{notes:?}");
    assert_eq!(log.len(), 2, "{log:?}");
    for entry in &log {
        assert!(entry.out_of_scope.is_some(), "{entry:?}");
        assert_eq!(entry.tried, 0, "{entry:?}");
    }
    assert!(
        log[0].out_of_scope.as_deref().unwrap().contains("function"),
        "{log:?}"
    );
    assert!(
        log[1]
            .out_of_scope
            .as_deref()
            .unwrap()
            .contains("nothing decides"),
        "{log:?}"
    );
}

#[test]
fn a_statement_with_a_huge_normal_form_is_not_searched() {
    let log = only("reject/lemma-on-large-normal-form.sw");
    let why = log.out_of_scope.as_deref().unwrap_or_default();
    assert!(why.contains("more than 100000 nodes"), "{log:?}");
    assert_eq!(log.tried, 0, "{log:?}");
}

#[test]
fn a_counterexample_at_a_goal() {
    let log = only("goals/counterexample-at-hole.sw");
    assert_eq!(found(&log), ["n = 1"]);
}

#[test]
fn running_out_of_steps_on_every_input_says_nothing() {
    let (notes, log) = search("goals/counterexample-out-of-steps.sw", true);
    assert!(notes.is_empty(), "{notes:?}");
    let log = &log[0];
    assert!(log.found.is_none(), "{log:?}");
    assert!(
        log.out_of_steps > 0 && log.out_of_steps == log.tried,
        "{log:?}"
    );
}

// Stage 2 (§10): random inputs, shrinking, more types.

/// A counterexample needing a list of 12 elements is found by a random
/// list and shrunk to a smallest one.
#[test]
fn a_long_list_is_found_at_random_and_shrunk() {
    let log = only("reject/counterexample-long-list.sw");
    assert_eq!(found(&log), ["xs = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]"]);
    assert_eq!(log.found_by, Some(Phase::Random), "{log:?}");
    assert!(log.shrinks > 0, "{log:?}");
    // Every input up to a size was tried first.
    assert_eq!(log.tried - log.random, MAX_INPUTS / 2, "{log:?}");
}

/// A `Nat` bug at 2^64 is found: random numbers include a machine word's
/// edges.
#[test]
fn a_bug_at_a_machine_words_edge_is_found() {
    let log = only("reject/counterexample-word-edge.sw");
    assert_eq!(found(&log), ["n = 18446744073709551616"]);
    assert_eq!(log.found_by, Some(Phase::Random), "{log:?}");
}

/// A record with `(ok: lo <= hi)` never has `lo > hi`: the true statement
/// about it holds on every input, none discarded, and the false one's
/// counterexample is a range that exists.
#[test]
fn a_proof_field_is_kept_true() {
    let (notes, log) = search("reject/counterexample-proof-field.sw", true);
    assert_eq!(log.len(), 2, "{log:?}");
    assert!(log[0].found.is_none(), "{:?}", log[0]);
    assert_eq!(log[0].tried, MAX_INPUTS, "{:?}", log[0]);
    assert!(log[0].random > 0 && log[0].discarded == 0, "{:?}", log[0]);
    assert_eq!(found(&log[1]), ["r = { lo = 0, hi = 1, ok = rfl }"]);
    assert_eq!(notes.len(), 1, "{notes:?}");
}

#[test]
fn text_and_characters_are_inputs() {
    let (_, log) = search("reject/counterexample-text.sw", true);
    assert_eq!(found(&log[0]), ["t = \"ab\""]);
    assert_eq!(log[0].found_by, Some(Phase::Enumerated));
    // Found at random, and shrunk to the smallest character past ASCII.
    assert_eq!(found(&log[1]), ["c = '\\u{80}'"]);
    assert_eq!(log[1].found_by, Some(Phase::Random));
}

#[test]
fn the_library_types_are_inputs() {
    let (_, log) = search("reject/counterexample-library-types.sw", true);
    let found: Vec<Vec<&str>> = log.iter().map(found).collect();
    assert_eq!(
        found,
        [
            vec!["x = Float.nan"],
            vec!["i = 4"],
            vec!["v = Vec.fromList [1, 0, 0]"],
            vec!["m = Map.fromList [(0, 0)]"],
            vec!["s = { items = Map.fromList [(0, ())] }"],
        ]
    );
}

/// The same statement gets the same random inputs every time (§5.1).
#[test]
fn the_random_inputs_are_the_same_every_time() {
    let a = only("reject/counterexample-long-list.sw");
    let b = only("reject/counterexample-long-list.sw");
    assert_eq!((a.tried, a.shrinks), (b.tried, b.shrinks));
}

/// `check --counterexamples` (D1159): every theorem of the program is
/// searched, its proof checked or not, each with a verdict.
fn verdicts(name: &str) -> Vec<(String, bool, Verdict, String)> {
    let text = example(name);
    let name = name.to_string();
    with_stack(STACK, move || {
        let mut session = Session::for_stack(STACK);
        let _ = session.load(&name, &text);
        let budget = Budget {
            inputs: 2000,
            millis: 2000,
        };
        session
            .search_theorems(budget, &|_| true)
            .into_iter()
            .map(|s| {
                let (verdict, line) = s.verdict();
                (s.name, s.checked, verdict, line)
            })
            .collect()
    })
}

#[test]
fn check_counterexamples_gives_every_theorem_a_verdict() {
    let found = verdicts("reject/counterexample-proof-field.sw");
    let rows: Vec<(&str, bool, Verdict)> = found
        .iter()
        .map(|(name, checked, verdict, _)| (name.as_str(), *checked, *verdict))
        .collect();
    assert_eq!(
        rows,
        [
            // The record's own extensionality theorem, which checks.
            ("Range.ext", true, Verdict::GaveUp),
            ("rangeOrdered", false, Verdict::NoneFound),
            ("rangeEmpty", false, Verdict::False),
        ],
        "{found:?}"
    );
    assert_eq!(
        found[1].3,
        "none in 2000 cases (sizes up to 63; evidence, not a proof)"
    );
    assert_eq!(
        found[2].3,
        "counterexample: r = { lo = 0, hi = 1, ok = rfl }"
    );
    // Out of scope: said why.
    let out = verdicts("reject/counterexample-out-of-scope.sw");
    assert_eq!(out[0].2, Verdict::NotApplicable, "{out:?}");
    assert_eq!(out[0].3, "not applicable: `f` is a function");
}

/// On theorems that check, no counterexample (a soundness canary, §7.3).
#[test]
fn theorems_that_check_have_no_counterexample() {
    for name in ["accept/integers.sw", "accept/list-toolkit.sw"] {
        let found = verdicts(name);
        assert!(found.iter().all(|(_, checked, _, _)| *checked), "{name}");
        assert!(
            found.iter().all(|(_, _, v, _)| *v != Verdict::False),
            "{name}: {found:?}"
        );
        assert!(
            found.iter().any(|(_, _, v, _)| *v == Verdict::NoneFound),
            "{name}: {found:?}"
        );
    }
}

/// Acceptance test 11: the reference evaluator, forced, finds the same
/// counterexamples (and says the same) as the fast runtime.
#[test]
fn the_fast_runtime_and_the_reference_evaluator_agree() {
    for name in [
        "reject/counterexample-reverse-append.sw",
        "reject/counterexample-sub-add.sw",
        "reject/counterexample-true-statement.sw",
        "reject/counterexample-data-type.sw",
        "reject/counterexample-record.sw",
        "reject/counterexample-polymorphic.sw",
        "goals/counterexample-at-hole.sw",
        "reject/counterexample-long-list.sw",
        "reject/counterexample-word-edge.sw",
        "reject/counterexample-proof-field.sw",
        "reject/counterexample-text.sw",
        "reject/counterexample-library-types.sw",
    ] {
        let (fast_notes, fast) = search(name, true);
        let (reference_notes, reference) = search(name, false);
        assert_eq!(fast_notes, reference_notes, "{name}");
        assert!(
            !fast_notes.iter().any(|n| n.contains("internal error")),
            "{name}"
        );
        for (f, r) in fast.iter().zip(&reference) {
            assert_eq!(f.found, r.found, "{name}");
            assert!(!f.disagreed, "{name}");
            assert_eq!(r.runner, Some(Runner::Reference), "{name}");
            if f.found.is_some() {
                assert_eq!(f.runner, Some(Runner::Fast), "{name}");
                assert_eq!(f.tried, r.tried, "{name}");
            }
        }
    }
}

/// Acceptance test 9: theorems that check are never searched.
#[test]
fn theorems_that_check_are_not_searched() {
    for name in [
        "accept/integers.sw",
        "accept/omega-basics.sw",
        "accept/list-toolkit.sw",
    ] {
        let (notes, log) = search(name, true);
        assert!(notes.is_empty() && log.is_empty(), "{name}: {log:?}");
    }
}

/// The proposal's §12 measurement: how many theorems of the library and of
/// the AoC solutions are in scope for the search (their statements could be
/// searched, were their proofs to fail), and why the rest aren't.
/// `cargo test --release -p stitchwort-driver --test counterexamples --
/// --ignored --nocapture scope`.
#[test]
#[ignore]
fn scope() {
    use std::collections::BTreeMap;
    use stitchwort_core::DefId;
    use stitchwort_core::globals::State;
    use stitchwort_driver::project::{DiskFiles, Target};
    with_stack(STACK, || {
        let mut session = Session::eager_for_stack(STACK);
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
        if let Err(errors) = session.load_project(&DiskFiles { root }, "aoc", &Target::Everything) {
            panic!("aoc doesn't load: {errors:#?}");
        }
        let theorems: Vec<(DefId, String)> = (0..session.elab.globals.defs.len())
            .map(DefId)
            .filter(|id| {
                let def = session.elab.globals.def(*id);
                def.theorem && def.state() == State::Final && !def.path.contains('%')
            })
            .map(|id| (id, session.elab.globals.def(id).path.to_string()))
            .collect();
        let mut tally: BTreeMap<(&str, String), usize> = BTreeMap::new();
        for (id, path) in theorems {
            let part = if path.starts_with("Aoc") {
                "aoc"
            } else {
                "std"
            };
            let outcome = match session.elab.counterexample_scope(id) {
                Ok(()) => "in scope".to_string(),
                Err(why) => {
                    let kind = [
                        "is a function",
                        "nothing decides the conclusion",
                        "nothing decides `",
                        "no inputs for",
                        "isn't a type of data",
                        "depends on another parameter",
                    ]
                    .into_iter()
                    .find(|k| why.contains(k))
                    .unwrap_or("other");
                    if kind == "other" || std::env::var("SCOPE_VERBOSE").is_ok() {
                        eprintln!("{path}: {why}");
                    }
                    format!("out: {kind}")
                }
            };
            *tally.entry((part, outcome)).or_default() += 1;
        }
        for ((part, outcome), n) in &tally {
            println!("{part}\t{n}\t{outcome}");
        }
    });
}
