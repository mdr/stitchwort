//! `stitchwort search --at`, stage 2 (SW-915; docs/proposals/search.md
//! §5.7, §8 S2): what closes a goal, on a small file of goals with known
//! closers: an exact lemma, one that needs the goal's hypotheses, one whose
//! premise `omega` closes, one that applies leaving a goal, a rewrite, and
//! a goal whose target binds a variable. Every suggestion said to close a
//! goal is pasted in place of its `?`, and the file checked again: the
//! goal must be gone, with no error.

use stitchwort_driver::driver::{Session, with_session};
use stitchwort_driver::search::Scope;
use stitchwort_driver::search_at::{AtOptions, AtReport, GoalAt, goals_in, pick};
use stitchwort_syntax::{Diagnostic, FileId, Severity};

const STACK: usize = 64 * 1024 * 1024;

const GOALS: &str = "\
import Std (Bool, Nat, List)

theorem exactly (xs: List Nat) (ys: List Nat): List.length (xs ++ ys) = List.length xs + List.length ys := ?

theorem withHyps (a: Nat) (b: Nat) (c: Nat) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := ?

theorem afterOmega (a: Nat) (c: Nat): a ≤ a + c := ?

theorem rewriting (xs: List Nat) (ys: List Nat): List.length (xs ++ ys) = List.length ys + List.length xs := ?

theorem introducing: (n: Nat) → n + 0 = n := ?

theorem falseOne (m: Nat) (n: Nat): m + n = n + m + 1 := ?

theorem byComputing: List.length [1, 2, 3] = 3 := ?

theorem fromHypothesis (a: Nat) (h: a = 3): a = 3 := ?

theorem onlyOmega (a: Nat) (b: Nat) (h: a < b): a ≤ b := ?

theorem onlyRing (x: Nat) (y: Nat): (x + y) * (x + y) = x * x + 2 * x * y + y * y := ?

theorem ruledOut (a: Nat) (h: Some a = None): a = 5 := ?

theorem byCases (x: Nat) (shared: Nat) (y: Nat): Bool.toNat (x + shared < shared + y) = Bool.toNat (x < y) := ?
";

/// Loads `text` as `goals.sw`: the diagnostics, goals included.
fn load(session: &mut Session, text: &str) -> (FileId, Vec<Diagnostic>) {
    session
        .use_check_cache(&std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("search-cache"));
    let mut diagnostics = match session.load("goals.sw", text) {
        Ok(_) => Vec::new(),
        Err(d) => d,
    };
    diagnostics.append(&mut session.warnings);
    let file = (session.sources.iter())
        .filter(|(_, f)| f.name == "goals.sw")
        .map(|(id, _)| id)
        .last()
        .expect("loaded");
    (file, diagnostics)
}

/// The options the tests search with: the defaults, but with a deadline far
/// longer than the 10 s one, so a busy machine's slowness can't truncate a
/// report (SW-1168); what these tests check is which suggestions are found,
/// not how fast. (Until SW-1082 they left out
/// `Float.Theory.magUnitsLeReflect`, which fits every `a ≤ b` and whose
/// premise `cases` grew a value to 1.4 GB on; a tried proof's values are
/// capped now.)
fn options() -> AtOptions {
    AtOptions {
        time: std::time::Duration::from_secs(120),
        ..AtOptions::default()
    }
}

/// What closes the goal on `line` of `text`.
fn at(text: &str, line: usize) -> AtReport {
    at_with(text, line, &options())
}

/// [`at`], with the given options.
fn at_with(text: &str, line: usize, options: &AtOptions) -> AtReport {
    with_session(STACK, Session::for_stack, |session| {
        let (file, diagnostics) = load(session, text);
        assert!(
            !diagnostics.iter().any(|d| d.severity == Severity::Error),
            "{diagnostics:?}"
        );
        let goals = goals_in(&session.sources, file, &diagnostics);
        let found = pick(&goals, GoalAt::Line(line, None)).unwrap().clone();
        session
            .elab
            .load_all_libraries()
            .expect("the library checks");
        let mut checking = Session::for_stack(STACK);
        load(&mut checking, text);
        session
            .search_at(
                &found,
                "goals.sw",
                options,
                &Scope::File,
                Some(&mut checking),
            )
            .unwrap_or_else(|d| panic!("{}: {}", d.code, d.message))
    })
}

/// `text` with the `?` on `line` replaced by `proof` has no goal there and
/// no error.
fn pastes(text: &str, line: usize, proof: &str) {
    let lines: Vec<String> = (text.lines().enumerate())
        .map(|(i, l)| {
            if i + 1 == line {
                l.replacen(":= ?", &format!(":= {proof}"), 1)
            } else {
                l.to_string()
            }
        })
        .collect();
    let pasted = lines.join("\n") + "\n";
    with_session(STACK, Session::for_stack, |session| {
        let (file, diagnostics) = load(session, &pasted);
        let errors: Vec<_> = (diagnostics.iter())
            .filter(|d| d.severity == Severity::Error)
            .map(|d| format!("{} {}", d.code, d.message))
            .collect();
        assert!(errors.is_empty(), "`{proof}` pasted: {errors:?}");
        let goals = goals_in(&session.sources, file, &diagnostics);
        assert!(
            !goals.iter().any(|g| g.line == line),
            "`{proof}` pasted leaves the goal"
        );
    });
}

fn line_of(name: &str) -> usize {
    GOALS
        .lines()
        .position(|l| l.contains(&format!("theorem {name}")))
        .expect("the theorem")
        + 1
}

/// Every closing suggestion of `report` pastes.
fn all_paste(report: &AtReport, line: usize) {
    for s in report.results.iter().filter(|s| s.class != "applicable") {
        assert_eq!(s.checked, "kernel");
        pastes(GOALS, line, &s.proof);
    }
}

#[test]
fn an_exact_lemma_comes_first() {
    let line = line_of("exactly");
    let report = at(GOALS, line);
    let first = &report.results[0];
    assert_eq!(
        (first.class, first.proof.as_str()),
        ("exact", "List.lengthAppend xs ys"),
        "{report:#?}"
    );
    assert_eq!(first.name, "Std.List.lengthAppend");
    assert_eq!(first.import.as_deref(), Some("import Std (List)"));
    all_paste(&report, line);
}

#[test]
fn premises_are_filled_from_hypotheses_or_closed_by_omega_or_left() {
    let line = line_of("withHyps");
    let report = at(GOALS, line);
    let first = &report.results[0];
    assert_eq!(
        (first.class, first.proof.as_str()),
        ("withHypotheses", "Nat.leTrans a b c h1 h2"),
        "{report:#?}"
    );
    // `omega` closes this goal on its own, and says so.
    assert!(report.tactics.iter().any(|t| t == "omega"), "{report:#?}");
    // Some apply leaving a goal, each listed, kernel-checked with it as a
    // hypothesis.
    let applicable: Vec<_> = (report.results.iter())
        .filter(|s| s.class == "applicable")
        .collect();
    assert!(!applicable.is_empty(), "{report:#?}");
    for s in &applicable {
        assert!(!s.goals.is_empty() && s.proof.contains('?'), "{s:?}");
    }
    assert!(applicable.iter().any(|s| s.checked == "kernel"));
    all_paste(&report, line);

    let line = line_of("afterOmega");
    let report = at(GOALS, line);
    assert_eq!(report.results[0].proof, "Nat.leAddRight a c", "{report:#?}");
    let obligation = (report.results.iter())
        .find(|s| s.class == "afterObligations")
        .expect("one closed after an obligation");
    assert_eq!(obligation.obligations[0].closer, "omega");
    all_paste(&report, line);
}

#[test]
fn rewrites_show_the_goal_they_leave() {
    let line = line_of("rewriting");
    let report = at(GOALS, line);
    let first = &report.rewrites[0];
    assert_eq!(first.proof, "rewrite List.lengthAppend xs ys in ?");
    assert_eq!(first.goal, "xs.length + ys.length = ys.length + xs.length");
    assert_eq!((first.closes, first.checked), (Some("omega"), "kernel"));
    // Then `omega` closes it: a closing suggestion.
    assert_eq!(
        report.results[0].proof, "rewrite List.lengthAppend xs ys in omega",
        "{report:#?}"
    );
    all_paste(&report, line);
}

#[test]
fn a_target_that_binds_a_variable_is_introduced() {
    let line = line_of("introducing");
    let report = at(GOALS, line);
    assert_eq!(report.goal.introduced, ["n"]);
    let first = &report.results[0];
    assert!(first.proof.starts_with("n => "), "{report:#?}");
    all_paste(&report, line);
}

/// Opening the goal computes its target, which is under the search's time
/// like the other phases (SW-2594): a goal that takes longer to open than
/// the time reports that it ran out, instead of opening for as long as it
/// takes.
#[test]
fn a_goal_that_takes_too_long_to_open_reports_running_out() {
    // 10,000 folds take more evaluation steps than the budget's first poll
    // (`budget::POLL`, 16,384), so opening is cut short by the zero time; at
    // 2,000 it finishes before then and opens the goal, which isn't what this
    // tests. It was 100,000, which took minutes in a debug build for the same
    // outcome.
    let text = "\
import Std (Nat, List)

def countDown (n: Nat) (acc: List Nat): List Nat := match n with
  | Zero => acc
  | Succ k => countDown k [k, ..acc]

theorem opening: countDown 10000 [] = [] := ?
";
    let options = AtOptions {
        time: std::time::Duration::ZERO,
        ..AtOptions::default()
    };
    let report = at_with(text, 7, &options);
    assert!(!report.budget.exhausted, "{report:#?}");
    assert!(report.results.is_empty() && report.tactics.is_empty());
    assert!(
        report.warnings.iter().any(|w| w.contains("while opening")),
        "{:?}",
        report.warnings
    );
}

#[test]
fn nothing_closes_a_false_goal() {
    let report = at(GOALS, line_of("falseOne"));
    assert_eq!(report.total.closing, 0, "{report:#?}");
    assert!(report.tactics.is_empty());
}

/// `cases` is tried as a closer too (SW-942): AoC 2021 day 3's last step,
/// which `cases` proves alone; and a rewrite after which `cases` closes it
/// adds nothing, so isn't suggested.
#[test]
fn cases_closes_a_goal_alone() {
    let line = line_of("byCases");
    let report = at(GOALS, line);
    assert!(report.tactics.iter().any(|t| t == "cases"), "{report:#?}");
    assert!(
        !(report.results.iter()).any(|s| s.proof.ends_with(" in cases")),
        "{report:#?}"
    );
    pastes(GOALS, line, "cases");
    all_paste(&report, line);
}

/// Goals whose printed form doesn't read back as the same statement, each a
/// kind `search --at` refused before it searched the goal as the elaborator
/// had it (SW-989; AoC 2021 days 12 to 18).
const UNPRINTABLE: &str = "\
import Std (Bool, Nat, List, Option, Void)

type Fold =
  | AlongX (line: Nat)
  | AlongY (line: Nat)

def lineOf (fold: Fold): Nat :=
  match fold with
    | AlongX line => line
    | AlongY line => line

theorem afterMatch (fold: Fold) (h: lineOf fold = 3): lineOf fold + 1 = 4 :=
  match fold with
    | AlongX line => ?
    | AlongY line => omega

theorem unnamed: (xs: List Nat) → List.length (List.map xs (x => x + 1)) = List.length xs
  | Nil => rfl
  | Cons _ rest => ?

type Leaf = { value: Nat, depth: Nat }

def deeper (xs: List Leaf): List Leaf := List.map xs (leaf => { value = leaf.value, depth = leaf.depth + 1 })

theorem recordInCons (leaf: Leaf) (rest: List Leaf): deeper (Cons leaf rest) = Cons ({ value = leaf.value, depth = leaf.depth + 1 }) (deeper rest) := ?

type Tree =
  | Tip (n: Nat)
  | Node (l: Tree) (r: Tree)

def find: Tree → Option Nat
  | Tip n => if 10 ≤ n then Some n else None
  | Node l r =>
    match find l with
      | Some v => Some v
      | None => find r

theorem liftedMatch: (t: Tree) → find t = None → find t = None
  | Tip n, h => h
  | Node l r, h => ?

theorem captured: (y: Nat) → (xs: List Nat) → y ∈ xs → y ∈ Cons 0 xs
  | y, Nil, member => Void.exfalso member
  | y, Cons x rest, member => ?
";

/// The line of the `?` after `marker` in `text`.
fn goal_line(text: &str, marker: &str) -> usize {
    let start = text.find(marker).expect("the marker");
    let at = start + text[start..].find('?').expect("a `?` after it");
    text[..at].matches('\n').count() + 1
}

/// `text` with the last `?` on `line` replaced by `proof` checks, and that
/// goal is gone.
fn pastes_at(text: &str, line: usize, proof: &str) {
    let lines: Vec<String> = (text.lines().enumerate())
        .map(|(i, l)| {
            if i + 1 == line {
                let q = l.rfind('?').expect("a `?`");
                format!("{}({proof}){}", &l[..q], &l[q + 1..])
            } else {
                l.to_string()
            }
        })
        .collect();
    let pasted = lines.join("\n") + "\n";
    with_session(STACK, Session::for_stack, |session| {
        let (file, diagnostics) = load(session, &pasted);
        let errors: Vec<_> = (diagnostics.iter())
            .filter(|d| d.severity == Severity::Error)
            .map(|d| format!("{} {}", d.code, d.message))
            .collect();
        assert!(errors.is_empty(), "`{proof}` pasted: {errors:?}");
        let goals = goals_in(&session.sources, file, &diagnostics);
        assert!(
            !goals.iter().any(|g| g.line == line),
            "`{proof}` pasted leaves the goal"
        );
    });
}

/// What closes each goal of `text` at `lines`: one search session and one
/// checking session for them all.
fn at_each(text: &str, lines: &[usize]) -> Vec<AtReport> {
    with_session(STACK, Session::for_stack, |session| {
        let (file, diagnostics) = load(session, text);
        assert!(
            !diagnostics.iter().any(|d| d.severity == Severity::Error),
            "{diagnostics:?}"
        );
        let goals = goals_in(&session.sources, file, &diagnostics);
        session
            .elab
            .load_all_libraries()
            .expect("the library checks");
        let mut checking = Session::for_stack(STACK);
        load(&mut checking, text);
        (lines.iter())
            .map(|line| {
                let found = pick(&goals, GoalAt::Line(*line, None)).unwrap().clone();
                session
                    .search_at(
                        &found,
                        "goals.sw",
                        &options(),
                        &Scope::File,
                        Some(&mut checking),
                    )
                    .unwrap_or_else(|d| {
                        panic!("line {line}: {}: {} {:?}", d.code, d.message, d.notes)
                    })
            })
            .collect()
    })
}

/// Each goal is searched, not refused (`E-SEARCH-AT`), and what closes it
/// pastes: a hypothesis printed before the pattern variable it mentions
/// (after a `match` on a constructor with fields), a `✝` name (a `_`
/// pattern), a record literal as a constructor's argument, a lifted
/// `%match` in a hypothesis, and a lambda whose binder is named as a
/// variable in scope (the printer's capture).
#[test]
fn goals_that_dont_print_back_are_searched() {
    let cases: [(&str, &[&str]); 5] = [
        ("theorem afterMatch", &["omega"]),
        ("theorem unnamed", &["lengthMap"]),
        ("theorem recordInCons", &["rfl"]),
        ("theorem liftedMatch", &[]),
        ("theorem captured", &["Inr member"]),
    ];
    let lines: Vec<usize> = cases
        .iter()
        .map(|(m, _)| goal_line(UNPRINTABLE, m))
        .collect();
    let reports = at_each(UNPRINTABLE, &lines);
    for (((marker, want), line), report) in cases.iter().zip(&lines).zip(&reports) {
        let closing: Vec<&str> = (report.results.iter())
            .filter(|s| s.class != "applicable")
            .map(|s| s.proof.as_str())
            .chain(report.tactics.iter().map(String::as_str))
            .collect();
        assert!(
            want.iter().all(|w| closing.iter().any(|p| p.contains(w))),
            "{marker}: {want:?} not among {closing:?}\n{report:#?}"
        );
        for proof in closing {
            pastes_at(UNPRINTABLE, *line, proof);
        }
    }
}

/// Recursive theorems whose step needs the induction hypothesis (SW-993):
/// in `omega`, as a rewrite whose argument matching solved (`x + 2`), and
/// as a rewrite after which `rfl` closes.
const RECURSIVE: &str = "\
import Std (Bool, Nat, List, Void)

def total: List Nat → Nat
  | Nil => 0
  | Cons x rest => x + total rest

theorem totalAtLeast: (xs: List Nat) → (y: Nat) → y ∈ xs → y ≤ total xs
  | Nil, y, member => Void.exfalso member
  | Cons x rest, y, Inl same => rewrite same in omega
  | Cons x rest, y, Inr later => ?

def steps: Nat → Nat → Nat
  | 0, x => x
  | Succ n, x => steps n (x + 2)

theorem stepsAdd: (n: Nat) → (x: Nat) → steps n x = x + 2 * n
  | 0, x => omega
  | Succ n, x => ?

def size: List Nat → Nat
  | Nil => 0
  | Cons _ rest => size rest + 1

theorem sizeMap: (xs: List Nat) → size (List.map xs (x => x + 1)) = size xs
  | Nil => rfl
  | Cons _ rest => ?
";

/// Each step is closed by a suggestion using the induction hypothesis on
/// the smaller argument, marked so and, in a file on its own, `elaborated`
/// (not `kernel`: nothing there checks that the call terminates); the
/// one wanted pastes, and the file then checks, termination included.
#[test]
fn the_induction_hypothesis_closes_a_step() {
    let cases: [(&str, &str); 3] = [
        ("theorem totalAtLeast", "omega [totalAtLeast rest y later]"),
        ("theorem stepsAdd", "stepsAdd n (x + 2)"),
        ("theorem sizeMap", "sizeMap rest"),
    ];
    // Each theorem's last `?`: its step's.
    let lines: Vec<usize> = (cases.iter())
        .map(|(marker, _)| {
            let start = RECURSIVE.find(marker).expect("the theorem");
            let end = (RECURSIVE[start..].find("\n\n")).map_or(RECURSIVE.len(), |e| start + e);
            let at = start + RECURSIVE[start..end].rfind('?').expect("a `?`");
            RECURSIVE[..at].matches('\n').count() + 1
        })
        .collect();
    let reports = at_each(RECURSIVE, &lines);
    for (((marker, want), line), report) in cases.iter().zip(&lines).zip(&reports) {
        let recursive: Vec<&str> = (report.results.iter())
            .filter(|s| s.recursive)
            .map(|s| s.proof.as_str())
            .collect();
        assert!(
            recursive.iter().any(|p| p.contains(want)),
            "{marker}: `{want}` not among {recursive:?}\n{report:#?}"
        );
        for s in report.results.iter().filter(|s| s.recursive) {
            assert_eq!(s.checked, "elaborated", "{marker}: {}", s.proof);
        }
        // One each: a check of the file takes a second.
        let first = recursive.iter().find(|p| p.contains(want)).expect("found");
        pastes_at(RECURSIVE, *line, first);
    }
}

/// A rewrite by a hypothesis, then a lemma that closes what it leaves
/// (SW-993; AoC 2021 day 16's `takeAppendLength`).
#[test]
fn a_hypothesis_rewrite_then_a_lemma_closes() {
    let text = "\
import Std (Bool, Nat, List)

theorem takeLength (xs: List Nat) (ys: List Nat) (k: Nat) (h: xs.length = k): (xs ++ ys).take k = xs := ?
";
    let report = &at_each(text, &[3])[0];
    let want = "rewrite <- h in List.takeAppend xs ys";
    assert!(
        (report.results.iter()).any(|s| s.proof == want && s.class == "withHypotheses"),
        "`{want}` not suggested: {report:#?}"
    );
    pastes_at(text, 3, want);
}

/// A conjunct of a theorem whose conclusion is a definition that unfolds
/// to a conjunction (SW-993; std's `Graph.distancesShortest`), nested.
#[test]
fn a_conjunct_of_a_theorem_closes() {
    let text = "\
import Std (Nat, List)

def total: List Nat → Nat
  | Nil => 0
  | Cons x rest => x + total rest

def Bounded (xs: List Nat) (n: Nat): Prop := And (total xs ≤ n) (And (List.length xs ≤ n) (0 < n + 1))

theorem boundedSelf (xs: List Nat): Bounded xs (total xs + List.length xs) := Both (omega) (Both (omega) (omega))

theorem useTotal (ys: List Nat): List.length ys ≤ total ys + List.length ys := ?
";
    let report = &at_each(text, &[11])[0];
    let want = "And.left (And.right (boundedSelf ys))";
    let found = (report.results.iter()).find(|s| s.proof == want);
    assert!(
        found.is_some_and(|s| s.conjunct.as_deref() == Some("right.left")),
        "`{want}` not suggested as the right.left conjunct: {report:#?}"
    );
    pastes_at(text, 11, want);
}

/// SW-1017: a check that would run for minutes is stopped from inside at the
/// deadline `search --at` gives it (a share of its time): here `rfl` on a
/// naive `fib 36`, which takes tens of seconds. It fails as having run out
/// (`E-RESOURCE`), the budget says the deadline stopped it, and the next
/// check, with no deadline, is unaffected.
#[test]
fn a_proof_check_past_its_deadline_is_stopped_from_inside() {
    let text = "\
import Std (Nat)

def fib: Nat → Nat
  | 0 => 0
  | Succ 0 => 1
  | Succ (Succ n) => fib n + fib (Succ n)
";
    with_session(STACK, Session::for_stack, |session| {
        let (_, diagnostics) = load(session, text);
        assert!(
            !diagnostics.iter().any(|d| d.severity == Severity::Error),
            "{diagnostics:?}"
        );
        let limit = std::time::Duration::from_millis(300);
        (session.elab.kernel.machine.budget).set_deadline(Some(std::time::Instant::now() + limit));
        let slow = session
            .parse_expression("<test>", "((rfl): fib 36 = 14930352)")
            .unwrap();
        let started = std::time::Instant::now();
        let stopped = session.elab.check_proof(&slow);
        let took = started.elapsed();
        (session.elab.kernel.machine.budget).set_deadline(None);
        let Err(error) = stopped else {
            panic!("the check can't finish in 300 ms");
        };
        assert_eq!(error.code, "E-RESOURCE", "{error:?}");
        assert!(
            session.elab.kernel.machine.budget.take_timed_out(),
            "the deadline didn't stop it"
        );
        assert!(took < std::time::Duration::from_secs(5), "took {took:?}");
        let quick = session
            .parse_expression("<test>", "((rfl): fib 10 = 55)")
            .unwrap();
        assert!(session.elab.check_proof(&quick).is_ok());
        assert!(!session.elab.kernel.machine.budget.take_timed_out());
    });
}

/// [`options`] answering with the simplest closer alone (SW-2966).
fn simplest() -> AtOptions {
    AtOptions {
        simplest_first: true,
        ..options()
    }
}

/// The only thing offered is `proof`, found by the ladder's `rung`, and it
/// pastes.
fn only_offer(name: &str, rung: &str, proof: &str) {
    let line = line_of(name);
    let report = at_with(GOALS, line, &simplest());
    assert_eq!(report.simplest, Some(rung), "{report:#?}");
    let offered: Vec<&str> = (report.tactics.iter().map(String::as_str))
        .chain(report.results.iter().map(|s| s.proof.as_str()))
        .collect();
    assert_eq!(offered, [proof], "{report:#?}");
    assert!(report.rewrites.is_empty() && report.induction.is_empty());
    assert_eq!(report.budget.candidates, 0, "nothing was searched");
    pastes(GOALS, line, proof);
}

/// A goal `rfl` closes is answered with `rfl` alone, where the full search
/// lists `omega`, `byDecision` and lemmas too.
#[test]
fn simplest_first_offers_only_rfl() {
    only_offer("byComputing", "rfl", "rfl");
    let full = at(GOALS, line_of("byComputing"));
    assert!(full.tactics.len() > 1, "{full:#?}");
}

#[test]
fn simplest_first_offers_a_hypothesis_that_is_the_goal() {
    only_offer("fromHypothesis", "hypothesis", "h");
}

/// A goal only `omega` closes: not `ring`, not `cases`, not lemmas.
#[test]
fn simplest_first_offers_only_omega() {
    only_offer("onlyOmega", "omega", "omega");
}

#[test]
fn simplest_first_offers_ring_when_omega_cannot() {
    only_offer("onlyRing", "ring", "ring");
}

#[test]
fn simplest_first_offers_cases_for_an_impossible_hypothesis() {
    only_offer("ruledOut", "cases", "cases");
}

/// A goal no rung closes gets the full search's offers: the same lemma
/// first as without the ladder, and no `simplest`.
#[test]
fn simplest_first_leaves_the_full_search_when_no_rung_closes() {
    let line = line_of("exactly");
    let report = at_with(GOALS, line, &simplest());
    assert_eq!(report.simplest, None);
    assert_eq!(
        report.results[0].proof, "List.lengthAppend xs ys",
        "{report:#?}"
    );
    assert!(report.budget.candidates > 0);
}
