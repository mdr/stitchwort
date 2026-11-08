//! The handler clause kinds of docs/proposals/operations-in-place.md §2.3
//! (stage A, `stitchwort_rt::clauses`): the handlers of `Std.Parse`,
//! `Std.Fail` and `Std.Each`, and the shapes of `effect-state.sw` and
//! `effect-handlers.sw`; and the census over std, `aoc/` and the AoC
//! programs of `bench/compare`, which the note reports.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

use stitchwort_core::{DefId, Ev, Term};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::{DiskFiles, Target, analyse, project_sources};
use stitchwort_rt::clauses::{
    Census, Classified, Fold, ForwardShape, Found, Kind, Position, census,
};

const STACK: usize = 256 * 1024 * 1024;

use Kind::{Abort, Forward, General, Tail};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn find(g: &Ev, name: &str) -> DefId {
    (0..g.env.defs().len())
        .map(DefId)
        .rfind(|id| &**g.def(*id).name() == name)
        .unwrap_or_else(|| panic!("no definition `{name}`"))
}

/// The folds of `name`'s generic body, then of its empty-row variant.
fn folds(g: &Ev, name: &str) -> (Vec<Found>, Vec<Found>) {
    let found = census(g, &[find(g, name)]).expect("census");
    found.into_iter().partition(|f| !f.variant)
}

/// The one fold of `name`'s generic body.
fn only(g: &Ev, name: &str) -> (Classified, Position) {
    let (generic, _) = folds(g, name);
    let [found] = &generic[..] else {
        panic!("{name}: {} folds", generic.len());
    };
    let classified = found
        .classified
        .clone()
        .unwrap_or_else(|| panic!("{name}: the step isn't recognised"));
    (classified, found.position)
}

fn check(g: &Ev, name: &str, state: bool, forward: ForwardShape, kinds: &[Kind]) -> Position {
    let (c, position) = only(g, name);
    assert_eq!(c.clauses, kinds, "{name}");
    assert_eq!(c.state, state, "{name}: state");
    assert_eq!(c.forward, forward, "{name}: forward");
    position
}

/// Uses the handlers, so that the library loads them.
const USES: &str = "import Std (Parse, Fail, Each, Option, Result, Text, List, Nat)
def p1(): {Parse} Option Nat := Parse.optional (() => Parse.label \"x\" (() => Parse.nat()))
def p2(): {Parse} Nat := Parse.sectionLine (() => Parse.labelWhole \"y\" (() => Parse.nat()))
def p3(): {Parse} Option (Nat, Bool) := Parse.attempt (() => Parse.nat())
def p4: Result Nat Parse.Failure := Parse.run ['1'] (() => Parse.nat())
def p5: Result (Option Nat) Text := Fail.toResult (() => Fail.toOption (() => Fail.orElse 0 (() => 1)))
def p6: List Nat := Each.collect (() => Each.each [1, 2])
";

#[test]
fn std_handler_clauses() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session.use_test_std_cache();
        session
            .load("uses.sw", USES)
            .unwrap_or_else(|e| panic!("{e:?}"));
        let g = &session.elab.ev();
        // `span`, `next`, `literal`, `mark`, `reset`, `note`, `stop`, `fatal`.
        let readers = [Forward, Forward, Forward, Forward, Forward, Forward];
        let backtracking = [&readers[..], &[Abort, Abort]].concat();
        for name in [
            "Parse.optionalFrom",
            "Parse.attemptFrom",
            "Parse.sectionLineFrom",
        ] {
            let at = check(g, name, false, ForwardShape::Plain, &backtracking);
            assert_eq!(at, Position::Consuming, "{name}");
        }
        // `note` resumes in either branch of an `if`, once with an outer
        // `note` first.
        check(
            g,
            "Parse.labelFrom",
            false,
            ForwardShape::Plain,
            &[&readers[..5], &[Tail, Abort, Abort]].concat(),
        );
        // A state handler at the closed empty row, run as a loop: every
        // reading clause jumps (`next`'s and `literal`'s through their
        // `match`es), `stop` and `fatal` give an `Err`. The fold is the body
        // of a `runPure`, which is a `let`'s value (`let go := …; go
        // initial`).
        let at = check(
            g,
            "Parse.runFrom",
            true,
            ForwardShape::Plain,
            &[Tail, Tail, Tail, Tail, Tail, Tail, Abort, Abort],
        );
        assert_eq!(at, Position::Consuming);
        // A state handler at `{Parse}`, not fused: each resumption is
        // under the state's lambda.
        check(
            g,
            "Parse.labelWholeFrom",
            false,
            ForwardShape::Plain,
            &[
                General, General, General, General, General, General, Abort, Abort,
            ],
        );
        // `Fail`'s open-row handlers go through `foldCompD` at the row's
        // divergence index, a variable in the generic body.
        for name in [
            "Fail.toResult",
            "Fail.toOption",
            "Fail.orElse",
            "Fail.recover",
            "Fail.context",
        ] {
            let (c, _) = only(g, name);
            assert_eq!(c.clauses, [Abort], "{name}");
            assert_eq!(c.fold, Fold::IndexedVariable, "{name}");
            assert_eq!(c.forward, ForwardShape::Divergence, "{name}");
        }
        // Its empty-row variant: `foldComp` itself, with nothing to forward
        // to.
        let (_, variant) = folds(g, "Fail.toResult");
        let [found] = &variant[..] else {
            panic!("Fail.toResult's variant: {} folds", variant.len());
        };
        let c = found.classified.as_ref().expect("recognised");
        assert_eq!((c.fold, &c.clauses[..]), (Fold::Comp, &[Abort][..]));
        // `fork` resumes twice, under `both`'s lambda.
        check(
            g,
            "Each.collect",
            false,
            ForwardShape::Plain,
            &[General, Abort],
        );
    });
}

fn example(name: &str) -> Session {
    let text = std::fs::read_to_string(repo().join("examples/extract").join(name))
        .expect("readable example");
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load(name, &text)
        .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
    session
}

#[test]
fn example_handler_clauses() {
    with_stack(STACK, || {
        let session = example("effect-state.sw");
        let g = &session.elab.ev();
        // `tick`, `stop`, `both`, `many`, `branch`, `mixed`: fused at the
        // closed empty row, as `state_handlers_run_as_a_loop_where_they_fit`
        // finds.
        let tally = [Tail, Abort, General, General, Tail, General];
        check(g, "Tally.run", true, ForwardShape::Plain, &tally);
        // At an open row the generic body isn't fused; its empty-row
        // variant is.
        check(
            g,
            "Tally.runIn",
            false,
            ForwardShape::Divergence,
            &[General, Abort, General, General, General, General],
        );
        let (_, variant) = folds(g, "Tally.runIn");
        let c = variant[0].classified.as_ref().expect("recognised");
        assert!(c.state, "Tally.runIn's variant is fused");
        assert_eq!(c.clauses, tally);
        // `get` and `put` jump. `keep`'s `put` is `k ()`, not `Done` of a
        // function, so fusion leaves the fold alone: `put` resumes as its
        // last step, and `get`'s `k` is under the state's lambda.
        check(g, "Store.run", true, ForwardShape::Plain, &[Tail, Tail]);
        check(
            g,
            "Store.keep",
            false,
            ForwardShape::Plain,
            &[General, Tail],
        );
        check(g, "Offer.counted", false, ForwardShape::Plain, &[General]);
        // A reader at an open row: `k value`.
        check(g, "Env.give", false, ForwardShape::Divergence, &[Tail]);

        let session = example("effect-handlers.sw");
        let g = &session.elab.ev();
        check(g, "Env.give", false, ForwardShape::Plain, &[Tail]);
        check(g, "Tick.ignore", false, ForwardShape::Divergence, &[Tail]);
        check(g, "Counter.number", true, ForwardShape::Plain, &[Tail]);
        let (c, _) = only(g, "Pick.all");
        assert!(c.clauses.contains(&General), "Pick.all: {:?}", c.clauses);
    });
}

/// Every definition `roots` reach, through the definitions their run
/// bodies mention.
fn reachable(g: &Ev, roots: &[DefId]) -> Vec<DefId> {
    let mut seen: BTreeSet<DefId> = roots.iter().copied().collect();
    let mut pending: Vec<DefId> = roots.to_vec();
    while let Some(id) = pending.pop() {
        let Some(body) = g.def(id).run_body() else {
            continue;
        };
        for (t, _) in body.subterms() {
            if let Term::Def(d) = t
                && seen.insert(*d)
            {
                pending.push(*d);
            }
        }
    }
    seen.into_iter().collect()
}

fn show(title: &str, found: &[&Found]) {
    let mut c = Census::default();
    for f in found {
        c.add(f);
    }
    eprintln!(
        "{title}: {} folds ({} unrecognised, {} fused state), clauses {:?}, state clauses {:?}, \
         folds {:?}, forwards {:?}, positions {:?}",
        c.folds,
        c.unrecognised,
        c.state,
        c.clauses,
        c.state_clauses,
        c.by_fold,
        c.by_forward,
        c.by_position
    );
}

/// The census of clause kinds that operations-in-place.md's "Stage A
/// census" reports: over every library definition, the `aoc/` project and
/// the AoC programs of `bench/compare`, the generic bodies and empty-row
/// variants the runtime lowers. Ignored by default: it loads all of `aoc/`
/// (through its check cache, about a minute warm). Run with
/// `task test:one -- clause_census --run-ignored only --no-capture`.
#[test]
#[ignore = "loads all of aoc/; run by hand for the note's census"]
fn clause_census() {
    with_stack(STACK, || {
        let start = Instant::now();
        let mut session = Session::eager_for_stack(STACK);
        let aoc = repo().join("aoc");
        session.use_check_cache(&aoc.join(".stitchwort/cache"));
        let files = DiskFiles { root: aoc.clone() };
        session.include_from(Rc::new(DiskFiles { root: aoc.clone() }));
        let sources = project_sources(&files, "aoc", &mut session.sources)
            .unwrap_or_else(|e| panic!("{e:?}"));
        let analysis = analyse(&mut session, "aoc", sources);
        // A namespace with an error still keeps the declarations that
        // checked, which is all the census needs.
        if let Err(errors) = session.load_analysis("aoc", analysis, &Target::Everything) {
            let files: BTreeSet<String> = errors
                .iter()
                .filter_map(|d| d.labels.first())
                .map(|l| session.sources.get(l.span.file).name.clone())
                .collect();
            eprintln!("{} errors loading aoc/, in {files:?}", errors.len());
        }
        eprintln!("loaded in {:.1?}", start.elapsed());
        let g = &session.elab.ev();
        let all: Vec<DefId> = (0..g.env.defs().len()).map(DefId).collect();
        let found = census(g, &all).expect("census");
        eprintln!("classified in {:.1?}", start.elapsed());
        let path = |f: &Found| g.def(f.def).path().to_string();
        let std: Vec<&Found> = found
            .iter()
            .filter(|f| path(f).starts_with("Std."))
            .collect();
        let aoc: Vec<&Found> = found
            .iter()
            .filter(|f| path(f).starts_with("Aoc."))
            .collect();
        show("std", &std);
        show("aoc", &aoc);
        // Each handler of the library, its kinds.
        let mut named: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for f in &std {
            let entry = match &f.classified {
                Some(c) => format!(
                    "{}{:?} {:?} {:?}{} {:?}",
                    if f.variant { "variant " } else { "" },
                    c.fold,
                    c.forward,
                    c.clauses,
                    if c.state { " state" } else { "" },
                    f.position
                ),
                None => format!("unrecognised {:?}", f.position),
            };
            named.entry(path(f)).or_default().push(entry);
        }
        for (name, entries) in &named {
            eprintln!("  {name}: {}", entries.join("; "));
        }
        // AoC handlers that aren't Forward, Tail or Abort throughout.
        for f in &aoc {
            if let Some(c) = &f.classified
                && c.clauses.contains(&General)
            {
                eprintln!(
                    "  aoc General: {}{} {:?}{}",
                    path(f),
                    if f.variant { " (variant)" } else { "" },
                    c.clauses,
                    if c.state { " state" } else { "" }
                );
            }
        }
        let programs = std::fs::read_to_string(repo().join("bench/compare/programs.toml"))
            .expect("programs.toml");
        let mut program = String::new();
        for line in programs.lines() {
            if let Some(name) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
                program = name.to_string();
            }
            let Some(main) = line
                .strip_prefix("stitchwort = \"")
                .and_then(|l| l.strip_suffix('"'))
            else {
                continue;
            };
            if !main.starts_with("Aoc.") {
                continue;
            }
            let reach: BTreeSet<DefId> = reachable(g, &[find_path(g, main)]).into_iter().collect();
            let used: Vec<&Found> = found.iter().filter(|f| reach.contains(&f.def)).collect();
            let handlers: BTreeSet<String> = used.iter().map(|f| path(f)).collect();
            show(&format!("{program} ({main})"), &used);
            eprintln!(
                "    handlers: {}",
                handlers.into_iter().collect::<Vec<_>>().join(", ")
            );
        }
        eprintln!("done in {:.1?}", start.elapsed());
    });
}

fn find_path(g: &Ev, path: &str) -> DefId {
    (0..g.env.defs().len())
        .map(DefId)
        .rfind(|id| &**g.def(*id).path() == path)
        .unwrap_or_else(|| panic!("no definition `{path}`"))
}
