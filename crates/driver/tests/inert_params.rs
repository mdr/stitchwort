//! The inert proof parameters the kernel computes for the standard library
//! (`stitchwort_core::inert`; docs/proposals/proof-irrelevance.md §7.3).
//! Comparison skips an inert argument, so a mark that isn't justified could
//! equate calls that compute differently: the marks are checked by the
//! reference validator, natives must not read them, and the listing pins
//! what the motivating definitions get.

use std::collections::BTreeSet;

use stitchwort_core::inert::{self, Why};
use stitchwort_core::{DefId, Ev};
use stitchwort_driver::driver::Session;

fn find(g: &Ev, name: &str) -> DefId {
    DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == name)
            .unwrap_or_else(|| panic!("no `{name}` in the library")),
    )
}

/// Every final definition's group, once each, in order.
fn groups(g: &Ev) -> Vec<Vec<DefId>> {
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for (i, def) in g.env.defs().iter().enumerate() {
        if seen.contains(&i) || def.body().is_none() {
            continue;
        }
        let ids: Vec<DefId> = match def.group() {
            Some(group) => group.to_vec(),
            None => vec![DefId(i)],
        };
        seen.extend(ids.iter().map(|d| d.0));
        out.push(ids);
    }
    out
}

fn why(g: &Ev, why: &Why) -> String {
    match why {
        Why::NotInert(f, k) => format!("argument {k} of `{}`", g.env.defs()[f.0].name()),
        other => format!("{other:?}"),
    }
}

/// The listing §7.3 asks for: every definition with a proof parameter
/// below its arity, its marks, and why each cleared one was cleared. Run
/// with `--nocapture` to read it. Recomputing the analysis must give the
/// marks installed.
#[test]
fn the_library_listing() {
    let session = Session::eager();
    let g = &session.elab.ev();
    let mut listing = String::new();
    for ids in groups(g) {
        let (marks, cleared) = inert::analyse(g, &ids).expect("within budget");
        for (id, marks) in ids.iter().zip(&marks) {
            let def = &g.env.defs()[id.0];
            assert_eq!(def.inert_params(), &marks[..], "`{}`", def.name());
            let candidates = inert::candidates(g, *id).expect("within budget");
            if !candidates.iter().any(|c| *c) {
                continue;
            }
            listing.push_str(&format!("{} {:?}", def.name(), marks));
            for c in cleared.iter().filter(|c| c.def == *id) {
                listing.push_str(&format!("; {} cleared: {}", c.param, why(g, &c.why)));
            }
            listing.push('\n');
        }
    }
    println!("{listing}");
    let inert = |name: &str, param: usize| g.def(find(g, name)).is_inert(param);
    // The motivating definitions keep their masks (§7.3's table).
    assert!(inert("Void.absurd", 1));
    assert!(inert("Nat.div", 2));
    assert!(inert("Nat.mod", 2));
    assert!(inert("Int.modNat", 2));
    assert!(inert("Fin.ofNatLt", 2));
}

/// Every mark in the library passes the reference evaluator's independent
/// validator (which also runs on every group admitted in a test build).
#[test]
fn the_reference_validator_accepts_the_library() {
    let session = Session::eager();
    let g = &session.elab.ev();
    for ids in groups(g) {
        stitchwort_core::reference::validate_inert(g, &ids);
    }
}

/// A native runs its implementation, not the body its marks come from, so
/// it must never read an argument at an inert position (§7.10's call step).
/// A native reads its first `numbers()` arguments; the float primitives and
/// natives read all of theirs, so they may have no inert position at all.
#[test]
fn natives_never_read_inert_positions() {
    let session = Session::eager();
    let g = &session.elab.ev();
    for (i, def) in g.env.defs().iter().enumerate() {
        let id = DefId(i);
        let first_inert = def.inert_params().iter().position(|m| *m);
        if let Some(native) = g.env.builtins().native(id) {
            assert!(
                first_inert.is_none_or(|p| p >= native.numbers()),
                "native `{}` reads its inert parameter {first_inert:?}",
                def.name()
            );
        }
        if g.env.builtins().float_bound(id) {
            assert_eq!(
                first_inert,
                None,
                "float definition `{}` has an inert parameter",
                def.name()
            );
        }
    }
}

/// One definition for each rule of the analysis (§7.1), to keep or to
/// clear a mark, with the reason it's cleared.
const RULES: &str = r#"
import Std (Nat, Void)

type Box (a: Prop): Type =
  | MkBox (h: a)

type PBox (a: Prop) (h: a): Type =
  | MkPBox

def passOn (n: Nat) (h: 0 ≠ n): Nat := n
def toInert (n: Nat) (h: 0 ≠ n): Nat := passOn n h
def inLetType (n: Nat) (h: 0 ≠ n): Nat :=
  let k: PBox (0 ≠ n) h := MkPBox
  n
def absurdly (h: 0 ≠ 0): Nat := Void.absurd (h rfl)
def ignored (n: Nat) (h: 0 = 0): Nat := n

def takenApart (h: 0 = 0): Nat := J (y e => Nat) 0 h
def applied (h: 0 ≠ 0): Void := h rfl
def returned (h: 0 = 0): 0 = 0 := h
def stored (h: 0 = 0): Box (0 = 0) := MkBox h
def toLocal (h: 0 = 0): Box (0 = 0) := (x => MkBox x) h
def toRelevant (h: 0 = 0): Box (0 = 0) := stored h
def letValue (h: 0 = 0): Nat :=
  let k := h
  0
def inType (h: 0 = 0): Type := PBox (0 = 0) h

-- An alias hiding the proof's arrow: `hidden`'s arity is 1 (its body binds
-- `h`), and its type is a `Pi` only once the alias unfolds.
def Hides: Type := 0 = 0 → Nat
def hidden: Hides := h => 0
"#;

#[test]
fn each_rule_keeps_or_clears_a_mark() {
    let mut session = Session::eager();
    session.load("rules.sw", RULES).expect("loads");
    let g = &session.elab.ev();
    let marks = |name: &str| g.def(find(g, name)).inert_params().to_vec();
    // Kept: passed only to an inert position, in a `let`'s type, the
    // scrutinee of an impossible `case`, or unused.
    assert_eq!(marks("passOn"), [false, true]);
    assert_eq!(marks("toInert"), [false, true]);
    assert_eq!(marks("inLetType"), [false, true]);
    assert_eq!(marks("absurdly"), [true]);
    assert_eq!(marks("ignored"), [false, true]);
    // The alias unfolds while the candidates are found, so `h` is one.
    assert_eq!(marks("hidden"), [true]);
    // Cleared, each for its reason.
    let why_cleared = |name: &str| {
        let id = find(g, name);
        let (_, cleared) = inert::analyse(g, &[id]).expect("within budget");
        assert_eq!(
            g.def(id).inert_params().iter().filter(|m| **m).count(),
            0,
            "`{name}`"
        );
        cleared.into_iter().map(|c| c.why).collect::<Vec<_>>()
    };
    assert_eq!(why_cleared("takenApart"), [Why::JProof]);
    assert_eq!(why_cleared("applied"), [Why::Applied]);
    assert_eq!(why_cleared("returned"), [Why::Returned]);
    assert_eq!(why_cleared("stored"), [Why::Field]);
    assert_eq!(why_cleared("toLocal"), [Why::LocalFunction]);
    assert_eq!(
        why_cleared("toRelevant"),
        [Why::NotInert(find(g, "stored"), 0)]
    );
    assert_eq!(why_cleared("letValue"), [Why::LetValue]);
    assert_eq!(why_cleared("inType"), [Why::Type]);
}

/// Every mark in the library sits on a parameter whose type is a
/// proposition, below the definition's arity.
#[test]
fn marks_sit_on_proof_parameters() {
    let session = Session::eager();
    let g = &session.elab.ev();
    for (i, def) in g.env.defs().iter().enumerate() {
        if !def.inert_params().iter().any(|m| *m) {
            continue;
        }
        let candidates = inert::candidates(g, DefId(i)).expect("within budget");
        assert_eq!(def.inert_params().len(), def.arity(), "`{}`", def.name());
        for (k, mark) in def.inert_params().iter().enumerate() {
            assert!(!mark || candidates[k], "`{}`'s parameter {k}", def.name());
        }
    }
}

/// The validator refuses a mark the body doesn't justify.
#[test]
#[should_panic(expected = "is marked inert")]
fn the_validator_refuses_an_unjustified_mark() {
    let mut session = Session::eager();
    session.load("rules.sw", RULES).expect("loads");
    let id = find(&session.elab.ev(), "stored");
    session
        .elab
        .kernel
        .env
        .def_mut_for_tests(id)
        .set_inert_params_unchecked_for_tests([true].into());
    stitchwort_core::reference::validate_inert(&session.elab.kernel.ev(), &[id]);
}
