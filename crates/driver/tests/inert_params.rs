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
