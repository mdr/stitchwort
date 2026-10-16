//! Groups of definitions that call each other (docs/proposals/mutual-recursion.md
//! §5.3, §5.5, §6, §8.4): admission through `define_group`, termination
//! across members, hashing a group as a unit, and generated groups that must
//! run to an answer whenever they're accepted. These call the kernel
//! directly, in orders the elaborator never uses.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, define_group};
use stitchwort_core::globals::State;
use stitchwort_core::hash::def_hash;
use stitchwort_core::term::Term;
use stitchwort_core::value::{eval, quote};
use stitchwort_core::{DataId, DefId, Globals, Limits, termination};

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

/// `Nat -> … -> Nat` with `n` parameters.
fn nats_to_nat(p: &Prelude, n: usize) -> Term {
    (0..n).fold(p.nat_ty(), |ty, _| arrow(p.nat_ty(), ty))
}

/// `\n -> case n of Zero -> zero; Succ k -> succ`, where `succ` is written
/// with `k` as `v(0)` and `n` as `v(1)`.
fn on_nat(nat: DataId, zero: Term, succ: Term) -> Term {
    lam("n", case(0, nat, vec![(vec![], zero), (vec!["k"], succ)]))
}

/// Declares `name : Nat`.
fn constant(p: &mut Prelude, name: &str) -> DefId {
    let ty = p.nat_ty();
    declare(&mut p.g, name, ty)
}

/// Declares each of `names` as `Nat -> Nat`.
fn declare_all(p: &mut Prelude, names: &[&str]) -> Vec<DefId> {
    let ty = nats_to_nat(p, 1);
    names
        .iter()
        .map(|n| declare(&mut p.g, n, ty.clone()))
        .collect()
}

/// `even` and `odd`, as 1 and 0: `even (Succ k) = odd k`, `odd (Succ k) =
/// even k`.
fn even_odd_bodies(p: &Prelude, even: DefId, odd: DefId) -> Vec<(DefId, Term)> {
    let call = |f: DefId| app(Term::Def(f), [v(0)]);
    vec![
        (even, on_nat(p.nat, p.num(1), call(odd))),
        (odd, on_nat(p.nat, p.num(0), call(even))),
    ]
}

/// Evaluates `f` applied to these numbers, fully, within `work` steps.
fn run(g: &Globals, f: DefId, args: &[usize], work: u64) -> Option<usize> {
    let nat = g.find_data("Nat").unwrap();
    let num = |n: usize| {
        (0..n).fold(Term::ctor(nat, 0, vec![]), |t, _| {
            Term::ctor(nat, 1, vec![t])
        })
    };
    let term = app(Term::Def(f), args.iter().map(|n| num(*n)));
    let _op = g.budget.operation(Limits {
        work,
        ..Limits::default()
    });
    let value = eval(g, &[], &term).ok()?;
    nat_of(&quote(g, 0, &value).ok()?)
}

fn nat_of(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_of(&args[0]).map(|n| n + 1),
        Term::Nat(n) => usize::try_from(&**n).ok(),
        _ => None,
    }
}

fn hash_of(g: &Globals, id: DefId) -> Option<stitchwort_core::hash::ContentHash> {
    let _op = g.budget.operation(Limits::default());
    def_hash(g, id).unwrap()
}

// Admission

#[test]
fn even_and_odd_are_accepted_together() {
    let mut p = Prelude::new();
    let ids = declare_all(&mut p, &["even", "odd"]);
    let bodies = even_odd_bodies(&p, ids[0], ids[1]);
    define_group(&mut p.g, &bodies).unwrap();
    for id in &ids {
        assert_eq!(p.g.def(*id).state, State::Final);
        assert_eq!(p.g.def(*id).group.as_deref(), Some(&ids[..]));
    }
    assert_eq!(run(&p.g, ids[0], &[4], 10_000), Some(1));
    assert_eq!(run(&p.g, ids[1], &[4], 10_000), Some(0));
    assert_eq!(run(&p.g, ids[0], &[7], 10_000), Some(0));
}

#[test]
fn a_cycle_split_into_two_groups_is_refused() {
    // f n = g n; g (Succ k) = f k. Submitted one at a time, `f`'s body
    // refers to `g`, which isn't finished and isn't in its group.
    let mut p = Prelude::new();
    let ids = declare_all(&mut p, &["f", "g"]);
    let (f, g) = (ids[0], ids[1]);
    let f_body = lam("n", app(Term::Def(g), [v(0)]));
    let g_body = on_nat(p.nat, p.num(0), app(Term::Def(f), [v(0)]));
    let e = define_group(&mut p.g, &[(f, f_body.clone())]).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
    assert!(
        e.labels
            .iter()
            .any(|l| l.message.contains("isn't finished")),
        "{e:?}"
    );
    assert_eq!(
        code(define_group(&mut p.g, &[(g, g_body.clone())])),
        "E-FAILED-DEPENDENCY"
    );
    assert_eq!(p.g.def(f).state, State::Failed);
    assert_eq!(p.g.def(g).state, State::Failed);
    // Neighbour: the same two as one group, accepted (`g` makes it smaller).
    let ids = declare_all(&mut p, &["f2", "g2"]);
    let f_body = lam("n", app(Term::Def(ids[1]), [v(0)]));
    let g_body = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    define_group(&mut p.g, &[(ids[0], f_body), (ids[1], g_body)]).unwrap();
}

/// `f → g → h → f`, with `h` making its argument smaller.
fn three_cycle(p: &mut Prelude) -> Vec<(DefId, Term)> {
    let ids = declare_all(p, &["f", "g", "h"]);
    let calls = |to: DefId| lam("n", app(Term::Def(to), [v(0)]));
    vec![
        (ids[0], calls(ids[1])),
        (ids[1], calls(ids[2])),
        (
            ids[2],
            on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)])),
        ),
    ]
}

#[test]
fn incorrect_partitions_of_a_cycle_are_refused() {
    // [f, g] then [h]: the first refers to pending `h`.
    let mut p = Prelude::new();
    let members = three_cycle(&mut p);
    assert_eq!(code(define_group(&mut p.g, &members[..2])), "E-MALFORMED");
    assert_eq!(
        code(define_group(&mut p.g, &members[2..])),
        "E-FAILED-DEPENDENCY"
    );
    assert!(
        members
            .iter()
            .all(|(id, _)| p.g.def(*id).state == State::Failed)
    );
    // [f] then [g, h].
    let mut p = Prelude::new();
    let members = three_cycle(&mut p);
    assert_eq!(code(define_group(&mut p.g, &members[..1])), "E-MALFORMED");
    assert_eq!(
        code(define_group(&mut p.g, &members[1..])),
        "E-FAILED-DEPENDENCY"
    );
    // Neighbour: all three together.
    let mut p = Prelude::new();
    let members = three_cycle(&mut p);
    define_group(&mut p.g, &members).unwrap();
    assert_eq!(run(&p.g, members[0].0, &[5], 10_000), Some(0));
}

#[test]
fn every_member_must_be_pending_and_listed_once() {
    let mut p = Prelude::new();
    // A member that's already final: refused, and the other member fails.
    let ids = declare_all(&mut p, &["even", "odd"]);
    let bodies = even_odd_bodies(&p, ids[0], ids[1]);
    let done = declare_all(&mut p, &["done"])[0];
    define_group(&mut p.g, &[(done, lam("n", v(0)))]).unwrap();
    let e = define_group(&mut p.g, &[bodies[0].clone(), (done, lam("n", v(0)))]).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
    assert_eq!(p.g.def(ids[0]).state, State::Failed);
    assert_eq!(p.g.def(done).state, State::Final);
    // Listed twice.
    let ids = declare_all(&mut p, &["even2", "odd2"]);
    let bodies = even_odd_bodies(&p, ids[0], ids[1]);
    let twice = [bodies[0].clone(), bodies[1].clone(), bodies[0].clone()];
    assert_eq!(code(define_group(&mut p.g, &twice)), "E-MALFORMED");
    assert!(ids.iter().all(|id| p.g.def(*id).state == State::Failed));
    // Empty, or naming a definition that doesn't exist: refused, and
    // nothing changes.
    let before: Vec<State> = p.g.defs.iter().map(|d| d.state).collect();
    assert_eq!(code(define_group(&mut p.g, &[])), "E-MALFORMED");
    let missing = DefId(p.g.defs.len() + 3);
    assert_eq!(
        code(define_group(&mut p.g, &[(missing, lam("n", v(0)))])),
        "E-MALFORMED"
    );
    let after: Vec<State> = p.g.defs.iter().map(|d| d.state).collect();
    assert_eq!(before, after);
    // A member of a failed group can't be submitted again.
    assert_eq!(code(define_group(&mut p.g, &bodies)), "E-MALFORMED");
}

#[test]
fn a_group_can_refer_only_to_its_members_and_final_declarations() {
    let mut p = Prelude::new();
    // A pending data type in a body: refused (there's no group of a data
    // type and a definition).
    let d = data(&mut p.g, "D", vec![], stitchwort_core::Sort::Type(0));
    let ids = declare_all(&mut p, &["f"]);
    let uses_d = lam(
        "n",
        app(
            lam("x", v(1)),
            [Term::Ann(Rc::new(p.num(0)), Rc::new(Term::Data(d, vec![])))],
        ),
    );
    assert_eq!(
        code(define_group(&mut p.g, &[(ids[0], uses_d)])),
        "E-MALFORMED"
    );
    // A pending definition outside the group, from a member of a group of
    // two.
    let outside = declare_all(&mut p, &["outside"])[0];
    let ids = declare_all(&mut p, &["even", "odd"]);
    let mut bodies = even_odd_bodies(&p, ids[0], ids[1]);
    bodies[1].1 = on_nat(
        p.nat,
        app(Term::Def(outside), [p.num(0)]),
        app(Term::Def(ids[0]), [v(0)]),
    );
    let e = define_group(&mut p.g, &bodies).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
    assert!(
        e.labels
            .iter()
            .any(|l| l.message.contains("isn't finished and isn't in this group")),
        "{e:?}"
    );
    assert!(ids.iter().all(|id| p.g.def(*id).state == State::Failed));
}

#[test]
fn a_signature_cannot_mention_a_sibling() {
    // f : (n : Nat) -> g n = g n, with `g` declared and pending.
    let mut p = Prelude::new();
    let g = declare_all(&mut p, &["g"])[0];
    let ty = pi(
        "n",
        p.nat_ty(),
        eq(None, app(Term::Def(g), [v(0)]), app(Term::Def(g), [v(0)])),
    );
    let r = check::declare_def(&mut p.g, &"f".into(), &ty, true, false, span());
    assert_eq!(code(r), "E-MALFORMED");
}

#[test]
fn members_are_opaque_while_their_group_is_checked() {
    // `f`'s body needs `z` to compute to `Zero`:
    // `((\_ -> n) : z = 0 -> Nat) rfl`.
    let mut p = Prelude::new();
    let body_using = |p: &Prelude, z: DefId| {
        let ignore = Term::Ann(
            Rc::new(lam("_", v(1))),
            Rc::new(arrow(eq(None, Term::Def(z), p.num(0)), p.nat_ty())),
        );
        lam("n", app(ignore, [Term::Refl]))
    };
    let z = constant(&mut p, "z");
    let f = declare_all(&mut p, &["f"])[0];
    let members = [(z, p.num(0)), (f, body_using(&p, z))];
    let e = define_group(&mut p.g, &members).unwrap_err();
    assert_eq!(e.code, "E-REFL", "{e:?}");
    assert_eq!(p.g.def(z).state, State::Failed);
    assert_eq!(p.g.def(f).state, State::Failed);
    assert_eq!(hash_of(&p.g, z), None);
    // Neighbour: `z` finished first, in its own group.
    let z = constant(&mut p, "z2");
    let zero = p.num(0);
    define_group(&mut p.g, &[(z, zero)]).unwrap();
    let f = declare_all(&mut p, &["f2"])[0];
    let body = body_using(&p, z);
    define_group(&mut p.g, &[(f, body)]).unwrap();
}

// Termination across members

#[test]
fn a_wrapper_that_passes_its_argument_on_unchanged_is_accepted() {
    // countdown n = step n; step (Succ k) = countdown k.
    let mut p = Prelude::new();
    let ids = declare_all(&mut p, &["countdown", "step"]);
    let wrapper = lam("n", app(Term::Def(ids[1]), [v(0)]));
    let step = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    define_group(&mut p.g, &[(ids[0], wrapper.clone()), (ids[1], step)]).unwrap();
    // Neighbour: without the decrease, refused.
    let ids = declare_all(&mut p, &["ping", "pong"]);
    let pong = lam("n", app(Term::Def(ids[0]), [v(0)]));
    let ping = lam("n", app(Term::Def(ids[1]), [v(0)]));
    let e = define_group(&mut p.g, &[(ids[0], ping), (ids[1], pong)]).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert_eq!(e.message, "can't show that `ping` and `pong` terminate");
}

/// §6.8 example 11: `f (Succ x) y = g x (Succ y)`, `g x (Succ y) = f (Succ
/// (Succ x)) y`.
fn alternating(p: &mut Prelude) -> Vec<(DefId, Term)> {
    let ty = nats_to_nat(p, 2);
    let f = declare(&mut p.g, "f", ty.clone());
    let g = declare(&mut p.g, "g", ty);
    let nat = p.nat;
    let succ = |t: Term| Term::ctor(nat, 1, vec![t]);
    // f: levels x 0, y 1, x' 2.
    let f_body = lam(
        "x",
        lam(
            "y",
            case(
                1,
                nat,
                vec![
                    (vec![], v(0)),
                    (vec!["x'"], app(Term::Def(g), [v(0), succ(v(1))])),
                ],
            ),
        ),
    );
    // g: levels x 0, y 1, y' 2.
    let g_body = lam(
        "x",
        lam(
            "y",
            case(
                0,
                nat,
                vec![
                    (vec![], v(1)),
                    (vec!["y'"], app(Term::Def(f), [succ(succ(v(2))), v(0)])),
                ],
            ),
        ),
    );
    vec![(f, f_body), (g, g_body)]
}

#[test]
fn growth_that_alternates_between_members_is_refused() {
    let mut p = Prelude::new();
    let members = alternating(&mut p);
    let e = define_group(&mut p.g, &members).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert_eq!(e.message, "can't show that `f` and `g` terminate");
    // Each call says where it goes.
    assert!(
        e.labels.iter().any(|l| l.message.contains("call to `g`")),
        "{e:?}"
    );
    assert!(
        e.labels.iter().any(|l| l.message.contains("call to `f`")),
        "{e:?}"
    );
    assert!(
        e.notes
            .iter()
            .any(|n| n.contains("going round `f` → `g` → `f`")),
        "{e:?}"
    );
    assert!(
        members
            .iter()
            .all(|(id, _)| p.g.def(*id).state == State::Failed)
    );
}

#[test]
fn a_member_must_be_given_all_its_arguments() {
    // walk n = applyTo walkList n: `walkList` bare.
    let mut p = Prelude::new();
    let apply_ty = arrow(nats_to_nat(&p, 1), nats_to_nat(&p, 1));
    let apply_to = define(
        &mut p.g,
        "applyTo",
        apply_ty,
        lam("f", lam("x", app(v(1), [v(0)]))),
    )
    .unwrap();
    let ids = declare_all(&mut p, &["walk", "walkList"]);
    let walk = lam("n", app(Term::Def(apply_to), [Term::Def(ids[1]), v(0)]));
    let walk_list = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    let e = define_group(&mut p.g, &[(ids[0], walk), (ids[1], walk_list.clone())]).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert_eq!(
        e.message,
        "`walkList` is used here without all its arguments"
    );
    // Neighbour: `\x -> walkList x` has all its arguments, but `x` isn't
    // smaller than anything, so going round nothing gets smaller.
    let ids = declare_all(&mut p, &["walk2", "walkList2"]);
    let eta = lam("x", app(Term::Def(ids[1]), [v(0)]));
    let walk = lam("n", app(Term::Def(apply_to), [eta, v(0)]));
    let walk_list = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    let e = define_group(&mut p.g, &[(ids[0], walk), (ids[1], walk_list)]).unwrap_err();
    assert_eq!(
        e.message,
        "can't show that `walk2` and `walkList2` terminate"
    );
}

#[test]
fn constants_defined_as_each_other_are_refused() {
    // c = d; d = c: arity zero, so no argument could get smaller.
    let mut p = Prelude::new();
    let c = constant(&mut p, "c");
    let d = constant(&mut p, "d");
    let e = define_group(&mut p.g, &[(c, Term::Def(d)), (d, Term::Def(c))]).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    // Neighbour: one constant defined from the other, no cycle.
    let c = constant(&mut p, "c2");
    let d = constant(&mut p, "d2");
    let three = p.num(3);
    define_group(&mut p.g, &[(c, Term::Def(d)), (d, three)]).unwrap();
    assert_eq!(run(&p.g, c, &[], 1000), Some(3));
}

#[test]
fn a_failed_group_publishes_nothing() {
    let mut p = Prelude::new();
    let members = alternating(&mut p);
    let _ = define_group(&mut p.g, &members);
    for (id, _) in &members {
        assert_eq!(p.g.def(*id).state, State::Failed);
        assert!(p.g.def(*id).body.is_none());
        assert_eq!(hash_of(&p.g, *id), None);
    }
    // Using a member afterwards fails too.
    let f = members[0].0;
    let uses = lam("n", app(Term::Def(f), [v(0), v(0)]));
    let ty = nats_to_nat(&p, 1);
    let r = define(&mut p.g, "uses", ty, uses);
    assert_eq!(r.err(), Some("E-FAILED-DEPENDENCY"));
}

/// `f a b c` whose calls go to `g` with the three arguments in every order
/// and `a` replaced by a part of it, and `g` passing them back unchanged:
/// terminating, but with dozens of graphs in the closure.
fn many_calls(p: &Prelude, f: DefId, g: DefId) -> Vec<(DefId, Term)> {
    let nat = p.nat;
    let perms: [[usize; 3]; 6] = [
        [3, 1, 2],
        [3, 2, 1],
        [1, 3, 2],
        [1, 2, 3],
        [2, 3, 1],
        [2, 1, 3],
    ];
    let level = 4;
    let calls = perms.iter().fold(p.num(0), |acc, perm| {
        app(
            Term::Def(p.add),
            [
                acc,
                app(Term::Def(g), perm.iter().map(|l| v(level - 1 - l))),
            ],
        )
    });
    let f_body = lam(
        "a",
        lam(
            "b",
            lam(
                "c",
                case(2, nat, vec![(vec![], p.num(0)), (vec!["a'"], calls)]),
            ),
        ),
    );
    let g_body = lam(
        "a",
        lam("b", lam("c", app(Term::Def(f), [v(2), v(1), v(0)]))),
    );
    vec![(f, f_body), (g, g_body)]
}

#[test]
fn running_out_while_deciding_a_groups_termination_fails_every_member() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 3);
    // How much checking the two bodies takes on its own.
    let (pf, pg) = (
        declare(&mut p.g, "pf", ty.clone()),
        declare(&mut p.g, "pg", ty.clone()),
    );
    let probe = many_calls(&p, pf, pg);
    let checking = {
        let _op = p.g.budget.operation(Limits::default());
        let before = p.g.budget.total_work();
        for (id, body) in &probe {
            let def = p.g.def(*id);
            let mut cx = check::Ctx::new(&p.g, def.span);
            check::check(&mut cx, body, &def.ty_value).expect("the body type-checks");
        }
        p.g.budget.total_work() - before
    };
    // With enough graphs, it terminates; with too few, inconclusive.
    let (f, g) = (
        declare(&mut p.g, "f", ty.clone()),
        declare(&mut p.g, "g", ty),
    );
    let members = many_calls(&p, f, g);
    for (id, _) in &members {
        p.g.defs[id.0].arity = 3;
    }
    let group: Vec<termination::Member> = members
        .iter()
        .map(|(id, body)| termination::Member { id: *id, body })
        .collect();
    {
        let _op = p.g.budget.operation(Limits::default());
        termination::check_group(&p.g, &group, stitchwort_core::sct::MAX_GRAPHS).unwrap();
        let e = termination::check_group(&p.g, &group, 3).unwrap_err();
        assert_eq!(e.code, "E-RESOURCE");
        assert!(
            e.notes
                .iter()
                .any(|n| n.contains("none of `f`, `g` is accepted")),
            "{e:?}"
        );
    }
    // Through the kernel, running out of steps in the termination check.
    let r = {
        let saved = p.g.budget.start(Limits {
            work: checking + 1,
            ..Limits::default()
        });
        let r = define_group(&mut p.g, &members);
        p.g.budget.restore(saved);
        r
    };
    let e = r.unwrap_err();
    assert_eq!(e.code, "E-RESOURCE");
    assert!(
        e.labels.iter().any(|l| l.message.contains("terminate")),
        "it ran out in the termination check: {e:?}"
    );
    for (id, _) in &members {
        assert_eq!(p.g.def(*id).state, State::Failed);
        assert_eq!(hash_of(&p.g, *id), None);
    }
}

// Hashing

/// `even` and `odd` in a fresh prelude, submitted in the given order, with
/// `odd`'s result type written as `ty`.
fn even_odd_hashes(
    order: [usize; 2],
    odd_result: impl Fn(&mut Prelude) -> Term,
) -> [stitchwort_core::hash::ContentHash; 2] {
    let mut p = Prelude::new();
    let odd_result = odd_result(&mut p);
    let names = ["even", "odd"];
    let mut ids = [DefId(0); 2];
    for &m in &order {
        let ty = if m == 1 {
            arrow(p.nat_ty(), odd_result.clone())
        } else {
            nats_to_nat(&p, 1)
        };
        ids[m] = declare(&mut p.g, names[m], ty);
    }
    let bodies = even_odd_bodies(&p, ids[0], ids[1]);
    let submitted: Vec<(DefId, Term)> = order.iter().map(|m| bodies[*m].clone()).collect();
    define_group(&mut p.g, &submitted).unwrap();
    [
        hash_of(&p.g, ids[0]).unwrap(),
        hash_of(&p.g, ids[1]).unwrap(),
    ]
}

#[test]
fn a_group_is_hashed_as_a_unit() {
    let nat = |p: &mut Prelude| p.nat_ty();
    let hashes = even_odd_hashes([0, 1], nat);
    // Deterministic, and distinct members have distinct hashes.
    assert_eq!(hashes, even_odd_hashes([0, 1], nat));
    assert_ne!(hashes[0], hashes[1]);
    // Members with different shapes are ordered by shape, so submitting (and
    // declaring) them in the other order gives the same hashes.
    assert_eq!(hashes, even_odd_hashes([1, 0], nat));
    // Changing only one member's signature changes every member's hash
    // (`idType Nat` computes to `Nat`, so the bodies still check).
    let id_type = |p: &mut Prelude| {
        let id = define(&mut p.g, "idType", arrow(ty(), ty()), lam("x", v(0))).unwrap();
        app(Term::Def(id), [p.nat_ty()])
    };
    let changed = even_odd_hashes([0, 1], id_type);
    assert_ne!(changed[0], hashes[0]);
    assert_ne!(changed[1], hashes[1]);
}

#[test]
fn members_with_the_same_shape_have_deterministic_distinct_hashes() {
    // f (Succ k) = g k; g (Succ k) = f k, both 0 at zero: the same shape.
    let build = || {
        let mut p = Prelude::new();
        let ids = declare_all(&mut p, &["f", "g"]);
        let call = |to: DefId| app(Term::Def(to), [v(0)]);
        let members = [
            (ids[0], on_nat(p.nat, p.num(0), call(ids[1]))),
            (ids[1], on_nat(p.nat, p.num(0), call(ids[0]))),
        ];
        define_group(&mut p.g, &members).unwrap();
        (
            hash_of(&p.g, ids[0]).unwrap(),
            hash_of(&p.g, ids[1]).unwrap(),
        )
    };
    let (f, g) = build();
    assert_ne!(f, g);
    assert_eq!((f, g), build());
}

#[test]
fn a_hash_covers_what_a_group_calls_outside_it() {
    // even/odd, but `odd 0` is `k`, a final definition outside the group.
    let hashes = |k_value: usize| {
        let mut p = Prelude::new();
        let k = constant(&mut p, "k");
        let value = p.num(k_value);
        define_group(&mut p.g, &[(k, value)]).unwrap();
        let ids = declare_all(&mut p, &["even", "odd"]);
        let mut bodies = even_odd_bodies(&p, ids[0], ids[1]);
        bodies[1].1 = on_nat(p.nat, Term::Def(k), app(Term::Def(ids[0]), [v(0)]));
        define_group(&mut p.g, &bodies).unwrap();
        hash_of(&p.g, ids[0]).unwrap()
    };
    assert_ne!(hashes(0), hashes(1));
}

/// The hash of the prelude's `add`, a single self-recursive definition,
/// as computed before groups were hashed: a single definition's hash is
/// unchanged.
#[test]
fn a_single_recursive_definition_keeps_its_hash() {
    let p = Prelude::new();
    assert_eq!(
        hash_of(&p.g, p.add).unwrap().hex(),
        // Computed with the hasher from before groups (commit a4fa333), then
        // updated when data types' field names were hashed
        // (docs/proposals/records.md §12), which changed `Nat`'s hash; with
        // field names left out, the old value still comes out.
        "1dd1ee02bf1534d9fe5b3bbb7b277bc9fa28032640e6114cc30615d33ae82f00"
    );
}

// Generated groups

/// Groups of two definitions on `Nat`, each of arity 1 or 2, built from:
/// case trees on parameters and fields, variables, `Zero`, `Succ`, `add`,
/// and calls to either member (with all their arguments). Every one
/// type-checks, so whenever the kernel accepts one, every member must run to
/// an answer.
struct Gen {
    rng: u64,
    nat: DataId,
    add: DefId,
    members: [(DefId, usize); 2],
}

impl Gen {
    fn next(&mut self) -> u64 {
        self.rng ^= self.rng >> 12;
        self.rng ^= self.rng << 25;
        self.rng ^= self.rng >> 27;
        self.rng.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn tree(&mut self, level: usize, matchable: &[usize], depth: usize) -> Term {
        // Always a match at the top, so most calls have a field to pass.
        if depth > 0 && (depth == 2 || self.below(4) > 0) {
            let x = matchable[self.below(matchable.len())];
            let zero = self.tree(level, matchable, depth - 1);
            let mut inner = matchable.to_vec();
            inner.push(level);
            let succ = self.tree(level + 1, &inner, depth - 1);
            return case(
                level - 1 - x,
                self.nat,
                vec![(vec![], zero), (vec!["k"], succ)],
            );
        }
        match self.below(6) {
            0 | 1 => self.expr(level, 1),
            2 | 3 => self.call(level, 1),
            4 => app(
                Term::Def(self.add),
                [self.call(level, 1), self.expr(level, 1)],
            ),
            _ => self.expr(level, 2),
        }
    }

    fn call(&mut self, level: usize, depth: usize) -> Term {
        let (f, arity) = self.members[self.below(2)];
        let args: Vec<Term> = (0..arity).map(|_| self.arg(level, depth)).collect();
        app(Term::Def(f), args)
    }

    /// An argument of a call: mostly a variable (often a field of the
    /// nearest match) or a variable rebuilt, sometimes anything.
    fn arg(&mut self, level: usize, depth: usize) -> Term {
        let near = |g: &mut Gen| v(g.below(level.min(2)));
        match self.below(12) {
            0..=5 => near(self),
            6 | 7 => v(self.below(level)),
            8 | 9 => Term::ctor(self.nat, 1, vec![near(self)]),
            _ => self.expr(level, depth),
        }
    }

    fn expr(&mut self, level: usize, depth: usize) -> Term {
        let leaf = depth == 0;
        match self.below(if leaf { 2 } else { 8 }) {
            0 => v(self.below(level)),
            1 => Term::ctor(self.nat, 0, vec![]),
            2 => Term::ctor(self.nat, 1, vec![self.expr(level, depth - 1)]),
            3 | 4 => app(
                Term::Def(self.add),
                [self.expr(level, depth - 1), self.expr(level, depth - 1)],
            ),
            5 | 6 => v(self.below(level)),
            _ => self.call(level, depth - 1),
        }
    }
}

const GROUPS: u64 = 20_000;

#[test]
fn every_accepted_generated_group_runs_to_an_answer() {
    let mut p = Prelude::new();
    let (mut accepted, mut cross) = (0, 0);
    for seed in 1..=GROUPS {
        let arities = [1 + (seed as usize % 2), 1 + (seed as usize / 2 % 2)];
        let types = [nats_to_nat(&p, arities[0]), nats_to_nat(&p, arities[1])];
        let ids = [
            declare(&mut p.g, &format!("f{seed}"), types[0].clone()),
            declare(&mut p.g, &format!("g{seed}"), types[1].clone()),
        ];
        let mut generator = Gen {
            rng: seed.wrapping_mul(0x9e37_79b9_7f4a_7c15),
            nat: p.nat,
            add: p.add,
            members: [(ids[0], arities[0]), (ids[1], arities[1])],
        };
        let bodies: Vec<(DefId, Term)> = (0..2)
            .map(|m| {
                let arity = arities[m];
                let params: Vec<usize> = (0..arity).collect();
                let tree = generator.tree(arity, &params, 2);
                let body = (0..arity).fold(tree, |b, i| lam(&format!("p{}", arity - 1 - i), b));
                (ids[m], body)
            })
            .collect();
        let calls_other = |m: usize| mentions(&bodies[m].1, ids[1 - m]);
        let is_cross = calls_other(0) && calls_other(1);
        if define_group(&mut p.g, &bodies).is_ok() {
            accepted += 1;
            cross += usize::from(is_cross);
            for (m, &id) in ids.iter().enumerate() {
                for input in 0..3usize.pow(arities[m] as u32) {
                    let args: Vec<usize> = (0..arities[m])
                        .map(|i| input / 3usize.pow(i as u32) % 3)
                        .collect();
                    assert!(
                        run(&p.g, id, &args, 1_000_000).is_some(),
                        "seed {seed}: accepted, but member {m} on {args:?} didn't finish: \
                         {}\n{}",
                        stitchwort_core::pretty::term(&p.g, &[], &bodies[0].1),
                        stitchwort_core::pretty::term(&p.g, &[], &bodies[1].1),
                    );
                }
            }
        }
    }
    eprintln!("{accepted} of {GROUPS} groups accepted, {cross} with calls both ways");
    // The test means something only if plenty of real cycles are accepted.
    assert!(cross >= 200, "{cross}");
}

/// Whether `term` mentions `f`.
fn mentions(term: &Term, f: DefId) -> bool {
    if matches!(term, Term::Def(id) if *id == f) {
        return true;
    }
    let mut found = false;
    term.for_each_child(|child, _| found |= mentions(child, f));
    found
}

// Partial applications (§6.3)

#[test]
fn an_alias_between_members_is_refused() {
    // f = g, with `g (Succ k) = f k`: `g` takes 1 argument and is given none.
    let mut p = Prelude::new();
    let ids = declare_all(&mut p, &["f", "g"]);
    let g_body = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    let e = define_group(&mut p.g, &[(ids[0], Term::Def(ids[1])), (ids[1], g_body)]).unwrap_err();
    assert_eq!(e.message, "`g` is used here without all its arguments");
    // Neighbour: f n = g n.
    let ids = declare_all(&mut p, &["f2", "g2"]);
    let g_body = on_nat(p.nat, p.num(0), app(Term::Def(ids[0]), [v(0)]));
    let f_body = lam("n", app(Term::Def(ids[1]), [v(0)]));
    define_group(&mut p.g, &[(ids[0], f_body), (ids[1], g_body)]).unwrap();
}

/// `f{name}` with the body `f_body(g)`, and `g{name} x (Succ y) = f{name}
/// y`, which decreases only its second argument, as one group.
fn decreasing_second(
    p: &mut Prelude,
    name: &str,
    f_body: &dyn Fn(DefId) -> Term,
) -> Result<(), stitchwort_syntax::Diagnostic> {
    let ty = nats_to_nat(p, 1);
    let f = declare(&mut p.g, &format!("f{name}"), ty);
    let ty = nats_to_nat(p, 2);
    let g = declare(&mut p.g, &format!("g{name}"), ty);
    // g: levels x 0, y 1, y' 2.
    let g_body = lam(
        "x",
        lam(
            "y",
            case(
                0,
                p.nat,
                vec![(vec![], p.num(0)), (vec!["y'"], app(Term::Def(f), [v(0)]))],
            ),
        ),
    );
    let members = [(f, f_body(g)), (g, g_body)];
    define_group(&mut p.g, &members)
}

#[test]
fn leaving_out_the_only_decreasing_argument_is_refused() {
    // `h fn = fn 0` is a final helper.
    let mut p = Prelude::new();
    let h_ty = arrow(nats_to_nat(&p, 1), p.nat_ty());
    let h_body = lam("fn", app(v(0), [p.num(0)]));
    let h = define(&mut p.g, "h", h_ty, h_body).unwrap();
    let (zero, nat) = (p.num(0), p.nat);
    // f t = h (g 0): refused by saturation.
    let partial = |g: DefId| lam("t", app(Term::Def(h), [app(Term::Def(g), [zero.clone()])]));
    let e = decreasing_second(&mut p, "1", &partial).unwrap_err();
    assert_eq!(e.message, "`g1` is used here without all its arguments");
    // f t = h (\x -> g 0 x): saturated, but `x` is unrelated to anything,
    // so there's no arc into `g`'s decreasing position.
    let eta = |g: DefId| {
        lam(
            "t",
            app(
                Term::Def(h),
                [lam("x", app(Term::Def(g), [zero.clone(), v(0)]))],
            ),
        )
    };
    let e = decreasing_second(&mut p, "2", &eta).unwrap_err();
    assert_eq!(e.message, "can't show that `f2` and `g2` terminate");
    // Neighbour: leave out the *other* argument instead. f (Succ k) =
    // h (\n -> g n k), where `k` is smaller.
    let other = |g: DefId| {
        let call = lam("n", app(Term::Def(g), [v(0), v(1)]));
        lam(
            "t",
            case(
                0,
                nat,
                vec![
                    (vec![], zero.clone()),
                    (vec!["k"], app(Term::Def(h), [call])),
                ],
            ),
        )
    };
    decreasing_second(&mut p, "3", &other).unwrap();
}
