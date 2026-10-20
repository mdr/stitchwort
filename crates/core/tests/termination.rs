//! The termination checker (`stitchwort_core::termination`), on hand-built
//! core terms: size-change termination for single definitions, the
//! definition-entry arity contract and the saturation rule
//! (docs/proposals/mutual-recursion.md §5.3, §6.2, §6.3), and a comparison
//! with the structural checker it replaced on generated programs.

mod common;
mod structural;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, define_def};
use stitchwort_core::hash::def_hash;
use stitchwort_core::term::{NumArm, Term};
use stitchwort_core::value::{eval, quote};
use stitchwort_core::{BigUint, DefId, Globals, Icit, Limits, termination};

/// `Nat -> … -> Nat` with `n` parameters.
fn nats_to_nat(p: &Prelude, n: usize) -> Term {
    (0..n).fold(p.nat_ty(), |ty, _| arrow(p.nat_ty(), ty))
}

/// Declares `name : ty` and defines it with a body that may refer to itself,
/// returning the error if the kernel refuses it.
fn define_rec(
    p: &mut Prelude,
    name: &str,
    ty: Term,
    body: impl FnOnce(Term) -> Term,
) -> Result<DefId, stitchwort_syntax::Diagnostic> {
    let id = declare(&mut p.g, name, ty);
    define_def(&mut p.g, id, &body(Term::Def(id)))?;
    Ok(id)
}

/// `applyTo : (Nat -> Nat) -> Nat -> Nat; applyTo f x = f x`.
fn apply_to(p: &mut Prelude) -> DefId {
    let ty = arrow(nats_to_nat(p, 1), nats_to_nat(p, 1));
    define(
        &mut p.g,
        "applyTo",
        ty,
        lam("f", lam("x", app(v(1), [v(0)]))),
    )
    .unwrap()
}

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

fn zero(p: &Prelude) -> Term {
    Term::ctor(p.nat, 0, vec![])
}

/// Evaluates `f` applied to these numbers, fully.
fn run(g: &Globals, f: DefId, args: &[usize], work: u64) -> Option<Term> {
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
    quote(g, 0, &value).ok()
}

fn nat_of(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_of(&args[0]).map(|n| n + 1),
        Term::Nat(n) => usize::try_from(&**n).ok(),
        _ => None,
    }
}

// Newly accepted: size change

#[test]
fn accepts_ackermann() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    // ack m n = case m of
    //   Zero -> Succ n
    //   Succ m' -> case n of
    //     Zero -> ack m' 1
    //     Succ n' -> ack m' (ack (Succ m') n')
    let (one, nat) = (p.num(1), p.nat);
    let body = |f: Term| {
        // Levels: m 0, n 1, m' 2, n' 3.
        lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (vec![], Term::ctor(nat, 1, vec![v(0)])),
                        (
                            vec!["m'"],
                            case(
                                1,
                                nat,
                                vec![
                                    (vec![], app(f.clone(), [v(0), one])),
                                    (
                                        vec!["n'"],
                                        app(
                                            f.clone(),
                                            [v(1), app(f, [Term::ctor(nat, 1, vec![v(1)]), v(0)])],
                                        ),
                                    ),
                                ],
                            ),
                        ),
                    ],
                ),
            ),
        )
    };
    let ack = define_rec(&mut p, "ack", ty, body).expect("Ackermann's function terminates");
    let result = run(&p.g, ack, &[2, 3], 10_000_000).expect("ack 2 3 runs");
    assert_eq!(nat_of(&result), Some(9));
}

#[test]
fn accepts_swapped_arguments() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    // f x y = case x of Zero -> y; Succ x' -> f y x'
    let nat = p.nat;
    let body = |f: Term| {
        lam(
            "x",
            lam(
                "y",
                case(
                    1,
                    nat,
                    vec![(vec![], v(0)), (vec!["x'"], app(f, [v(1), v(0)]))],
                ),
            ),
        )
    };
    let id = define_rec(&mut p, "swap", ty, body);
    assert!(id.is_ok(), "{id:?}");
}

/// A call that keeps one argument (the parameter itself, or the value it
/// was matched as, rebuilt) while another gets smaller, alongside a call
/// that does the opposite: no one position gets smaller in every call.
#[test]
fn accepts_calls_that_keep_an_argument_while_another_gets_smaller() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    // f m n = case m of
    //   Zero -> case n of Zero -> 0; Succ n' -> f Zero n'    (Zero is m, rebuilt)
    //   Succ m' -> f m' n                                    (n is the parameter)
    let nat = p.nat;
    let z = zero(&p);
    let body = |f: Term| {
        lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (
                            vec![],
                            case(
                                0,
                                nat,
                                vec![
                                    (vec![], z.clone()),
                                    (vec!["n'"], app(f.clone(), [z.clone(), v(0)])),
                                ],
                            ),
                        ),
                        (vec!["m'"], app(f, [v(0), v(1)])),
                    ],
                ),
            ),
        )
    };
    let id = define_rec(&mut p, "both", ty, body);
    assert!(id.is_ok(), "{id:?}");
}

// Must reject

#[test]
fn rejects_alternating_growth() {
    // f x y = case x of
    //   Zero -> case y of Zero -> 0; Succ y' -> f (Succ (Succ y')) y'
    //   Succ x' -> f x' (Succ (Succ y))
    // Each call makes one argument smaller and grows the other, in turn:
    // `f 1 0 → f 0 2 → f 3 1 → f 2 3 → …`. Merging the two calls' graphs
    // would accept it.
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    let nat = p.nat;
    let ss = |t: Term| Term::ctor(nat, 1, vec![Term::ctor(nat, 1, vec![t])]);
    let z = zero(&p);
    let body = |f: Term| {
        lam(
            "x",
            lam(
                "y",
                case(
                    1,
                    nat,
                    vec![
                        (
                            vec![],
                            case(
                                0,
                                nat,
                                vec![(vec![], z), (vec!["y'"], app(f.clone(), [ss(v(0)), v(0)]))],
                            ),
                        ),
                        (vec!["x'"], app(f, [v(0), ss(v(1))])),
                    ],
                ),
            ),
        )
    };
    let e = define_rec(&mut p, "bounce", ty, body).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert_eq!(e.labels.len(), 2, "both calls are shown: {e:?}");
}

#[test]
fn rejects_swapped_arguments_when_nothing_gets_smaller() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    let e = define_rec(&mut p, "swap", ty, |f| {
        lam("x", lam("y", app(f, [v(0), v(1)])))
    })
    .unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert!(
        e.notes.iter().any(|n| n.contains("twice in a row")),
        "the witness is the call made twice: {e:?}"
    );
}

#[test]
fn rejects_rebuilding_the_parameter() {
    // f n = case n of Zero -> 0; Succ m -> f (Succ m): `Succ m` is `n`.
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 1);
    let (nat, z) = (p.nat, zero(&p));
    let r = define_rec(&mut p, "loop", ty, |f| {
        lam(
            "n",
            case(
                0,
                nat,
                vec![
                    (vec![], z),
                    (vec!["m"], app(f, [Term::ctor(nat, 1, vec![v(0)])])),
                ],
            ),
        )
    });
    assert_eq!(code(r), "E-TERMINATION");
}

#[test]
fn rejects_rebuilding_with_a_different_constructor_or_fields() {
    // f m n = case m of Zero -> 0; Succ m' -> f (Succ n) m': `Succ n` isn't
    // a rebuilt match, so the first argument is unknown; the second isn't
    // in the first position's place.
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 2);
    let (nat, z) = (p.nat, zero(&p));
    let r = define_rec(&mut p, "grow", ty, |f| {
        lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (vec![], z),
                        (vec!["m'"], app(f, [Term::ctor(nat, 1, vec![v(1)]), v(1)])),
                    ],
                ),
            ),
        )
    });
    assert_eq!(code(r), "E-TERMINATION");
}

#[test]
fn transport_is_no_evidence() {
    // f n = case n of Zero -> 0; Succ m -> f (J (y p => Nat) m (rfl : m = m)):
    // the result of `J` is `m`, but a transport never counts as a part.
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 1);
    let nat_ty = p.nat_ty();
    let (nat, z) = (p.nat, zero(&p));
    let transported = Term::J(
        Rc::new(lam("y", lam("p", nat_ty))),
        Rc::new(v(0)),
        Rc::new(Term::Ann(
            Rc::new(Term::Refl),
            Rc::new(eq(None, v(0), v(0))),
        )),
    );
    let r = define_rec(&mut p, "viaJ", ty.clone(), |f| {
        lam(
            "n",
            case(
                0,
                nat,
                vec![(vec![], z.clone()), (vec!["m"], app(f, [transported]))],
            ),
        )
    });
    assert_eq!(code(r), "E-TERMINATION");
    // The neighbour, passing `m` itself, is accepted.
    let r = define_rec(&mut p, "direct", ty, |f| {
        lam(
            "n",
            case(0, nat, vec![(vec![], z), (vec!["m"], app(f, [v(0)]))]),
        )
    });
    assert_eq!(code(r), "ok");
}

#[test]
fn a_number_case_is_no_evidence() {
    // f n = case n of 3 -> f n; _ -> 0, with `Nat` registered as the
    // builtin so number cases check.
    let mut p = Prelude::new();
    stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
    let ty = nats_to_nat(&p, 1);
    let z = zero(&p);
    let num_case = |arm: Term, default: Term| {
        Term::NumCase(
            0,
            Rc::new([NumArm {
                value: Rc::new(BigUint::from(3u32)),
                body: Rc::new(arm),
            }]),
            Rc::new(default),
        )
    };
    let r = define_rec(&mut p, "loop", ty, |f| {
        lam("n", num_case(app(f, [v(0)]), z))
    });
    assert_eq!(code(r), "E-TERMINATION");
}

// Saturation

#[test]
fn rejects_a_partial_recursive_call() {
    // f m n = case m of Zero -> n; Succ m' -> applyTo (f m') n
    // `f m'` would be fine as a call, but isn't given `n`.
    let mut p = Prelude::new();
    let apply_to = apply_to(&mut p);
    let ty = nats_to_nat(&p, 2);
    let nat = p.nat;
    let e = define_rec(&mut p, "sumWith", ty.clone(), |f| {
        lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (vec![], v(0)),
                        (vec!["m'"], app(Term::Def(apply_to), [app(f, [v(0)]), v(1)])),
                    ],
                ),
            ),
        )
    })
    .unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert!(e.message.contains("without all its arguments"), "{e:?}");
    assert!(
        e.notes.iter().any(|n| n.contains("`x => sumWith m' x`")),
        "suggests the lambda: {e:?}"
    );
    // The neighbour: `x => f m' x`.
    let r = define_rec(&mut p, "sumWith2", ty, |f| {
        lam(
            "m",
            lam(
                "n",
                case(
                    1,
                    nat,
                    vec![
                        (vec![], v(0)),
                        (
                            vec!["m'"],
                            app(Term::Def(apply_to), [lam("x", app(f, [v(1), v(0)])), v(1)]),
                        ),
                    ],
                ),
            ),
        )
    });
    assert_eq!(code(r), "ok");
}

#[test]
fn rejects_a_bare_recursive_reference() {
    let mut p = Prelude::new();
    let apply_to = apply_to(&mut p);
    let ty = nats_to_nat(&p, 1);
    let e = define_rec(&mut p, "viaHelper", ty, |f| {
        lam("n", app(Term::Def(apply_to), [f, v(0)]))
    })
    .unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert!(e.message.contains("without all its arguments"), "{e:?}");
}

/// Implicit parameters count towards the entry arity: a call given only the
/// implicit ones is partial.
#[test]
fn implicit_parameters_count_towards_the_arity() {
    // len : [a : Type] -> List a -> Nat
    // len [a] xs = case xs of Nil -> 0; Cons h t -> Succ (len [a] t)
    let mut p = Prelude::new();
    let ty = ipi("a", ty(), arrow(Term::data(p.list, vec![v(0)]), p.nat_ty()));
    let (list, nat) = (p.list, p.nat);
    let z = zero(&p);
    let with_a = |f: Term| Term::App(Rc::new(f), Rc::new(v(3)), Icit::Implicit);
    let len = |f: Term, tail: fn(Term) -> Term| {
        ilam(
            "a",
            lam(
                "xs",
                case(
                    0,
                    list,
                    vec![
                        (vec![], z.clone()),
                        (vec!["h", "t"], Term::ctor(nat, 1, vec![tail(with_a(f))])),
                    ],
                ),
            ),
        )
    };
    let id = define_rec(&mut p, "len", ty.clone(), |f| len(f, |g| app(g, [v(0)])))
        .expect("len terminates");
    assert_eq!(p.g.def(id).arity, 2);
    // `len [a]`, given only the implicit argument, is partial. (It isn't
    // type-checked: the termination checker is what refuses it.)
    let id = declare(&mut p.g, "len2", ty);
    p.g.defs[id.0].arity = 2;
    let body = len(Term::Def(id), |g| g);
    let e = termination::check(&p.g, &body, id, "len2", span()).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert!(e.message.contains("without all its arguments"), "{e:?}");
}

/// The entry arity is the body's leading lambdas, not the type's arrows:
/// a definition returning a function is saturated by its entry parameters.
#[test]
fn the_arity_comes_from_the_body_not_the_type() {
    // f : Nat -> (Nat -> Nat); f n = case n of Zero -> x => x; Succ m -> f m
    let mut p = Prelude::new();
    let ty = arrow(p.nat_ty(), nats_to_nat(&p, 1));
    let nat = p.nat;
    let id = define_rec(&mut p, "f", ty, |f| {
        lam(
            "n",
            case(
                0,
                nat,
                vec![(vec![], lam("x", v(0))), (vec!["m"], app(f, [v(0)]))],
            ),
        )
    })
    .expect("`f m` is saturated: f has one entry parameter");
    assert_eq!(p.g.def(id).arity, 1);
}

/// Arguments beyond the arity get no entry in the graph, but they're walked
/// for calls.
#[test]
fn over_applied_calls_are_walked_in_every_argument() {
    // f : Nat -> Nat -> Nat with entry arity 1:
    // f n = case n of Zero -> x => x; Succ m -> x => f m (<hidden>)
    let mut p = Prelude::new();
    let ty = arrow(p.nat_ty(), nats_to_nat(&p, 1));
    let nat = p.nat;
    let with_extra = |p: &mut Prelude, name: &str, extra: fn(Term) -> Term| {
        define_rec(p, name, ty.clone(), |f| {
            lam(
                "n",
                case(
                    0,
                    nat,
                    vec![
                        (vec![], lam("x", v(0))),
                        (vec!["m"], lam("x", app(f.clone(), [v(1), extra(f)]))),
                    ],
                ),
            )
        })
    };
    // The extra argument calls `f n x`: `n` isn't smaller.
    let hidden = with_extra(&mut p, "hidden", |f| app(f, [v(2), v(0)]));
    assert_eq!(code(hidden), "E-TERMINATION");
    // The neighbour calls `f m x`.
    let fine = with_extra(&mut p, "fine", |f| app(f, [v(1), v(0)]));
    let fine = fine.expect("`fine` terminates");
    // `fine 3` is a closure that calls `fine` when it's applied, after
    // `fine` has returned (§6.3 test 2, for one function): it finishes.
    let result = run(&p.g, fine, &[3, 7], 1_000_000).expect("fine 3 7 runs");
    assert_eq!(nat_of(&result), Some(7));
}

// Arity zero

#[test]
fn rejects_an_arity_zero_self_reference() {
    let mut p = Prelude::new();
    let ty = p.nat_ty();
    let e = define_rec(&mut p, "forever", ty, |f| f).unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
    assert!(e.labels[0].message.contains("no parameters"), "{e:?}");
}

#[test]
fn rejects_an_arity_zero_function_calling_itself() {
    // loop : Nat -> Nat; loop = (n => loop n : Nat -> Nat)
    // No entry lambdas (the annotation comes first), so `loop n` is
    // over-applied and its graph has no entries.
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 1);
    let ann_ty = ty.clone();
    let e = define_rec(&mut p, "loop", ty, |f| {
        Term::Ann(Rc::new(lam("n", app(f, [v(0)]))), Rc::new(ann_ty))
    })
    .unwrap_err();
    assert_eq!(e.code, "E-TERMINATION");
}

// The arity contract

#[test]
fn the_arity_is_set_before_the_body_is_checked() {
    // Even when checking fails, the stored arity is the submitted body's.
    let mut p = Prelude::new();
    let apply_to = apply_to(&mut p);
    let ty = nats_to_nat(&p, 2);
    let id = declare(&mut p.g, "f", ty);
    // f m n = applyTo (f m) n
    let body = lam(
        "m",
        lam(
            "n",
            app(Term::Def(apply_to), [app(Term::Def(id), [v(1)]), v(0)]),
        ),
    );
    assert_eq!(code(define_def(&mut p.g, id, &body)), "E-TERMINATION");
    assert_eq!(p.g.def(id).arity, 2);
}

#[test]
fn a_body_that_disagrees_with_the_stored_arity_is_malformed() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 1);
    let id = declare(&mut p.g, "f", ty);
    p.g.defs[id.0].arity = 2;
    let body = lam("n", v(0));
    let e = termination::check(&p.g, &body, id, "f", span()).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
}

// Running out

/// `f a b c` whose calls pass the three arguments in every order, with `a`
/// replaced by a part of it: terminating (each call makes one argument
/// smaller and none larger), but with dozens of graphs in the closure.
fn many_calls(p: &Prelude, f: Term) -> Term {
    let nat = p.nat;
    // Levels: a 0, b 1, c 2, a' 3. Under the match on `a`, call `f` with
    // each permutation of (a', b, c).
    let perms: [[usize; 3]; 6] = [
        [3, 1, 2],
        [3, 2, 1],
        [1, 3, 2],
        [1, 2, 3],
        [2, 3, 1],
        [2, 1, 3],
    ];
    let level = 4;
    let calls = perms.iter().fold(zero(p), |acc, perm| {
        app(
            Term::Def(p.add),
            [acc, app(f.clone(), perm.iter().map(|l| v(level - 1 - l)))],
        )
    });
    lam(
        "a",
        lam(
            "b",
            lam(
                "c",
                case(2, nat, vec![(vec![], zero(p)), (vec!["a'"], calls)]),
            ),
        ),
    )
}

#[test]
fn running_out_while_deciding_termination_is_inconclusive() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 3);
    let id = declare(&mut p.g, "f", ty.clone());
    let body = many_calls(&p, Term::Def(id));
    p.g.defs[id.0].arity = 3;
    // Enough graphs: it terminates (a permutation of the arguments with one
    // made smaller, repeated, always shrinks something).
    assert!(termination::check(&p.g, &body, id, "f", span()).is_ok());
    // Too few: inconclusive, not accepted.
    let e = termination::check_with_limit(&p.g, &body, id, "f", span(), 3).unwrap_err();
    assert_eq!(e.code, "E-RESOURCE");
    assert!(e.notes.iter().any(|n| n.contains("inconclusive")), "{e:?}");
}

#[test]
fn running_out_of_steps_while_deciding_termination_leaves_the_definition_failed() {
    let mut p = Prelude::new();
    let ty = nats_to_nat(&p, 3);
    // How many steps type-checking the body takes on its own.
    let probe = declare(&mut p.g, "probe", ty.clone());
    let body = many_calls(&p, Term::Def(probe));
    let checking = {
        let _op = p.g.budget.operation(Limits::default());
        let before = p.g.budget.total_work();
        let def = p.g.def(probe);
        let mut cx = check::Ctx::new(&p.g, def.span);
        check::check(&mut cx, &body, &def.ty_value).expect("the body type-checks");
        p.g.budget.total_work() - before
    };
    let id = declare(&mut p.g, "f", ty);
    let body = many_calls(&p, Term::Def(id));
    let r = {
        let saved = p.g.budget.start(Limits {
            work: checking + 1,
            ..Limits::default()
        });
        let r = define_def(&mut p.g, id, &body);
        p.g.budget.restore(saved);
        r
    };
    let e = r.unwrap_err();
    assert_eq!(e.code, "E-RESOURCE");
    assert!(
        e.labels.iter().any(|l| l.message.contains("terminates")),
        "it ran out in the termination check: {e:?}"
    );
    assert_eq!(p.g.def(id).state(), stitchwort_core::globals::State::Failed);
    assert_eq!(def_hash(&p.g, id).unwrap(), None);
}

// Generated programs: the old checker against the new

/// Programs on `Nat` in the core, all of type `Nat`, built from: case trees
/// on parameters and fields, variables, `Zero`, `Succ`, `add`, calls to the
/// function being defined (with all its arguments, or occasionally fewer,
/// passed to `applyTo`), and lambdas passed to `applyTo`. Every one
/// type-checks, so it can be run.
struct Gen {
    rng: u64,
    nat: stitchwort_core::DataId,
    add: DefId,
    apply_to: DefId,
    f: DefId,
    arity: usize,
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

    /// A case tree with `level` variables in scope, of which those in
    /// `matchable` (levels) are parameters or fields.
    fn tree(&mut self, level: usize, matchable: &[usize], depth: usize) -> Term {
        if depth > 0 && self.below(4) > 0 {
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
            0 => self.expr(level, 1),
            1..=3 => self.call(level),
            4 => app(Term::Def(self.add), [self.call(level), self.call(level)]),
            _ => self.expr(level, 2),
        }
    }

    fn call(&mut self, level: usize) -> Term {
        let args: Vec<Term> = (0..self.arity).map(|_| self.arg(level, 1)).collect();
        app(Term::Def(self.f), args)
    }

    /// An argument of a call: mostly a variable or a variable rebuilt (both
    /// of which may be related to a parameter), sometimes anything.
    fn arg(&mut self, level: usize, depth: usize) -> Term {
        // The nearest binders are most often fields of matches.
        let near = |g: &mut Gen| v(g.below(level.min(2)));
        match self.below(12) {
            0..=3 => near(self),
            // A parameter itself.
            4..=6 => v(level - 1 - self.below(self.arity)),
            7 | 8 => Term::ctor(self.nat, 1, vec![near(self)]),
            9 => v(self.below(level)),
            _ => self.expr(level, depth),
        }
    }

    fn expr(&mut self, level: usize, depth: usize) -> Term {
        let leaf = depth == 0;
        match self.below(if leaf { 2 } else { 9 }) {
            0 => v(self.below(level)),
            1 => Term::ctor(self.nat, 0, vec![]),
            2 => Term::ctor(self.nat, 1, vec![self.expr(level, depth - 1)]),
            // Rebuilding a variable: sometimes a matched value.
            3 => Term::ctor(self.nat, 1, vec![v(self.below(level))]),
            4 => app(
                Term::Def(self.add),
                [self.expr(level, depth - 1), self.expr(level, depth - 1)],
            ),
            5 | 6 => {
                let args: Vec<Term> = (0..self.arity)
                    .map(|_| self.arg(level, depth - 1))
                    .collect();
                app(Term::Def(self.f), args)
            }
            7 => {
                let body = self.expr(level + 1, depth - 1);
                app(
                    Term::Def(self.apply_to),
                    [lam("x", body), self.expr(level, depth - 1)],
                )
            }
            _ => {
                // A partial call, passed to `applyTo`; only possible when
                // exactly one argument is missing.
                if self.arity == 0 {
                    return Term::ctor(self.nat, 0, vec![]);
                }
                let args: Vec<Term> = (1..self.arity)
                    .map(|_| self.arg(level, depth - 1))
                    .collect();
                app(
                    Term::Def(self.apply_to),
                    [app(Term::Def(self.f), args), self.expr(level, depth - 1)],
                )
            }
        }
    }
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

/// Whether `term` has an occurrence of `f` with fewer than `arity` arguments.
fn has_partial_occurrence(term: &Term, f: DefId, arity: usize) -> bool {
    let (head, args) = term.spine();
    if args.is_empty() {
        if matches!(head, Term::Def(id) if *id == f) {
            return arity > 0;
        }
        let mut found = false;
        term.for_each_child(|child, _| found |= has_partial_occurrence(child, f, arity));
        return found;
    }
    let partial = match head {
        Term::Def(id) if *id == f => args.len() < arity,
        _ => has_partial_occurrence(head, f, arity),
    };
    partial || args.iter().any(|a| has_partial_occurrence(a, f, arity))
}

const PROGRAMS: u64 = 20_000;

/// On generated programs: everything the structural checker accepted, the
/// size-change checker accepts too, unless it has a partial recursive call
/// (refused on purpose). And every program either accepts runs to an answer
/// on small inputs.
#[test]
fn accepts_everything_the_structural_checker_accepted() {
    let mut p = Prelude::new();
    let apply_to = apply_to(&mut p);
    let (mut old_accepts, mut new_accepts, mut both) = (0, 0, 0);
    let (mut only_new, mut partial, mut recursive, mut old_recursive) = (0, 0, 0, 0);
    for seed in 1..=PROGRAMS {
        let arity = 1 + (seed as usize % 3);
        let ty = nats_to_nat(&p, arity);
        let id = declare(&mut p.g, &format!("f{seed}"), ty);
        let mut generator = Gen {
            rng: seed.wrapping_mul(0x9e37_79b9_7f4a_7c15),
            nat: p.nat,
            add: p.add,
            apply_to,
            f: id,
            arity,
        };
        let params: Vec<usize> = (0..arity).collect();
        let tree = generator.tree(arity, &params, 2);
        let body = (0..arity).fold(tree, |b, i| lam(&format!("p{}", arity - 1 - i), b));
        p.g.defs[id.0].arity = arity;
        let old = structural::check(&p.g, &body, id, "f", span()).is_ok();
        let is_recursive = mentions(&body, id);
        recursive += usize::from(is_recursive);
        old_recursive += usize::from(old && is_recursive);
        let new = termination::check(&p.g, &body, id, "f", span()).is_ok();
        old_accepts += usize::from(old);
        new_accepts += usize::from(new);
        both += usize::from(old && new);
        only_new += usize::from(new && !old);
        if old && !new {
            assert!(
                has_partial_occurrence(&body, id, arity),
                "seed {seed}: the structural checker accepts this, the size-change one doesn't: \
                 {}",
                stitchwort_core::pretty::term(&p.g, &[], &body)
            );
            partial += 1;
        }
        // Through the kernel, which agrees, and then run on small inputs.
        let admitted = define_def(&mut p.g, id, &body);
        assert_eq!(admitted.is_ok(), new, "seed {seed}: {admitted:?}");
        if new {
            for input in 0..3usize.pow(arity as u32) {
                let args: Vec<usize> = (0..arity)
                    .map(|i| input / 3usize.pow(i as u32) % 3)
                    .collect();
                assert!(
                    run(&p.g, id, &args, 1_000_000).is_some(),
                    "seed {seed}: accepted, but {args:?} didn't finish: {}",
                    stitchwort_core::pretty::term(&p.g, &[], &body)
                );
            }
        }
    }
    eprintln!(
        "{recursive} recursive programs (of {PROGRAMS}); structural accepts {old_accepts} \
         ({old_recursive} recursive), size change accepts {new_accepts}: both {both}, only \
         size change {only_new}, only structural (partial calls) {partial}"
    );
    // The comparison means something only if both sides have plenty of
    // cases.
    assert!(old_recursive >= 100, "{old_recursive}");
    assert!(only_new >= 50, "{only_new}");
    assert_eq!(both + partial, old_accepts);
}
