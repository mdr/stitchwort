//! Stated theorems (`check::admit_trusted_stated`, docs/core.md "Stated
//! theorems"): a final theorem whose proof isn't in this session. To
//! everything that checks against it, it is the proved theorem: the same
//! verdicts and the same hashes for its users, whatever shape its proof had.
//! `check::leave_stated` makes the same from a theorem declared in this
//! session whose proof hasn't been checked, and marks the session.

use crate::common::*;
use stitchwort_core::check;
use stitchwort_core::globals::{Assumption, Kernel, State};
use stitchwort_core::hash::{def_hash, has_interface, interface_hash, proofless_hash};
use stitchwort_core::native::{self, Native};
use stitchwort_core::pins;
use stitchwort_core::value::{Head, Value, eval};
use stitchwort_core::{DefId, Limits, Term};
use stitchwort_syntax::Diagnostic;

fn code<T>(result: Result<T, Diagnostic>) -> &'static str {
    result.err().map_or("ok", |d| d.code)
}

fn theorem(g: &mut Kernel, name: &str, ty: Term, proof: Term) -> Result<DefId, &'static str> {
    let id = check::declare_def(g, &name.into(), &name.into(), &ty, true, false, span())
        .map_err(|d| d.code)?;
    check::define_def(g, id, &proof).map_err(|d| d.code)?;
    Ok(id)
}

/// `(n: Nat) -> n = n`.
/// Declares theorem `name: ty`, pending.
fn declare_theorem(g: &mut Kernel, name: &str, ty: Term) -> DefId {
    check::declare_def(g, &name.into(), &name.into(), &ty, true, false, span()).unwrap()
}

fn statement(p: &Prelude) -> Term {
    pi("n", p.nat_ty(), eq(Some(p.nat_ty()), v(0), v(0)))
}

/// How `refl: (n: Nat) -> n = n` is there.
#[derive(Clone, Copy, Debug)]
enum Refl {
    /// Proved as lambdas, `n => Refl`: arity 1.
    Lambdas,
    /// Proved by a lemma, `:= base`: arity 0.
    Lemma,
    /// Stated, its proof not loaded, as a cache entry would give it.
    Stated,
    /// Declared here and left stated, its proof not checked.
    Left,
    /// Left stated in another session, and admitted from its interface
    /// entry, its proof still not checked.
    Admitted,
}

/// The prelude with `refl` in it, `how`.
fn with_refl(how: Refl) -> (Prelude, DefId) {
    let mut p = Prelude::new();
    let ty = statement(&p);
    let refl = match how {
        Refl::Lambdas => theorem(&mut p.g, "refl", ty, lam("n", Term::Refl)).unwrap(),
        Refl::Lemma => {
            let base = theorem(&mut p.g, "base", ty.clone(), lam("n", Term::Refl)).unwrap();
            theorem(&mut p.g, "refl", ty, Term::Def(base)).unwrap()
        }
        Refl::Stated => {
            // The type the checked path gave back, with its proof marks, as
            // an entry records it.
            let (proved, id) = with_refl(Refl::Lambdas);
            let checked = proved.g.def(id).ty().clone();
            check::admit_trusted_stated(&mut p.g, &"refl".into(), &"refl".into(), &checked, span())
                .unwrap()
        }
        Refl::Left => {
            let id = declare_theorem(&mut p.g, "refl", ty);
            check::leave_stated(&mut p.g, id).unwrap();
            id
        }
        Refl::Admitted => {
            let (left, id) = with_refl(Refl::Left);
            let checked = left.g.def(id).ty().clone();
            check::admit_trusted_unproved(
                &mut p.g,
                &"refl".into(),
                &"refl".into(),
                &checked,
                span(),
            )
            .unwrap()
        }
    };
    (p, refl)
}

/// Users of `refl`: a full application, a partial one compared with a
/// lambda (eta, which once read the proof's lambdas), and a definition
/// returning it unapplied.
fn users(p: &mut Prelude, refl: DefId) -> Vec<DefId> {
    let nat = p.nat_ty();
    let two = p.num(2);
    let full = theorem(
        &mut p.g,
        "full",
        eq(Some(nat.clone()), two.clone(), two.clone()),
        app(Term::Def(refl), [two]),
    )
    .unwrap();
    let st = statement(p);
    let eta = theorem(
        &mut p.g,
        "eta",
        eq(
            Some(st.clone()),
            Term::Def(refl),
            lam("n", app(Term::Def(refl), [v(0)])),
        ),
        Term::Refl,
    )
    .unwrap();
    let partial = theorem(&mut p.g, "partial", st, Term::Def(refl)).unwrap();
    vec![full, eta, partial]
}

#[test]
fn a_stated_theorem_is_final_with_no_proof() {
    let (p, refl) = with_refl(Refl::Stated);
    let def = p.g.def(refl);
    assert!(def.stated() && def.theorem() && def.proof() && def.defined());
    assert_eq!(def.state(), State::Final);
    assert!(def.body().is_none() && def.group().is_none() && def.assumption().is_none());
    assert_eq!(def.arity(), 0);
    assert!(has_interface(&p.g.ev(), refl));
}

/// Its interface hash is the proved theorem's, whichever shape the proof
/// had, so every user's hash is the same with either; and without proofs
/// it hashes as the proved theorem does. Its full hash isn't here: the
/// cache's replay puts the recorded one in.
#[test]
fn users_check_and_hash_the_same_against_a_stated_theorem() {
    let mut hashes = Vec::new();
    for how in [
        Refl::Lambdas,
        Refl::Lemma,
        Refl::Stated,
        Refl::Left,
        Refl::Admitted,
    ] {
        let (mut p, refl) = with_refl(how);
        let users = users(&mut p, refl);
        let ev = p.g.ev();
        let mut these = vec![
            interface_hash(&ev, refl).unwrap(),
            proofless_hash(&ev, refl).unwrap(),
        ];
        for u in users {
            these.push(def_hash(&ev, u).unwrap());
            these.push(proofless_hash(&ev, u).unwrap());
        }
        assert!(these.iter().all(Option::is_some), "{how:?}: {these:?}");
        if matches!(how, Refl::Stated) {
            assert_eq!(def_hash(&ev, refl).unwrap(), None);
        }
        hashes.push((how, these));
    }
    let (_, first) = &hashes[0];
    for (how, these) in &hashes[1..] {
        assert_eq!(first, these, "{how:?} against proved as lambdas");
    }
}

/// While a program runs, a call of a theorem is erased whatever its
/// arguments, with or without a body here, and its arity isn't read: a
/// stated theorem applied to one argument, unapplied, and a proved one
/// unapplied.
#[test]
fn running_erases_a_stated_theorem_at_any_arity() {
    for how in [Refl::Stated, Refl::Lambdas] {
        let (p, refl) = with_refl(how);
        let _op = p.g.machine.budget.operation(Limits::default());
        let _running = p.g.machine.erasure.running();
        let ev = p.g.ev();
        for term in [Term::Def(refl), app(Term::Def(refl), [p.num(3)])] {
            let value = eval(&ev, &[], &term).unwrap();
            assert!(
                stitchwort_core::erase::is_erased(&value),
                "{how:?}: {term:?} is erased"
            );
        }
    }
}

/// While checking, it never unfolds: a call of it is neutral.
#[test]
fn a_stated_theorem_is_neutral_while_checking() {
    let (p, refl) = with_refl(Refl::Stated);
    let _op = p.g.machine.budget.operation(Limits::default());
    let value = eval(&p.g.ev(), &[], &app(Term::Def(refl), [p.num(1)])).unwrap();
    assert!(matches!(value, Value::Neutral(Head::Def(id), _) if id == refl));
}

/// Nothing gives it a body, a new type, a run body or a validator
/// afterwards, and an `unfolding` list can't name it.
#[test]
fn nothing_gives_a_stated_theorem_a_body() {
    let (mut p, refl) = with_refl(Refl::Stated);
    let st = statement(&p);
    assert_eq!(
        code(check::define_def(&mut p.g, refl, &lam("n", Term::Refl))),
        "E-MALFORMED"
    );
    assert_eq!(code(check::retype_def(&mut p.g, refl, &st)), "E-MALFORMED");
    assert_eq!(
        code(check::set_run_body(&mut p.g, refl, &lam("n", Term::Refl))),
        "E-MALFORMED"
    );
    assert_eq!(
        code(check::admit_trusted_run_body(&mut p.g, refl, &Term::Refl)),
        "E-MALFORMED"
    );
    let opaque =
        check::declare_def(&mut p.g, &"o".into(), &"o".into(), &st, true, false, span()).unwrap();
    check::mark_opaque(&mut p.g, opaque);
    check::set_unfolding(&mut p.g, opaque, &[refl]);
    assert_ne!(
        code(check::define_def(&mut p.g, opaque, &Term::Def(refl))),
        "ok"
    );
    let def = p.g.def(refl);
    assert!(def.stated() && def.body().is_none() && def.own_run_body().is_none());
}

/// It is made only for a proposition whose type refers only to final
/// declarations; a refusal adds nothing.
#[test]
fn admit_trusted_stated_refuses_what_isnt_a_final_statement() {
    let mut p = Prelude::new();
    let before = p.g.env.defs().len();
    let computes = arrow(p.nat_ty(), p.nat_ty());
    assert_eq!(
        code(check::admit_trusted_stated(
            &mut p.g,
            &"f".into(),
            &"f".into(),
            &computes,
            span()
        )),
        "E-MALFORMED"
    );
    let nat = p.nat_ty();
    let pending = declare(&mut p.g, "pending", nat);
    let on_pending = eq(Some(p.nat_ty()), Term::Def(pending), Term::Def(pending));
    assert_eq!(
        code(check::admit_trusted_stated(
            &mut p.g,
            &"t".into(),
            &"t".into(),
            &on_pending,
            span()
        )),
        "E-MALFORMED"
    );
    assert_eq!(p.g.env.defs().len(), before + 1, "only `pending` was added");
}

/// Left stated, a declared theorem is final with no proof, as one from the
/// cache is, and the session is marked as holding a promise; a stated
/// theorem from the cache doesn't mark it.
#[test]
fn leave_stated_makes_a_stated_theorem_and_marks_the_session() {
    let (p, refl) = with_refl(Refl::Left);
    let def = p.g.def(refl);
    assert!(def.stated() && def.unproved() && def.theorem() && def.proof() && def.defined());
    assert_eq!(def.state(), State::Final);
    assert!(def.body().is_none() && def.group().is_none() && def.assumption().is_none());
    assert_eq!(def.arity(), 0);
    assert_eq!(
        (def.name().to_string(), def.path().to_string()),
        ("refl".into(), "refl".into())
    );
    assert!(has_interface(&p.g.ev(), refl));
    assert!(p.g.holds_unproved_theorems());
    let (cached, refl) = with_refl(Refl::Stated);
    assert!(!cached.g.def(refl).unproved());
    assert!(!cached.g.holds_unproved_theorems());
}

/// The mark is the theorem: rewinding to before it drops the mark, with
/// everything checked against it.
#[test]
fn rewinding_past_a_theorem_left_stated_clears_the_mark() {
    let mut p = Prelude::new();
    let mark = p.g.mark();
    let st = statement(&p);
    let refl = declare_theorem(&mut p.g, "refl", st.clone());
    let declared = format!("{:?}", p.g.def(refl).ty());
    check::leave_stated(&mut p.g, refl).unwrap();
    let kept = format!("{:?}", p.g.def(refl).ty());
    assert_eq!(kept, declared, "the checked statement, kept");
    theorem(&mut p.g, "user", st, Term::Def(refl)).unwrap();
    assert!(p.g.holds_unproved_theorems());
    p.g.rewind(&mark);
    assert!(!p.g.holds_unproved_theorems());
}

/// The kernel counts its unproved theorems: a rewind that keeps some of
/// them keeps their count, and one past the last clears it.
#[test]
fn the_unproved_count_follows_rewinds() {
    let mut p = Prelude::new();
    let start = p.g.mark();
    let st = statement(&p);
    assert_eq!(p.g.env.unproved_count(), 0);
    let first = declare_theorem(&mut p.g, "first", st.clone());
    check::leave_stated(&mut p.g, first).unwrap();
    assert_eq!(p.g.env.unproved_count(), 1);
    let between = p.g.mark();
    let second = declare_theorem(&mut p.g, "second", st);
    check::leave_stated(&mut p.g, second).unwrap();
    assert_eq!(p.g.env.unproved_count(), 2);
    p.g.rewind(&between);
    assert_eq!(p.g.env.unproved_count(), 1);
    assert!(p.g.holds_unproved_theorems());
    p.g.rewind(&start);
    assert_eq!(p.g.env.unproved_count(), 0);
    assert!(!p.g.holds_unproved_theorems());
}

/// Nothing gives it a body afterwards: it isn't pending any more.
#[test]
fn nothing_gives_a_theorem_left_stated_a_body() {
    let (mut p, refl) = with_refl(Refl::Left);
    let st = statement(&p);
    assert_eq!(
        code(check::define_def(&mut p.g, refl, &lam("n", Term::Refl))),
        "E-MALFORMED"
    );
    assert_eq!(code(check::retype_def(&mut p.g, refl, &st)), "E-MALFORMED");
    assert_eq!(
        code(check::set_run_body(&mut p.g, refl, &lam("n", Term::Refl))),
        "E-MALFORMED"
    );
    assert_eq!(code(check::leave_stated(&mut p.g, refl)), "E-MALFORMED");
    assert_eq!(
        code(check::add_validator(&mut p.g, refl, 0, p.nat, &Term::Refl)),
        "E-MALFORMED"
    );
    assert!(p.g.def(refl).body().is_none());
}

/// A native can't be registered for it, and a pin never takes it for the
/// pinned declaration: refusals, not the full hash's internal error.
#[test]
fn natives_and_pins_refuse_a_theorem_left_stated() {
    for how in [Refl::Left, Refl::Stated] {
        let (mut p, refl) = with_refl(how);
        let b = Native::Add.builtin();
        assert_eq!(
            code(native::register_native(&mut p.g, refl, Native::Add)),
            "E-BUILTIN",
            "{how:?}"
        );
        assert!(!pins::holds(&p.g.ev(), refl, b), "{how:?}");
        assert!(pins::stale_def(&mut p.g, refl, b), "{how:?}");
        assert_eq!(
            code(pins::check_bound_def(&mut p.g, refl, b)),
            "E-BUILTIN",
            "{how:?}"
        );
    }
}

/// Its hash without proofs is its statement's even when working out which
/// positions are proofs runs out of resources, which for a proved theorem
/// falls back to hashing the body a stated one hasn't got.
#[test]
fn a_stated_theorems_proofless_hash_needs_no_budget() {
    let (proved, id) = with_refl(Refl::Lambdas);
    let expected = proofless_hash(&proved.g.ev(), id).unwrap();
    for how in [Refl::Stated, Refl::Left] {
        let (p, refl) = with_refl(how);
        let _op = p.g.machine.budget.operation(Limits {
            work: 1,
            ..Limits::default()
        });
        assert_eq!(
            proofless_hash(&p.g.ev(), refl).unwrap(),
            expected,
            "{how:?}"
        );
    }
}

/// Admitted from an interface entry in another session, a theorem left
/// stated keeps its mark there: it is the same stated theorem, and that
/// session holds a promise too (`admit_trusted_stated` would drop it).
#[test]
fn admit_trusted_unproved_keeps_the_mark_in_another_session() {
    let (p, refl) = with_refl(Refl::Admitted);
    let def = p.g.def(refl);
    assert!(def.stated() && def.unproved() && def.theorem() && def.proof() && def.defined());
    assert!(def.body().is_none() && def.group().is_none() && def.assumption().is_none());
    assert!(p.g.holds_unproved_theorems());
    let (left, id) = with_refl(Refl::Left);
    assert_eq!(
        interface_hash(&p.g.ev(), refl).unwrap(),
        interface_hash(&left.g.ev(), id).unwrap()
    );
}

/// Nor is it once admitted elsewhere: asking there is the internal error too.
#[test]
#[should_panic(expected = "a theorem whose proof hasn't been checked")]
fn the_full_hash_of_an_admitted_unproved_theorem_is_an_internal_error() {
    let (p, refl) = with_refl(Refl::Admitted);
    let _ = def_hash(&p.g.ev(), refl);
}

/// Its full hash isn't known, so asking for it is an internal error, never
/// `None` (which reads as "not final").
#[test]
#[should_panic(expected = "a theorem whose proof hasn't been checked")]
fn the_full_hash_of_a_theorem_left_stated_is_an_internal_error() {
    let (p, refl) = with_refl(Refl::Left);
    let _ = def_hash(&p.g.ev(), refl);
}

/// Puts a mark on a pending definition, given an opaque one to unfold.
type Mark = fn(&mut Kernel, DefId, DefId);

/// `leave_stated` takes only a pending theorem the kernel declared and
/// checked here, with nothing a stated theorem can't carry; each refusal
/// leaves it as it was.
#[test]
fn leave_stated_refuses_what_isnt_a_checked_pending_theorem() {
    let mut p = Prelude::new();
    let st = statement(&p);
    let nat = p.nat_ty();
    let unchanged = |g: &Kernel, id: DefId, state: State| {
        let def = g.def(id);
        assert!(
            !def.stated() && !def.unproved(),
            "`{}` unchanged",
            def.name()
        );
        assert_eq!(def.state(), state, "`{}` unchanged", def.name());
    };

    let unknown = DefId(p.g.env.defs().len() + 5);
    assert_eq!(code(check::leave_stated(&mut p.g, unknown)), "E-MALFORMED");

    // A definition whose type is a proposition, but not a theorem.
    let def = declare(&mut p.g, "def", st.clone());
    assert_eq!(code(check::leave_stated(&mut p.g, def)), "E-MALFORMED");
    unchanged(&p.g, def, State::Pending);

    // Already defined, or failed.
    let proved = theorem(&mut p.g, "proved", st.clone(), lam("n", Term::Refl)).unwrap();
    assert_eq!(code(check::leave_stated(&mut p.g, proved)), "E-MALFORMED");
    unchanged(&p.g, proved, State::Final);
    let failed = declare_theorem(&mut p.g, "failed", st.clone());
    assert_ne!(code(check::define_def(&mut p.g, failed, &Term::Refl)), "ok");
    assert_eq!(code(check::leave_stated(&mut p.g, failed)), "E-MALFORMED");
    unchanged(&p.g, failed, State::Failed);

    // An assumption, final at once.
    let assumed = check::assume(
        &mut p.g,
        &"a".into(),
        &"a".into(),
        &st,
        Assumption::goal("a".into(), 1),
        true,
        span(),
    )
    .unwrap();
    assert_eq!(code(check::leave_stated(&mut p.g, assumed)), "E-MALFORMED");
    unchanged(&p.g, assumed, State::Final);

    // A statement the cache gave, not checked here.
    let checked = p.g.def(proved).ty().clone();
    let trusted =
        check::admit_trusted_def(&mut p.g, &"tr".into(), &"tr".into(), &checked, true, span())
            .unwrap();
    assert_eq!(code(check::leave_stated(&mut p.g, trusted)), "E-MALFORMED");
    unchanged(&p.g, trusted, State::Pending);

    // An export.
    let export = check::declare_def(
        &mut p.g,
        &"ex".into(),
        &"ex".into(),
        &st,
        true,
        true,
        span(),
    )
    .unwrap();
    assert_eq!(code(check::leave_stated(&mut p.g, export)), "E-MALFORMED");
    unchanged(&p.g, export, State::Pending);

    // Each mark a stated theorem can't carry.
    let opaque = declare_theorem(&mut p.g, "o", st.clone());
    check::mark_opaque(&mut p.g, opaque);
    let marks: [(&str, Mark); 6] = [
        ("instance", |g, id, _| check::mark_instance(g, id)),
        ("fold", |g, id, _| check::mark_folded(g, id)),
        ("opaque", |g, id, _| check::mark_opaque(g, id)),
        ("tailrec", |g, id, _| check::mark_tailrec(g, id)),
        ("default", |g, id, _| check::mark_param_default(g, id)),
        ("unfolding", |g, id, o| check::set_unfolding(g, id, &[o])),
    ];
    for (name, mark) in marks {
        let id = declare_theorem(&mut p.g, name, st.clone());
        mark(&mut p.g, id, opaque);
        assert_eq!(
            code(check::leave_stated(&mut p.g, id)),
            "E-MALFORMED",
            "{name}"
        );
        unchanged(&p.g, id, State::Pending);
    }

    // A statement about a failed declaration, which `declare_def` let
    // through for `define_def` to find.
    let bad = declare(&mut p.g, "bad", nat.clone());
    assert_ne!(code(check::define_def(&mut p.g, bad, &Term::Refl)), "ok");
    let on_bad = eq(Some(nat), Term::Def(bad), Term::Def(bad));
    let uses_bad = declare_theorem(&mut p.g, "usesBad", on_bad);
    assert_eq!(
        code(check::leave_stated(&mut p.g, uses_bad)),
        "E-FAILED-DEPENDENCY"
    );
    unchanged(&p.g, uses_bad, State::Pending);

    assert!(!p.g.holds_unproved_theorems());
}
