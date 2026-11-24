//! Stated theorems (`check::admit_trusted_stated`, docs/core.md "Stated
//! theorems"): a final theorem whose proof isn't in this session. To
//! everything that checks against it, it is the proved theorem: the same
//! verdicts and the same hashes for its users, whatever shape its proof had.

use crate::common::*;
use stitchwort_core::check;
use stitchwort_core::globals::{Kernel, State};
use stitchwort_core::hash::{def_hash, has_interface, interface_hash, proofless_hash};
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
    for how in [Refl::Lambdas, Refl::Lemma, Refl::Stated] {
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
