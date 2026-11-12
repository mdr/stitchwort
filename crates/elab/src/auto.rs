//! Finding proofs for `[auto x : P]` arguments (DESIGN.md §6).
//!
//! When an auto argument is inserted, the elaborator records an obligation and
//! carries on. Once the declaration has been elaborated, so unification has
//! worked out as much as it can, each obligation is proved, in this order:
//!
//! 1. a hypothesis in scope whose type is `P` (e.g. the `h` in
//!    `if h : d != 0 then n / d else 0`);
//! 2. a decision procedure for `P`: any definition marked `instance` whose
//!    result type is `Decidable …` (D163), trying the most recently defined
//!    first (so a file's own procedures take priority over the prelude's).
//!    An equation none of them decides is decided through its type's
//!    `DecEq` instance (`interfaces::decide_eq`, docs/proposals/interfaces.md
//!    §5.12, §5.16). Only definitions that
//!    are already checked, and, in the same module, written above the use:
//!    declarations may be checked out of source order
//!    (docs/proposals/mutual-recursion.md §8.1), and one waiting for its
//!    dependencies isn't available yet. That's a deliberate limitation;
//!    passing a procedure explicitly makes it a dependency, checked first. Its arguments are found by unification, and any
//!    `Decidable` or auto arguments it needs are found recursively, one
//!    deeper each time, up to `MAX_DEPTH`. It's run at
//!    compile time, and its test must be `True`. The proof is then `d.sound
//!    rfl`, which the kernel re-checks by computing `d`'s test itself.
//!
//! Between 1 and 2, a lexicographic `decreasing` obligation, `Nat.LexLess a1
//! a2 b1 b2`, is split: `a1 < b1`, or else `a1` the same as `b1` and `a2 <
//! b2`, each proved this same way (docs/proposals/well-founded-recursion.md,
//! stage 3d).
//!
//! A goal that computing doesn't decide is then tried against the decision
//! procedures again as written, its calls matched by their arguments
//! (`Nat.pow 2 (Succ k) ≠ 0` before it computes to `Nat.pow 2 k * 2 ≠ 0`),
//! and then proved from the facts in scope where that's quick: `d ≠ 0` from
//! a fact `Succ k ≤ d`, `Nat.toInt d ≠ 0` from `d ≠ 0`, and, in a module that
//! loads `omega`'s library, an arithmetic goal by `omega` within a small
//! budget (`from_facts`). Last, the parts of a conjunction in scope are facts
//! too, each as in 1 or as `Succ k ≤ d` (`from_conjuncts`): `h: b ≠ 0 ∧ c ≠ 0`,
//! or the proof an `if b != 0 && c != 0` gives its branch. Failing that, a context
//! that contradicts itself proves anything: `e = True` beside `e = False`, or
//! an equation of different constructors (`cases`' closer, `by_contradiction`).
//!
//! An obligation whose type is an interface applied to a type is an instance
//! to find instead (`interfaces.rs`, docs/proposals/interfaces.md §5.5).
//! One may have to wait, until solving others has said more about its type
//! or its candidates; obligations are retried in rounds while a round makes
//! progress.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::rc::Rc;

use stitchwort_core::globals::State;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{DataId, DefId, Ev, Icit, Name, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, builtin_ctor, builtin_data, builtin_def};
use crate::interfaces::{self, Attempt};
use crate::{Elaborator, Global};

type Result<T> = std::result::Result<T, Diagnostic>;

/// What one level of dependence between decision procedures costs.
const LEVEL: usize = 256;

/// How deep decision procedures may depend on each other: eight levels. A
/// procedure that needs the decision of a smaller part of its own proposition
/// (`Decidable.or` on `a ∨ rest`, which membership in a literal list unfolds
/// to) costs 1 instead of `LEVEL`, so such a chain may be a couple of
/// thousand steps long and the search is still bounded.
const MAX_DEPTH: usize = 8 * LEVEL;

/// An auto argument still to be proved: the metavariable standing for it, its
/// type, and the context it was created in.
#[derive(Clone)]
pub struct Obligation {
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    pub names: Vec<Name>,
    pub goal: Value,
    pub meta: Term,
    pub span: Span,
    /// The obligation tree it belongs to (an obligation and the
    /// prerequisites finding its instance created), whose step budget it
    /// spends: the first one's metavariable.
    pub tree: usize,
}

impl Elaborator {
    /// Proves every outstanding obligation, and finds every instance. An
    /// instance that can't be found yet waits; the waiting ones are retried
    /// while anything else gets solved, and reported once nothing does.
    pub(crate) fn solve_obligations(&self) -> Result<()> {
        match self.solve_obligations_until_stuck()? {
            None => Ok(()),
            Some(stuck) => {
                // Reported: nothing is left waiting.
                self.attempt.obligations.borrow_mut().clear();
                Err(stuck)
            }
        }
    }

    /// [`Elaborator::solve_obligations`], except that when the instances
    /// still waiting stop making progress they're kept, to be retried, and
    /// the error that would be reported is returned instead: at the end of a
    /// declaration a row unknown defaulted to the empty row may yet settle
    /// them (`Elaborator::settle_rows`, D1123).
    pub(crate) fn solve_obligations_until_stuck(&self) -> Result<Option<Diagnostic>> {
        let mut waiting: Vec<(Obligation, Diagnostic)> = Vec::new();
        let mut progress = false;
        loop {
            let obligations = std::mem::take(&mut *self.attempt.obligations.borrow_mut());
            if obligations.is_empty() {
                // Queued checks whose unknown is solved now (`queue.rs`,
                // W3): they may make obligations.
                if self.resume_from(0)? {
                    progress = true;
                    continue;
                }
                // Row comparisons put aside: one that's settled now is
                // progress.
                if self.retry_rows()? {
                    progress = true;
                }
                if waiting.is_empty() {
                    return Ok(None);
                }
                if !progress {
                    let stuck = waiting.swap_remove(0);
                    let mut kept = self.attempt.obligations.borrow_mut();
                    kept.push(stuck.0);
                    kept.extend(waiting.into_iter().map(|(ob, _)| ob));
                    return Ok(Some(stuck.1));
                }
                progress = false;
                self.attempt
                    .obligations
                    .borrow_mut()
                    .extend(waiting.drain(..).map(|(ob, _)| ob));
                continue;
            }
            for ob in obligations {
                if let Some((interface, arg)) = interfaces::interface_goal(self, &ob.goal)? {
                    let mut cx = Ctx::from_parts(
                        self,
                        ob.env.clone(),
                        ob.types.clone(),
                        ob.names.clone(),
                        ob.span,
                    );
                    match interfaces::attempt(&mut cx, &ob, interface, &arg)? {
                        Attempt::Solved => progress = true,
                        Attempt::Wait(why) => {
                            self.session
                                .instance_waits
                                .set(self.session.instance_waits.get() + 1);
                            waiting.push((ob, why))
                        }
                    }
                    continue;
                }
                let mut cx = Ctx::from_parts(self, ob.env, ob.types, ob.names, ob.span);
                let placeholder = cx.eval(&ob.meta)?;
                if !matches!(
                    force(&cx.g(), placeholder.clone())?,
                    Value::Neutral(Head::Meta(_), _)
                ) {
                    continue; // already determined by unification
                }
                progress = true;
                let goal = ob.goal.clone();
                let proved = crate::queue::counted_search(
                    &mut cx,
                    &goal,
                    crate::queue::Search::Auto,
                    |cx| prove(cx, &goal, 0),
                );
                let proof = match proved {
                    Ok(proof) => proof,
                    Err(e) => {
                        return Err(crate::decreasing::explain_obligation(&mut cx, &ob.goal, e));
                    }
                };
                let proof_value = cx.eval(&proof)?;
                if !cx.unify(&placeholder, &proof_value)? {
                    return Err(cx.error(
                        "E-AUTO",
                        "internal error: a found proof doesn't fit",
                        "here",
                    ));
                }
            }
        }
    }
}

impl Elaborator {
    /// Tries to prove the outstanding obligations whose metavariable is one
    /// of `wanted`, now rather than once the declaration is elaborated:
    /// `rewrite` needs to see the proof it would abstract over. One that
    /// can't be proved yet is left for later, unchanged. Whether any was
    /// proved.
    pub(crate) fn prove_now(&self, wanted: &dyn Fn(usize) -> bool) -> Result<bool> {
        let pending: Vec<_> = self
            .attempt
            .obligations
            .borrow()
            .iter()
            .filter(|ob| matches!(ob.meta.spine().0, Term::Meta(m) if wanted(*m)))
            .map(|ob| ob.meta.clone())
            .collect();
        let mut proved = false;
        for meta in pending {
            let ob = {
                let obligations = self.attempt.obligations.borrow();
                let id = |t: &Term| match t.spine().0 {
                    Term::Meta(m) => Some(*m),
                    _ => None,
                };
                let Some(ob) = obligations.iter().find(|ob| id(&ob.meta) == id(&meta)) else {
                    continue;
                };
                Obligation {
                    env: ob.env.clone(),
                    types: ob.types.clone(),
                    names: ob.names.clone(),
                    goal: ob.goal.clone(),
                    meta: ob.meta.clone(),
                    span: ob.span,
                    tree: ob.tree,
                }
            };
            let (goal, span) = (ob.goal.clone(), ob.span);
            let mut cx = Ctx::from_parts(
                self,
                ob.env.clone(),
                ob.types.clone(),
                ob.names.clone(),
                span,
            );
            let placeholder = cx.eval(&meta)?;
            if !matches!(
                force(&cx.g(), placeholder.clone())?,
                Value::Neutral(Head::Meta(_), _)
            ) {
                continue;
            }
            if interfaces::interface_goal(self, &goal)?.is_some() {
                self.solve_now(&meta)?;
                let placeholder = cx.eval(&meta)?;
                proved |= !matches!(
                    force(&cx.g(), placeholder)?,
                    Value::Neutral(Head::Meta(_), _)
                );
                continue;
            }
            let solved = crate::undo::attempt(&mut cx, |cx| {
                let proof = prove(cx, &goal, 0)?;
                let proof_value = cx.eval(&proof)?;
                if cx.unify(&placeholder, &proof_value)? {
                    Ok(())
                } else {
                    Err(cx.error("E-AUTO", "a found proof doesn't fit", "here"))
                }
            })?;
            proved |= solved.is_some();
        }
        Ok(proved)
    }
}

/// A proof of `goal`. (For an instance, an obligation to find it, solved
/// with the declaration's others.)
pub fn prove(cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Term> {
    let goal = force(&cx.g(), goal.clone())?;
    if interfaces::interface_goal(cx.e, &goal)?.is_some() {
        return Ok(crate::check::implicit_arg(cx, Icit::Auto, &goal));
    }
    for level in (0..cx.level()).rev() {
        let ty = cx.types[level].clone();
        if attempt(cx, |cx| Ok(cx.unify(&ty, &goal)?.then_some(())))?.is_some() {
            return Ok(Term::Var(cx.level() - 1 - level));
        }
    }
    if let Some(proof) = lex_less(cx, &goal, depth)? {
        return Ok(proof);
    }
    let decision = decide(cx, &goal, depth)?;
    let shown = cx.show(&goal);
    match verdict(cx, &decision)? {
        Some(true) => from_yes(cx, &goal, decision),
        Some(false) => {
            let message = match not_in_list(cx, &goal)? {
                Some(message) => message,
                None => format!("`{shown}` is false"),
            };
            Err(cx.error(
                "E-AUTO-FALSE",
                message,
                "this needs a proof that can't exist",
            ))
        }
        _ => {
            if let Some(proof) = decide_as_written(cx, &goal, depth)? {
                return Ok(proof);
            }
            if let Some(proof) = from_facts(cx, &goal)? {
                return Ok(proof);
            }
            if let Some(proof) = from_conjuncts(cx, &goal)? {
                return Ok(proof);
            }
            let levels: Vec<usize> = (0..cx.level()).collect();
            if let Some(proof) = crate::cases::by_contradiction(cx, &goal, &levels)? {
                return Ok(proof);
            }
            let mut error = cx
                .error(
                    "E-AUTO-STUCK",
                    format!("can't decide `{shown}` here"),
                    // Not "it depends on run-time values": `most + 1 ≠ 0` before
                    // `Nat.decAddSuccNotZero` holds for every `most`, but
                    // didn't compute (games/rogue/NOTES.md §2).
                    "it involves values that aren't known here, and computing it doesn't settle it",
                )
                .with_note("establish it first, with `if h: … then … else …`");
            if let Some(note) = hidden_name_note(&shown) {
                error = error.with_note(note);
            }
            Err(cx.with_opaque_notes(error, &[&goal]))
        }
    }
}

/// For a goal shown with a name the compiler generated, one with a `%`
/// (`Packet.%m1%size items`, what `Packet.size (Packets items)` computes
/// to: the call takes its step at once, so the goal can't be shown as
/// written), a note saying what it is: a helper generated for nested type
/// `Packet` (`derive_induct.rs`), which can't be written in source.
fn hidden_name_note(shown: &str) -> Option<String> {
    let name = shown
        .split(|c: char| c.is_whitespace() || "()[]{},`".contains(c))
        .find(|word| word.contains(".%"))?;
    let owner = &name[..name.find(".%")?];
    Some(format!(
        "`{name}` is a helper the compiler generates for `{owner}` \
         (part of `{owner}.size`, `{owner}.induct` or their lemmas); it can't be written in source"
    ))
}

/// `Decidable.sound [p := goal] decision rfl`: the proof from a decision
/// whose test computes to `True`, which the kernel checks by running the
/// test, not the proofs. (`cases`' decision closer writes it too,
/// `cases.rs`.)
pub(crate) fn from_yes(cx: &mut Ctx, goal: &Value, decision: Term) -> Result<Term> {
    let sound = crate::check::decidable_field(cx, 1)?;
    let goal_term = cx.quote_folded(goal)?;
    Ok(Term::app(
        Term::app(
            Term::app_icit(Term::Def(sound), goal_term, Icit::Implicit),
            decision,
        ),
        Term::Refl,
    ))
}

/// What a decision says, run now: `Some(true)` when its test computes to
/// `True`, `Some(false)` for `False`, `None` when it's stuck.
pub(crate) fn verdict(cx: &mut Ctx, decision: &Term) -> Result<Option<bool>> {
    let Value::Ctor(_, 0, fields) = force(&cx.g(), cx.eval(decision)?)? else {
        return Ok(None);
    };
    let Some(holds) = fields.first() else {
        return Ok(None);
    };
    let (bool, true_) = builtin_ctor(cx, Builtin::True)?;
    Ok(match force(&cx.g(), holds.clone())? {
        Value::Ctor(d, c, _) if d == bool => Some(c == true_),
        _ => None,
    })
}

/// A proof of a goal that computing doesn't decide, by a decision procedure
/// matched against the goal as written, its calls not yet computed: the one
/// for `Nat.pow (Succ b) e ≠ 0` decides `Nat.pow 2 (Succ k) ≠ 0`, which
/// computes to `Nat.pow 2 k * 2 ≠ 0`, which it doesn't fit.
fn decide_as_written(cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Option<Term>> {
    if !cx.g().machine.glue.get() || depth > MAX_DEPTH {
        return Ok(None);
    }
    let decidable = decidable(cx)?;
    for id in decision_procedures(cx, decidable)? {
        let found = attempt(cx, |cx| {
            let Some(decision) = instantiate(cx, id, decidable, goal, depth, true)? else {
                return Ok(None);
            };
            Ok((verdict(cx, &decision)? == Some(true)).then_some(decision))
        })?;
        if let Some(decision) = found {
            return from_yes(cx, goal, decision).map(Some);
        }
    }
    Ok(None)
}

/// Lemmas that `auto` may apply to facts in scope, with the number of
/// arguments before their one premise: `Nat.nonzeroOfSuccLe k d h` has two,
/// and `Nat.toIntNeZero d ok` one. The arguments are found by unification,
/// the premise from a fact, and the result must be the goal.
const FACT_LEMMAS: &[(&str, usize)] = &[("Std.Nat.nonzeroOfSuccLe", 2), ("Std.Nat.toIntNeZero", 1)];

/// A proof of a goal that computing doesn't decide, from the facts in scope:
/// `d ≠ 0` from a fact `Succ k ≤ d` (`0 < d`, `1 ≤ d`, `2 ≤ d`, …) or from
/// `Nat.toInt d ≠ 0`'s `d ≠ 0`, or, in a module that loads `omega`'s library,
/// an arithmetic goal `omega` proves from them within a small budget.
fn from_facts(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    if let Some(proof) = attempt(cx, |cx| nonzero_from_positive(cx, goal))? {
        return Ok(Some(proof));
    }
    if let Some(proof) = size_from_member(cx, goal)? {
        return Ok(Some(proof));
    }
    if cx.e.unit.omega_for_auto {
        return crate::omega::prove_for_auto(cx, goal, cx.span);
    }
    Ok(None)
}

/// A proof of `goal` from a lemma in [`FACT_LEMMAS`] and the hypotheses in
/// scope.
fn nonzero_from_positive(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    let hypotheses: Vec<(Term, Value)> = (0..cx.level())
        .rev()
        .map(|level| (Term::Var(cx.level() - 1 - level), cx.types[level].clone()))
        .collect();
    nonzero_from(cx, goal, &hypotheses)
}

/// [`nonzero_from_positive`] with the first of `facts`, proofs with their
/// types, whose type fits.
fn nonzero_from(cx: &mut Ctx, goal: &Value, facts: &[(Term, Value)]) -> Result<Option<Term>> {
    for &(name, arguments) in FACT_LEMMAS {
        if let Some(proof) = attempt(cx, |cx| apply_fact_lemma(cx, name, arguments, goal, facts))? {
            return Ok(Some(proof));
        }
    }
    Ok(None)
}

/// The lemma `name` applied to unknowns for its first `arguments` parameters
/// and to the first of `facts` whose type fits its premise, if the result is
/// `goal`.
fn apply_fact_lemma(
    cx: &mut Ctx,
    name: &str,
    arguments: usize,
    goal: &Value,
    facts: &[(Term, Value)],
) -> Result<Option<Term>> {
    let Some((Global::Def(lemma), _)) = cx.e.named(name) else {
        return Ok(None);
    };
    let lemma = *lemma;
    let g = cx.g();
    let mut term = Term::Def(lemma);
    let mut ty = g.def(lemma).ty_value().clone();
    for _ in 0..arguments {
        let Value::Pi(_, icit, dom, cod) = force(&g, ty)? else {
            return Ok(None);
        };
        let meta = cx.fresh_meta_of(&dom);
        let value = cx.eval(&meta)?;
        term = Term::app_icit(term, meta, icit);
        ty = cod.apply(&g, value)?;
    }
    let Value::Pi(_, icit, fact, cod) = force(&g, ty)? else {
        return Ok(None);
    };
    for (proof, ty) in facts {
        let found = attempt(cx, |cx| {
            if !cx.unify(ty, &fact)? {
                return Ok(None);
            }
            let conclusion = cod.apply(&g, cx.eval(proof)?)?;
            if !cx.unify(&conclusion, goal)? {
                return Ok(None);
            }
            Ok(Some(Term::app_icit(term.clone(), proof.clone(), icit)))
        })?;
        if found.is_some() {
            return Ok(found);
        }
    }
    Ok(None)
}

/// How deep a conjunction in scope is taken apart: `p ∧ (q ∧ r)` is two.
const MAX_CONJUNCTS: usize = 8;

/// A proof of `goal` from the parts of the conjunctions in scope: one whose
/// type is `goal`, or `d ≠ 0` from one that is `Succ k ≤ d`.
fn from_conjuncts(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    let mut parts = Vec::new();
    for level in (0..cx.level()).rev() {
        let proof = Term::Var(cx.level() - 1 - level);
        conjuncts(cx, proof, &cx.types[level].clone(), 1, &mut parts)?;
    }
    if parts.is_empty() {
        return Ok(None);
    }
    for (proof, ty) in &parts {
        if attempt(cx, |cx| Ok(cx.unify(ty, goal)?.then_some(())))?.is_some() {
            return Ok(Some(proof.clone()));
        }
    }
    attempt(cx, |cx| nonzero_from(cx, goal, &parts))
}

/// Adds to `parts` those of `proof: ty`, if `ty` is a conjunction `p ∧ q`:
/// `And.left proof: p` and `And.right proof: q`, each followed by its own.
fn conjuncts(
    cx: &Ctx,
    proof: Term,
    ty: &Value,
    depth: usize,
    parts: &mut Vec<(Term, Value)>,
) -> Result<()> {
    if depth > MAX_CONJUNCTS {
        return Ok(());
    }
    let g = cx.g();
    let Value::Data(d, args) = force(&g, ty.clone())? else {
        return Ok(());
    };
    if !g.env.registry().is_data(Builtin::And, d) || args.len() != 2 {
        return Ok(());
    }
    let (p, q) = (cx.quote(&args[0])?, cx.quote(&args[1])?);
    for (side, part_ty) in [(Builtin::AndLeft, &args[0]), (Builtin::AndRight, &args[1])] {
        let head = Term::Def(builtin_def(cx, side)?);
        let head = Term::app_icit(
            Term::app_icit(head, p.clone(), Icit::Implicit),
            q.clone(),
            Icit::Implicit,
        );
        let part = Term::app(head, proof.clone());
        parts.push((part.clone(), part_ty.clone()));
        conjuncts(cx, part, part_ty, depth + 1, parts)?;
    }
    Ok(())
}

/// For a nested type `T` (`derive_induct.rs`), a goal `T.size y < T.size
/// (C … xs …)` (computed: `Succ` of the sizes of `C`'s fields that hold `T`)
/// from a membership `List.Mem y xs` in scope: a hypothesis, or a field of a
/// record in scope, such as an `attach`ed element's `isIn`. It's what a
/// recursive call on an element of a list in a node needs under `decreasing
/// T.size x`. The proof is `T.%C%i%sizeMem` (generated for each field `i` of
/// `C` that's a `List T`), its arguments found by unification.
fn size_from_member(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    // A membership is a glued call of `List.Mem` (a hypothesis written `h:
    // List.Mem y xs` or `y ∈ xs`) or of `List.Any`, what that unfolds to
    // (the type of a field like `attach`'s `isIn`, stored computed). Either
    // way its first argument is the element type.
    let mut mems = Vec::new();
    for name in ["Std.List.Mem", "Std.List.Any"] {
        if let Some((Global::Def(id), _)) = cx.e.named(name) {
            mems.push(*id);
        }
    }
    if mems.is_empty() {
        return Ok(None);
    }
    for (proof, ty) in membership_facts(cx, &mems)? {
        let Value::Call(_, spine, _) = &ty else {
            continue;
        };
        if stitchwort_core::value::is_call_field(spine) {
            continue;
        }
        let args = stitchwort_core::value::call_args(spine);
        let Some((elem, _)) = args.first() else {
            continue;
        };
        let Value::Data(t, _) = force(&cx.g(), elem.clone())? else {
            continue;
        };
        for lemma in size_lemmas(cx, t) {
            let found = attempt(cx, |cx| {
                let g = cx.g();
                let mut term = Term::Def(lemma);
                let mut lemma_ty = g.def(lemma).ty_value().clone();
                let mut metas = Vec::new();
                // Every parameter but the last, the membership, is unknown.
                loop {
                    let Value::Pi(_, icit, dom, cod) = force(&g, lemma_ty)? else {
                        return Ok(None);
                    };
                    if !matches!(
                        force(&g, cod.apply(&g, Value::var(cx.level()))?)?,
                        Value::Pi(..)
                    ) {
                        if !cx.unify(&dom, &ty)? {
                            return Ok(None);
                        }
                        let conclusion = cod.apply(&g, cx.eval(&proof)?)?;
                        if !cx.unify(&conclusion, goal)? {
                            return Ok(None);
                        }
                        term = Term::app_icit(term, proof.clone(), icit);
                        break;
                    }
                    let meta = cx.fresh_meta_of(&dom);
                    let value = cx.eval(&meta)?;
                    metas.push(value.clone());
                    term = Term::app_icit(term, meta, icit);
                    lemma_ty = cod.apply(&g, value)?;
                }
                for m in &metas {
                    if matches!(force(&g, m.clone())?, Value::Neutral(Head::Meta(_), _)) {
                        return Ok(None);
                    }
                }
                Ok(Some(term))
            })?;
            if found.is_some() {
                return Ok(found);
            }
        }
    }
    Ok(None)
}

/// The memberships in scope, as proofs with their types: hypotheses `List.Mem
/// y xs`, and such fields of the records in scope (`e.isIn`), latest first:
/// those whose type is a glued call of one of `mems`.
fn membership_facts(cx: &mut Ctx, mems: &[DefId]) -> Result<Vec<(Term, Value)>> {
    let g = cx.g();
    let is_mem = |ty: &Value| matches!(ty, Value::Call(id, ..) if mems.contains(id));
    let mut facts = Vec::new();
    for level in (0..cx.level()).rev() {
        let ty = cx.types[level].clone();
        let here = Term::Var(cx.level() - 1 - level);
        if is_mem(&ty) {
            facts.push((here, ty));
            continue;
        }
        let Value::Data(r, params) = force(&g, ty)? else {
            continue;
        };
        let Some(info) = cx.e.tables.records.get(&r) else {
            continue;
        };
        for projection in info.projections.iter().flatten() {
            let mut term = Term::Def(*projection);
            let mut ty = g.def(*projection).ty_value().clone();
            let mut params = params.iter();
            loop {
                let Value::Pi(_, icit, _, cod) = force(&g, ty.clone())? else {
                    break;
                };
                if icit == Icit::Explicit {
                    term = Term::app(term, here.clone());
                    ty = cod.apply(&g, Value::var(level))?;
                    break;
                }
                let Some(p) = params.next() else {
                    break;
                };
                term = Term::app_icit(term, cx.quote(p)?, icit);
                ty = cod.apply(&g, p.clone())?;
            }
            if is_mem(&ty) {
                facts.push((term, ty));
            }
        }
    }
    Ok(facts)
}

/// The lemmas `T.%C%i%sizeMem` generated for nested type `t`, by name.
fn size_lemmas(cx: &Ctx, t: DataId) -> Vec<DefId> {
    let e = cx.e;
    let key = e.data_key(t);
    let mut found = Vec::new();
    for ctor in cx.g().data(t).ctors() {
        for i in 0..ctor.fields.len() {
            let member = format!("%{}%{i}%sizeMem", ctor.name);
            if let Some((Global::Def(id), _)) = e.scope.get(&Elaborator::member_key(&key, &member))
            {
                found.push(id);
            }
        }
    }
    found
}

/// The fewest items a list written out has for a false membership in it to
/// be reported as such, not as the disjunction it computes to.
const LISTED_MEMBERSHIP: usize = 3;

/// The most items of that list the message shows.
const LISTED_SHOWN: usize = 10;

/// For a membership in a list written out, which computes to
/// `y1 = x ∨ y2 = x ∨ … ∨ Void`: "`x` is not in the list `[y1, y2, …]`".
/// `None` for any other goal, or a list shorter than [`LISTED_MEMBERSHIP`].
fn not_in_list(cx: &Ctx, goal: &Value) -> Result<Option<String>> {
    let (Some(or), Some(void)) = (
        cx.g().env.registry().data(Builtin::Or),
        cx.g().env.registry().data(Builtin::Void),
    ) else {
        return Ok(None);
    };
    let mut value: Option<String> = None;
    let mut items: Vec<String> = Vec::new();
    let mut rest = goal.clone();
    loop {
        match force(&cx.g(), rest)? {
            Value::Data(d, params) if d == void && params.is_empty() => break,
            Value::Data(d, params) if d == or && params.len() == 2 => {
                let Value::Eq(_, item, sought) = force(&cx.g(), params[0].clone())? else {
                    return Ok(None);
                };
                let sought = cx.show(&sought);
                if value.as_ref().is_some_and(|v| *v != sought) {
                    return Ok(None);
                }
                value = Some(sought);
                items.push(cx.show(&item));
                rest = params[1].clone();
            }
            _ => return Ok(None),
        }
    }
    let Some(value) = value.filter(|_| items.len() >= LISTED_MEMBERSHIP) else {
        return Ok(None);
    };
    let count = items.len();
    let mut shown: Vec<String> = items.into_iter().take(LISTED_SHOWN).collect();
    let mut size = String::new();
    if count > LISTED_SHOWN {
        shown.push("…".to_string());
        size = format!(" ({count} items)");
    }
    Ok(Some(format!(
        "`{value}` is not in the list `[{}]`{size}",
        shown.join(", ")
    )))
}

/// A proof of `Nat.LexLess a1 a2 b1 b2`, what a recursive call of a
/// definition with `decreasing (m1, m2)` needs
/// (docs/proposals/well-founded-recursion.md, stage 3d): `a1 < b1`, or else
/// `a1` the same as `b1` and `a2 < b2`, each found the way any goal is.
/// `None` for any other goal, or when neither is found.
fn lex_less(cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Option<Term>> {
    let Some(lex) = cx.g().env.registry().data(Builtin::LexLess) else {
        return Ok(None);
    };
    let (a1, a2, b1, b2) = match goal {
        Value::Data(d, params) if *d == lex && params.len() == 4 => (
            params[0].clone(),
            params[1].clone(),
            params[2].clone(),
            params[3].clone(),
        ),
        _ => return Ok(None),
    };
    let less = builtin_def(cx, Builtin::LessThan)?;
    let less_than = |cx: &mut Ctx, a: &Value, b: &Value| -> Result<Value> {
        let term = Term::app(Term::app(Term::Def(less), cx.quote(a)?), cx.quote(b)?);
        cx.eval(&term)
    };
    let first = less_than(cx, &a1, &b1)?;
    let found = attempt(cx, |cx| match prove(cx, &first, depth + LEVEL) {
        Ok(proof) => Ok(Some(proof)),
        Err(e) => give_up_on(e),
    })?;
    if let Some(proof) = found {
        return Ok(Some(Term::ctor(lex, 0, vec![proof])));
    }
    let second = less_than(cx, &a2, &b2)?;
    attempt(cx, |cx| {
        if !cx.unify(&a1, &b1)? {
            return Ok(None);
        }
        match prove(cx, &second, depth + LEVEL) {
            Ok(proof) => Ok(Some(Term::ctor(lex, 1, vec![Term::Refl, proof]))),
            Err(e) => give_up_on(e),
        }
    })
}

/// A term of type `Decidable prop`, from the decision procedures in scope.
///
/// The search sees what the proposition computes to (D484, D2535,
/// docs/proposals/bounded-readback.md §2.6): it runs with gluing off, on
/// `prop` read back folded and computed again unglued. Unglued, evaluation
/// unfolds every call it meets, so procedures are matched against what the
/// proposition computes to (`y < 10` decided by `Nat.decLessEq y 9`, as
/// `y < 10` computes to `y <= 9`, not by `Nat.decLessThan y 10`), and the
/// decisions found, and so the elaborated terms, don't depend on gluing.
/// The folded read-back keeps the calls, so it stays small where the
/// unfolded one wouldn't.
///
/// With `STITCHWORT_DECIDE_BOTH` set, it also decides from the unfolded
/// read-back, undoes that, and reports on standard error where the two
/// decisions differ: a check that the folded read-back changes nothing.
pub fn decide(cx: &mut Ctx, prop: &Value, depth: usize) -> Result<Term> {
    let g = cx.g();
    if !g.machine.glue.get() {
        return decide_unglued(cx, prop, depth);
    }
    let both = std::env::var_os("STITCHWORT_DECIDE_BOTH").is_some();
    let unfolded = if both {
        let snapshot = crate::undo::Snapshot::take(cx);
        let written = cx.quote(prop);
        let found = decide_from(cx, written, depth);
        let shown = decided(cx, &found);
        snapshot.restore(cx);
        Some(shown)
    } else {
        None
    };
    let written = cx.quote_folded(prop);
    let found = decide_from(cx, written, depth);
    if let Some(unfolded) = unfolded {
        let folded = decided(cx, &found);
        if folded != unfolded {
            eprintln!(
                "decide differs on `{}`:\n  unfolded: {unfolded}\n  folded:   {folded}",
                cx.show(prop)
            );
        }
    }
    found
}

/// [`decide`] from the proposition read back as `written`, evaluated
/// unglued.
fn decide_from(cx: &mut Ctx, written: Result<Term>, depth: usize) -> Result<Term> {
    let g = cx.g();
    let written = written?;
    g.machine.glue.set(false);
    let found = cx
        .eval(&written)
        .and_then(|prop| decide_unglued(cx, &prop, depth));
    g.machine.glue.set(true);
    found
}

/// A decision's term with its solved unknowns filled in, or its error's
/// code and message, for [`decide`]'s comparison.
fn decided(cx: &Ctx, found: &Result<Term>) -> String {
    match found {
        Ok(term) => match cx.e.zonk_keeping(term, cx.level(), &|_| true) {
            Ok(term) => format!("{term:?}"),
            Err(e) => format!("{term:?} (unzonked: {})", e.message),
        },
        Err(e) => format!("error {}: {}", e.code, e.message),
    }
}

/// [`decide`], with gluing off.
fn decide_unglued(cx: &mut Ctx, prop: &Value, depth: usize) -> Result<Term> {
    let decidable = decidable(cx)?;
    // A relation from a dictionary: its paired decider, from the same one
    // (docs/proposals/interfaces.md §5.16 step 2).
    if let Some(term) = interfaces::relation_decider(cx, prop)? {
        return Ok(term);
    }
    if depth <= MAX_DEPTH {
        for id in decision_procedures(cx, decidable)? {
            let found = attempt(cx, |cx| instantiate(cx, id, decidable, prop, depth, false))?;
            if let Some(term) = found {
                return Ok(term);
            }
        }
    }
    // An equation: through `DecEq`.
    if let Value::Eq(ty, x, y) = force(&cx.g(), prop.clone())?
        && interfaces::dec_eq(cx.e).is_some()
    {
        return interfaces::decide_eq(cx, &ty, &x, &y);
    }
    let shown = cx.show(prop);
    let error = cx
        .error(
            "E-AUTO-NONE",
            format!("no way to decide `{shown}`"),
            "the compiler needs a proof of this",
        )
        .with_note("supply a proof by name, or write a decision procedure: an `instance` returning `Decidable …`");
    // A record of propositions whose decision couldn't be derived: why.
    let error = match force(&cx.g(), prop.clone())? {
        Value::Data(d, _) if cx.e.tables.no_decide.contains_key(&d) => error.with_note(format!(
            "`{}` has no derived decision: {}",
            cx.e.relative_to_root(cx.g().data(d).name()),
            cx.e.tables.no_decide[&d]
        )),
        _ => error,
    };
    let error =
        cx.e.auto_hints()
            .into_iter()
            .fold(error, Diagnostic::with_note);
    Err(unrelated_hints(cx, error, decidable, prop, depth)?)
}

/// Runs `f`, undoing what it did unless it succeeds (`undo.rs`).
/// `Ok(None)` means this way didn't work, so another may be tried. An error
/// (running out of resources, say) means stop.
fn attempt<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> Result<Option<T>>) -> Result<Option<T>> {
    crate::undo::transaction(cx, f)
}

/// A failed search for an argument means this candidate doesn't work, unless
/// it failed by running out of resources: then there's no answer, and the
/// search must stop rather than try something else.
fn give_up_on<T>(e: Diagnostic) -> Result<Option<T>> {
    if e.code == "E-RESOURCE" {
        Err(e)
    } else {
        Ok(None)
    }
}

fn decidable(cx: &Ctx) -> Result<DataId> {
    builtin_data(cx, Builtin::Decidable)
}

/// Definitions whose result type is `Decidable …`, in the order `auto` tries
/// them. In file mode, every definition, most recent first, but of the
/// library files only those the module needs. In a project
/// (docs/proposals/multi-file.md §4.9.5): this module's, most recent first;
/// then each namespace it depends on, the last in canonical order first, by
/// name within it; then those of the library files the module needs (not
/// those another module loaded), by name; then the prelude's, most recent
/// first. No other namespace's.
///
/// The part after this module's own definitions is worked out once and
/// remembered (`DecisionOrder`): the search runs for every `auto` argument,
/// and sorting the library's definitions each time was most of its cost
/// (SW-913).
fn decision_procedures(cx: &Ctx, decidable: DataId) -> Result<Vec<DefId>> {
    let g = cx.g();
    // Until the core has declared `DecEq`, every procedure is a candidate,
    // as before D163: the core's own uses of `==` come before it.
    let bootstrap = interfaces::dec_eq(cx.e).is_none();
    let first_def = cx.e.unit.module.first_def.min(g.env.defs().len());
    let earlier = earlier_candidates(cx.e, first_def, bootstrap);
    let own = (first_def..g.env.defs().len()).rev().map(DefId);
    let mut found = Vec::new();
    for id in own.chain(earlier.iter().copied()) {
        if !(g.def(id).instance() || bootstrap) || !cx.e.auto_eligible(id) {
            continue; // not marked, not checked yet, or below the use
        }
        if result_head(cx, id)? == Some(decidable) {
            found.push(id);
        }
    }
    Ok(found)
}

/// Decision procedure `id` applied to make a decision of `prop`, with its
/// own arguments found as `auto` finds them, if it fits.
pub(crate) fn instance_for(cx: &mut Ctx, id: DefId, prop: &Value) -> Result<Option<Term>> {
    let decidable = decidable(cx)?;
    attempt(cx, |cx| instantiate(cx, id, decidable, prop, 0, false))
}

/// What `decision_procedures` tries after the current module's own
/// definitions, in its order, with what that was worked out from
/// (`Elaborator::decision_order`).
///
/// The order depends only on the fields here and on the definitions below
/// `first_def`: earlier modules', library files' and the prelude's. So it is
/// reused while the fields are the same. Those definitions are never changed
/// once declared, and only a rewind removes them, which forgets the order.
/// (The check cache's undo of a failed replay also removes definitions, but
/// only ones declared during that replay, past every `first_def` seen
/// before it.) The current module's own definitions, which grow as it's
/// checked, aren't part of it.
///
/// It leaves out only what can never be a candidate: a checked or failed
/// definition not marked `instance` (outside the bootstrap, which is one of
/// the fields). A mark is only ever set while a definition is pending
/// (`kernel::mark_instance`), so pending ones stay in; everything else
/// (checked yet, written above the use, its result type) is still asked on
/// every call, as before.
pub(crate) struct DecisionOrder {
    first_def: usize,
    prelude_defs: usize,
    closure: Option<Vec<String>>,
    library_reach: Option<Rc<BTreeSet<usize>>>,
    namespace_defs: BTreeMap<String, Range<usize>>,
    bootstrap: bool,
    candidates: Rc<[DefId]>,
}

impl DecisionOrder {
    fn matches(&self, e: &Elaborator, first_def: usize, bootstrap: bool) -> bool {
        self.first_def == first_def
            && self.bootstrap == bootstrap
            && self.prelude_defs == e.tables.prelude_defs
            && self.closure == e.unit.module.closure
            && self.library_reach == e.unit.module.library_reach
            && self.namespace_defs == e.tables.namespace_defs
    }
}

/// `DecisionOrder::candidates` for the elaborator as it is now, remembered.
fn earlier_candidates(e: &Elaborator, first_def: usize, bootstrap: bool) -> Rc<[DefId]> {
    if let Some(order) = &*e.caches.decision_order.borrow()
        && order.matches(e, first_def, bootstrap)
    {
        return order.candidates.clone();
    }
    let g = &e.ev();
    // A library file's definition is a candidate only where the module
    // needs that file: what else the run loaded doesn't count (SW-1354).
    // The D58 exceptions decide only propositions that need their own file,
    // so leaving the others out loses nothing.
    let index = e.library_index();
    let reachable = |id: DefId| match (&index, &e.unit.module.library_reach) {
        (Some(index), Some(reach)) if id.0 >= e.tables.prelude_defs => index
            .owner_of_path(g.def(id).path())
            .is_none_or(|f| f == 0 || reach.contains(&f)),
        _ => true,
    };
    let ordered: Vec<DefId> = match &e.unit.module.closure {
        None => (0..first_def)
            .rev()
            .map(DefId)
            .filter(|id| reachable(*id))
            .collect(),
        Some(closure) => {
            let mut all = Vec::new();
            for namespace in closure.iter().rev() {
                let Some(range) = e.tables.namespace_defs.get(namespace) else {
                    continue;
                };
                let mut ids: Vec<DefId> = range.clone().map(DefId).collect();
                ids.sort_by(|a, b| g.def(*a).path().cmp(g.def(*b).path()));
                all.extend(ids);
            }
            // The library files' few procedures (`List.decMem`, the
            // equality of `Map`, `Set` and `Float`: the D58 exceptions,
            // each deciding only propositions that can't be written
            // without its file loaded), by name: every definition
            // outside the core that no namespace of the project made.
            // File mode sees them as it sees everything.
            let project: Vec<Range<usize>> = e.tables.namespace_defs.values().cloned().collect();
            let mut library: Vec<DefId> = (e.tables.prelude_defs..first_def)
                .filter(|id| !project.iter().any(|range| range.contains(id)))
                .map(DefId)
                .filter(|id| reachable(*id))
                .collect();
            library.sort_by(|a, b| g.def(*a).path().cmp(g.def(*b).path()));
            all.extend(library);
            all.extend((0..e.tables.prelude_defs).rev().map(DefId));
            all
        }
    };
    let candidates: Rc<[DefId]> = ordered
        .into_iter()
        .filter(|id| {
            let def = g.def(*id);
            def.instance() || bootstrap || def.state() == State::Pending
        })
        .collect();
    *e.caches.decision_order.borrow_mut() = Some(DecisionOrder {
        first_def,
        prelude_defs: e.tables.prelude_defs,
        closure: e.unit.module.closure.clone(),
        library_reach: e.unit.module.library_reach.clone(),
        namespace_defs: e.tables.namespace_defs.clone(),
        bootstrap,
        candidates: candidates.clone(),
    });
    candidates
}

/// In a project, what the error says about decision procedures in
/// namespaces that were checked but that this one doesn't use: they'd
/// fit, but `auto` won't look there. At most three.
fn unrelated_hints(
    cx: &mut Ctx,
    error: Diagnostic,
    decidable: DataId,
    prop: &Value,
    depth: usize,
) -> Result<Diagnostic> {
    let Some(closure) = cx.e.unit.module.closure.clone() else {
        return Ok(error);
    };
    let current = cx.e.unit.module.namespace.clone().unwrap_or_default();
    let mut error = error;
    let mut hints = 0;
    let namespaces: Vec<(String, std::ops::Range<usize>)> =
        cx.e.tables
            .namespace_defs
            .iter()
            .filter(|(name, _)| **name != current && !closure.contains(name))
            .map(|(name, range)| (name.clone(), range.clone()))
            .collect();
    for (namespace, range) in namespaces {
        let mut ids: Vec<DefId> = range.map(DefId).collect();
        ids.sort_by(|a, b| cx.g().def(*a).path().cmp(cx.g().def(*b).path()));
        for id in ids {
            if hints == 3 {
                return Ok(error);
            }
            if cx.g().def(id).body().is_none()
                || !cx.g().def(id).instance()
                || result_head(cx, id)? != Some(decidable)
            {
                continue;
            }
            let mut fits = false;
            attempt(cx, |cx| {
                fits = instantiate(cx, id, decidable, prop, depth, false)?.is_some();
                Ok(None::<()>)
            })?;
            if fits {
                let name = cx.g().def(id).name().to_string();
                let short = name
                    .strip_prefix(&format!("{namespace}."))
                    .unwrap_or(&name)
                    .to_string();
                error = error.with_note(format!(
                    "`{short}` is in `{namespace}`, which `{current}` doesn't use"
                ));
                hints += 1;
            }
        }
    }
    Ok(error)
}

/// The data type that definition `id`'s result type is, after all its
/// parameters, if it is one; remembered (`Elaborator::result_heads`). `id`
/// must be final (`auto_eligible`), so the answer never changes.
fn result_head(cx: &Ctx, id: DefId) -> Result<Option<DataId>> {
    let e = cx.e;
    if let Some(Some(head)) = e.caches.result_heads.borrow().get(id.0) {
        return Ok(*head);
    }
    let g = cx.g();
    let mut ty = g.def(id).ty_value().clone();
    let mut level = 0;
    while let Value::Pi(_, _, _, cod) = &ty {
        ty = force(&g, cod.apply(&g, Value::var(level))?)?;
        level += 1;
    }
    let head = match ty {
        Value::Data(d, _) => Some(d),
        _ => None,
    };
    let mut heads = e.caches.result_heads.borrow_mut();
    if heads.len() <= id.0 {
        heads.resize(g.env.defs().len(), None);
    }
    heads[id.0] = Some(head);
    Ok(head)
}

/// Applies decision procedure `id` to fresh unknowns, unifies its result with
/// `Decidable prop`, and fills in what's left: `Decidable` arguments by
/// recursive search, auto arguments by proof search. `as_written`: a call in
/// `prop` matches the same call in the procedure's result by its arguments,
/// before either is computed.
fn instantiate(
    cx: &mut Ctx,
    id: DefId,
    decidable: DataId,
    prop: &Value,
    depth: usize,
    as_written: bool,
) -> Result<Option<Term>> {
    let g = &cx.u();
    let mut ty = g.def(id).ty_value().clone();
    // Whether each parameter is mentioned by the ones after it or the
    // result: one that isn't needs no solution for its unknown.
    let mut mentioned = Vec::new();
    let mut written = g.def(id).ty().clone();
    while let Term::Pi(_, _, _, cod) = written.strip_loc() {
        mentioned.push(cod.mentions(0));
        written = (**cod).clone();
    }
    let mut args = Vec::new();
    let mut arg_terms = Vec::new();
    while let Value::Pi(_, icit, dom, cod) = force(g, ty.clone())? {
        // Typed, so unification's first-order rule won't pair it with a
        // value of another type: `?p Greater h` against `?x < ?y` would
        // solve `?x: Int` with `Greater`, and the test is run at once
        // ([`verdict`]), long before the kernel would refuse it (SW-2961).
        let meta = cx.fresh_meta_of(&dom);
        let value = cx.eval(&meta)?;
        args.push((value.clone(), icit, (*dom).clone()));
        arg_terms.push((meta, icit));
        ty = cod.apply(g, value)?;
    }
    let wanted = Value::Data(decidable, vec![prop.clone()].into());
    let fits = if as_written {
        crate::unify::unify_solving_arguments(g, cx.level(), &ty, &wanted)?
    } else {
        cx.unify(&ty, &wanted)?
    };
    if !fits {
        return Ok(None);
    }
    for (i, (value, icit, dom)) in args.into_iter().enumerate() {
        if !matches!(force(g, value.clone())?, Value::Neutral(Head::Meta(_), _)) {
            continue;
        }
        let found = match force(g, dom)? {
            Value::Data(d, params) if d == decidable => {
                let cost = if size(&g.ev, &params[0])? < size(&g.ev, prop)? {
                    1
                } else {
                    LEVEL
                };
                decide(cx, &params[0], depth + cost)
            }
            dom if icit == Icit::Auto => prove(cx, &dom, depth + LEVEL),
            _ => return Ok(None),
        };
        let found = match found {
            Ok(found) => found,
            Err(e) => return give_up_on(e),
        };
        // The decision as found goes in the term, not its unknown's
        // solution read back, and the unknown is solved only if something
        // after it depends on it: a decision is a record that computes to
        // its fields, each holding the decisions it was made from
        // (`Decidable.or dp dq`'s test and proofs all mention `dp` and
        // `dq`), so read back it grows with each level of nesting.
        if mentioned.get(i).copied().unwrap_or(true) && !cx.unify(&value, &cx.eval(&found)?)? {
            return Ok(None);
        }
        arg_terms[i].0 = found;
    }
    let term =
        (arg_terms.into_iter()).fold(Term::Def(id), |f, (arg, icit)| Term::app_icit(f, arg, icit));
    Ok(Some(term))
}

/// The number of data types, constructors and equations in a proposition: a
/// measure of whether one is part of another.
fn size(g: &Ev, value: &Value) -> Result<usize> {
    let sum = |parts: &[Value]| -> Result<usize> {
        let mut total = 1;
        for part in parts {
            total += size(g, part)?;
        }
        Ok(total)
    };
    Ok(match force(g, value.clone())? {
        Value::Data(_, parts) => sum(&parts)?,
        Value::Ctor(_, _, fields) => sum(&fields)?,
        Value::Eq(ty, x, y) => sum(&[(*ty).clone(), (*x).clone(), (*y).clone()])?,
        _ => 1,
    })
}
