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
//!    compile time, and must say `Yes`. The proof is then `fromYes d Trivial`,
//!    which the kernel re-checks by running `d` itself.
//!
//! Between 1 and 2, a lexicographic `decreasing` obligation, `Nat.LexLess a1
//! a2 b1 b2`, is split: `a1 < b1`, or else `a1` the same as `b1` and `a2 <
//! b2`, each proved this same way (docs/proposals/well-founded-recursion.md,
//! stage 3d).
//!
//! An obligation whose type is an interface applied to a type is an instance
//! to find instead (`interfaces.rs`, docs/proposals/interfaces.md §5.5).
//! One may have to wait, until solving others has said more about its type
//! or its candidates; obligations are retried in rounds while a round makes
//! progress.

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, builtin_ctor, builtin_data, builtin_def};
use crate::interfaces::{self, Attempt};

type Result<T> = std::result::Result<T, Diagnostic>;

/// How deep decision procedures may depend on each other.
const MAX_DEPTH: usize = 8;

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
        let mut waiting: Vec<(Obligation, Diagnostic)> = Vec::new();
        let mut progress = false;
        loop {
            let obligations = std::mem::take(&mut *self.obligations.borrow_mut());
            if obligations.is_empty() {
                // Row comparisons put aside: one that's settled now is
                // progress.
                if self.retry_rows()? {
                    progress = true;
                }
                if waiting.is_empty() {
                    return Ok(());
                }
                if !progress {
                    return Err(waiting.swap_remove(0).1);
                }
                progress = false;
                self.obligations
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
                            self.instance_waits.set(self.instance_waits.get() + 1);
                            waiting.push((ob, why))
                        }
                    }
                    continue;
                }
                let mut cx = Ctx::from_parts(self, ob.env, ob.types, ob.names, ob.span);
                let placeholder = cx.eval(&ob.meta)?;
                if !matches!(
                    force(cx.g(), placeholder.clone())?,
                    Value::Neutral(Head::Meta(_), _)
                ) {
                    continue; // already determined by unification
                }
                progress = true;
                let proof = match prove(&mut cx, &ob.goal, 0) {
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
            .obligations
            .borrow()
            .iter()
            .filter(|ob| matches!(ob.meta.spine().0, Term::Meta(m) if wanted(*m)))
            .map(|ob| ob.meta.clone())
            .collect();
        let mut proved = false;
        for meta in pending {
            let ob = {
                let obligations = self.obligations.borrow();
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
                force(cx.g(), placeholder.clone())?,
                Value::Neutral(Head::Meta(_), _)
            ) {
                continue;
            }
            if interfaces::interface_goal(self, &goal)?.is_some() {
                self.solve_now(&meta)?;
                let placeholder = cx.eval(&meta)?;
                proved |= !matches!(
                    force(cx.g(), placeholder)?,
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
    let goal = force(cx.g(), goal.clone())?;
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
    match force(cx.g(), cx.eval(&decision)?)? {
        Value::Ctor(_, 0, _) => {
            // `fromYes [p := goal] decision Trivial`
            let from_yes = builtin_def(cx, Builtin::FromYes)?;
            let (unit, trivial) = builtin_ctor(cx, Builtin::Trivial)?;
            let goal_term = cx.quote(&goal)?;
            Ok(Term::app(
                Term::app(
                    Term::app_icit(Term::Def(from_yes), goal_term, Icit::Implicit),
                    decision,
                ),
                Term::Ctor(unit, trivial, Vec::new()),
            ))
        }
        Value::Ctor(_, _, _) => Err(cx.error(
            "E-AUTO-FALSE",
            format!("`{shown}` is false"),
            "this needs a proof that can't exist",
        )),
        _ => Err(cx
            .error(
                "E-AUTO-STUCK",
                format!("can't decide `{shown}` here"),
                "it depends on values that aren't known until the program runs",
            )
            .with_note("establish it first, with `if h: … then … else …`")),
    }
}

/// A proof of `Nat.LexLess a1 a2 b1 b2`, what a recursive call of a
/// definition with `decreasing (m1, m2)` needs
/// (docs/proposals/well-founded-recursion.md, stage 3d): `a1 < b1`, or else
/// `a1` the same as `b1` and `a2 < b2`, each found the way any goal is.
/// `None` for any other goal, or when neither is found.
fn lex_less(cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Option<Term>> {
    let Some(lex) = cx.g().registry.data(Builtin::LexLess) else {
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
    let found = attempt(cx, |cx| match prove(cx, &first, depth + 1) {
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
        match prove(cx, &second, depth + 1) {
            Ok(proof) => Ok(Some(Term::ctor(lex, 1, vec![Term::Refl, proof]))),
            Err(e) => give_up_on(e),
        }
    })
}

/// A term of type `Decidable prop`, from the decision procedures in scope.
///
/// The search sees the unfolded proposition (D484,
/// docs/proposals/folded-calls.md): it runs with gluing off, on `prop`
/// read back and computed again unglued. Otherwise a procedure would be
/// matched against a call by its arguments before unfolding (`y < 10`
/// decided by `Nat.decLessThan y 10` rather than `Nat.decLessEq y 9`, as
/// `y < 10` computes to `y <= 9`), and the decisions found, and so the
/// elaborated terms, would depend on gluing.
pub fn decide(cx: &mut Ctx, prop: &Value, depth: usize) -> Result<Term> {
    let g = cx.g();
    if !g.glue.get() {
        return decide_unglued(cx, prop, depth);
    }
    let written = cx.quote(prop)?;
    g.glue.set(false);
    let found = cx
        .eval(&written)
        .and_then(|prop| decide_unglued(cx, &prop, depth));
    g.glue.set(true);
    found
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
            let found = attempt(cx, |cx| instantiate(cx, id, decidable, prop, depth))?;
            if let Some(term) = found {
                return Ok(term);
            }
        }
    }
    // An equation: through `DecEq`.
    if let Value::Eq(ty, x, y) = force(cx.g(), prop.clone())?
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
/// them. In file mode, every definition, most recent first. In a project
/// (docs/proposals/multi-file.md §4.9.5): this module's, most recent first;
/// then each namespace it depends on, the last in canonical order first, by
/// name within it; then the prelude's, most recent first. No other
/// namespace's.
fn decision_procedures(cx: &Ctx, decidable: DataId) -> Result<Vec<DefId>> {
    let g = cx.g();
    let candidates: Vec<DefId> = match &cx.e.module.closure {
        None => (0..g.defs.len()).rev().map(DefId).collect(),
        Some(closure) => {
            let mut all: Vec<DefId> = (cx.e.module.first_def..g.defs.len())
                .rev()
                .map(DefId)
                .collect();
            for namespace in closure.iter().rev() {
                let Some(range) = cx.e.namespace_defs.get(namespace) else {
                    continue;
                };
                let mut ids: Vec<DefId> = range.clone().map(DefId).collect();
                ids.sort_by(|a, b| g.def(*a).path.cmp(&g.def(*b).path));
                all.extend(ids);
            }
            all.extend((0..cx.e.prelude_defs).rev().map(DefId));
            all
        }
    };
    // Until the core has declared `DecEq`, every procedure is a candidate,
    // as before D163: the core's own uses of `==` come before it.
    let bootstrap = interfaces::dec_eq(cx.e).is_none();
    let mut found = Vec::new();
    for id in candidates {
        if !(g.def(id).instance || bootstrap) || !cx.e.auto_eligible(id) {
            continue; // not marked, not checked yet, or below the use
        }
        if result_head(cx, id)? == Some(decidable) {
            found.push(id);
        }
    }
    Ok(found)
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
    let Some(closure) = cx.e.module.closure.clone() else {
        return Ok(error);
    };
    let current = cx.e.module.namespace.clone().unwrap_or_default();
    let mut error = error;
    let mut hints = 0;
    let namespaces: Vec<(String, std::ops::Range<usize>)> =
        cx.e.namespace_defs
            .iter()
            .filter(|(name, _)| **name != current && !closure.contains(name))
            .map(|(name, range)| (name.clone(), range.clone()))
            .collect();
    for (namespace, range) in namespaces {
        let mut ids: Vec<DefId> = range.map(DefId).collect();
        ids.sort_by(|a, b| cx.g().def(*a).path.cmp(&cx.g().def(*b).path));
        for id in ids {
            if hints == 3 {
                return Ok(error);
            }
            if cx.g().def(id).body().is_none()
                || !cx.g().def(id).instance
                || result_head(cx, id)? != Some(decidable)
            {
                continue;
            }
            let mut fits = false;
            attempt(cx, |cx| {
                fits = instantiate(cx, id, decidable, prop, depth)?.is_some();
                Ok(None::<()>)
            })?;
            if fits {
                let name = cx.g().def(id).name.to_string();
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
    if let Some(Some(head)) = e.result_heads.borrow().get(id.0) {
        return Ok(*head);
    }
    let g = cx.g();
    let mut ty = g.def(id).ty_value.clone();
    let mut level = 0;
    while let Value::Pi(_, _, _, cod) = &ty {
        ty = force(g, cod.apply(g, Value::var(level))?)?;
        level += 1;
    }
    let head = match ty {
        Value::Data(d, _) => Some(d),
        _ => None,
    };
    let mut heads = e.result_heads.borrow_mut();
    if heads.len() <= id.0 {
        heads.resize(g.defs.len(), None);
    }
    heads[id.0] = Some(head);
    Ok(head)
}

/// Applies decision procedure `id` to fresh unknowns, unifies its result with
/// `Decidable prop`, and fills in what's left: `Decidable` arguments by
/// recursive search, auto arguments by proof search.
fn instantiate(
    cx: &mut Ctx,
    id: DefId,
    decidable: DataId,
    prop: &Value,
    depth: usize,
) -> Result<Option<Term>> {
    let g = cx.g();
    let mut term = Term::Def(id);
    let mut ty = g.def(id).ty_value.clone();
    let mut args = Vec::new();
    while let Value::Pi(_, icit, dom, cod) = force(g, ty.clone())? {
        let meta = cx.fresh_meta();
        let value = cx.eval(&meta)?;
        args.push((value.clone(), icit, (*dom).clone()));
        term = Term::app_icit(term, meta, icit);
        ty = cod.apply(g, value)?;
    }
    if !cx.unify(&ty, &Value::Data(decidable, vec![prop.clone()]))? {
        return Ok(None);
    }
    for (value, icit, dom) in args {
        if !matches!(force(g, value.clone())?, Value::Neutral(Head::Meta(_), _)) {
            continue;
        }
        let found = match force(g, dom)? {
            Value::Data(d, params) if d == decidable => decide(cx, &params[0], depth + 1),
            dom if icit == Icit::Auto => prove(cx, &dom, depth + 1),
            _ => return Ok(None),
        };
        let found = match found {
            Ok(found) => cx.eval(&found)?,
            Err(e) => return give_up_on(e),
        };
        if !cx.unify(&value, &found)? {
            return Ok(None);
        }
    }
    Ok(Some(term))
}
