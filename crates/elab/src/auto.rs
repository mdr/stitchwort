//! Finding proofs for `[auto x : P]` arguments (DESIGN.md §6).
//!
//! When an auto argument is inserted, the elaborator records an obligation and
//! carries on. Once the declaration has been elaborated, so unification has
//! worked out as much as it can, each obligation is proved, in this order:
//!
//! 1. a hypothesis in scope whose type is `P` (e.g. the `h` in
//!    `if h : d != 0 then n / d else 0`);
//! 2. a decision procedure for `P`: any definition whose result type is
//!    `Decidable …`, trying the most recently defined first (so a file's own
//!    procedures take priority over the prelude's). Only definitions that
//!    are already checked, and, in the same module, written above the use:
//!    declarations may be checked out of source order
//!    (docs/proposals/mutual-recursion.md §8.1), and one waiting for its
//!    dependencies isn't available yet. That's a deliberate limitation;
//!    passing a procedure explicitly makes it a dependency, checked first. Its arguments are found by unification, and any
//!    `Decidable` or auto arguments it needs are found recursively, as are
//!    decision procedures it takes as arguments (`(x y : a) -> Decidable
//!    (x = y)`, for `List.decEq`): `x y => …`, searched for with `x` and `y`
//!    in scope. Each recursive search is one deeper, up to `MAX_DEPTH`. It's run at
//!    compile time, and must say `Yes`. The proof is then `fromYes d Trivial`,
//!    which the kernel re-checks by running `d` itself.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, builtin_ctor, builtin_data, builtin_def};

type Result<T> = std::result::Result<T, Diagnostic>;

/// How deep decision procedures may depend on each other.
const MAX_DEPTH: usize = 8;

/// An auto argument still to be proved: the metavariable standing for it, its
/// type, and the context it was created in.
pub struct Obligation {
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    pub names: Vec<Name>,
    pub goal: Value,
    pub meta: Term,
    pub span: Span,
}

impl Elaborator {
    /// Proves every outstanding obligation.
    pub(crate) fn solve_obligations(&self) -> Result<()> {
        loop {
            let obligations = std::mem::take(&mut *self.obligations.borrow_mut());
            if obligations.is_empty() {
                return Ok(());
            }
            for ob in obligations {
                let mut cx = Ctx::from_parts(self, ob.env, ob.types, ob.names, ob.span);
                let placeholder = cx.eval(&ob.meta)?;
                if !matches!(
                    force(cx.g(), placeholder.clone())?,
                    Value::Neutral(Head::Meta(_), _)
                ) {
                    continue; // already determined by unification
                }
                let proof = prove(&mut cx, &ob.goal, 0)?;
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
            .map(|ob| {
                (
                    ob.env.clone(),
                    ob.types.clone(),
                    ob.names.clone(),
                    ob.goal.clone(),
                    ob.meta.clone(),
                    ob.span,
                )
            })
            .collect();
        let mut proved = false;
        for (env, types, names, goal, meta, span) in pending {
            let mut cx = Ctx::from_parts(self, env, types, names, span);
            let placeholder = cx.eval(&meta)?;
            if !matches!(
                force(cx.g(), placeholder.clone())?,
                Value::Neutral(Head::Meta(_), _)
            ) {
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

/// A proof of `goal`.
pub fn prove(cx: &mut Ctx, goal: &Value, depth: usize) -> Result<Term> {
    let goal = force(cx.g(), goal.clone())?;
    for level in (0..cx.level()).rev() {
        let ty = cx.types[level].clone();
        if attempt(cx, |cx| Ok(cx.unify(&ty, &goal)?.then_some(())))?.is_some() {
            return Ok(Term::Var(cx.level() - 1 - level));
        }
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

/// A term of type `Decidable prop`, from the decision procedures in scope.
pub fn decide(cx: &mut Ctx, prop: &Value, depth: usize) -> Result<Term> {
    let decidable = decidable(cx)?;
    // Why candidates that fit the goal didn't work, for the error.
    let mut reasons = Vec::new();
    if depth <= MAX_DEPTH {
        // Decision procedures passed in as arguments, for a generated `==`
        // on a type with parameters (`derive.rs`), and only there, so no
        // other search changes. They decide `=` on a parameter, which no
        // definition can, so they're tried first: a search through every
        // definition that fails is what's slow.
        if cx.e.local_deciders.get() {
            for level in (0..cx.level()).rev() {
                let ty = cx.types[level].clone();
                if !returns(cx, ty.clone(), decidable)? {
                    continue;
                }
                let head = Term::Var(cx.level() - 1 - level);
                let name = cx.names[level].to_string();
                let found = attempt(cx, |cx| {
                    instantiate_head(cx, head, ty, &name, decidable, prop, depth, &mut reasons)
                })?;
                if let Some(term) = found {
                    return Ok(term);
                }
            }
        }
        for id in decision_procedures(cx, decidable)? {
            let found = attempt(cx, |cx| {
                instantiate(cx, id, decidable, prop, depth, &mut reasons)
            })?;
            if let Some(term) = found {
                return Ok(term);
            }
        }
    }
    let shown = cx.show(prop);
    let error = cx
        .error(
            "E-AUTO-NONE",
            format!("no way to decide `{shown}`"),
            "the compiler needs a proof of this",
        )
        .with_note("supply a proof by name, or write a decision procedure: a function returning `Decidable …`");
    let error = reasons.into_iter().fold(error, Diagnostic::with_note);
    // `=` on a record whose `==` wasn't derived: say why.
    let error = match force(cx.g(), prop.clone())? {
        Value::Eq(ty, _, _) => match force(cx.g(), (*ty).clone())? {
            Value::Data(d, _) => match cx
                .e
                .records
                .get(&d)
                .and_then(|r| r.no_eq.as_ref())
                .or(cx.e.no_eq.get(&d))
            {
                Some(why) => error.with_note(format!(
                    "`==` isn't derived for `{}`: {why}",
                    cx.g().data(d).name
                )),
                None => error,
            },
            _ => error,
        },
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
    let mut found = Vec::new();
    for id in candidates {
        if !cx.e.auto_eligible(id) {
            continue; // not checked yet, or below the use
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
            if cx.g().def(id).body().is_none() || result_head(cx, id)? != Some(decidable) {
                continue;
            }
            let mut fits = false;
            attempt(cx, |cx| {
                let mut reasons = Vec::new();
                fits = instantiate(cx, id, decidable, prop, depth, &mut reasons)?.is_some();
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
        ty = cod.apply(g, Value::var(level))?;
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

/// For an argument of type `(x : A) -> (y : B) -> Decidable P` (a decision
/// procedure passed in, such as the one for elements that `List.decEq`
/// takes): `x y => d`, where `d` decides `P` with `x` and `y` in scope.
/// `None` if `ty` isn't such a type; if `P` can't be decided, the error and
/// what `P` is, for saying why.
///
/// It's a search one level deeper, like a `Decidable` argument's, so it's
/// bounded by `MAX_DEPTH` in the same way.
#[allow(clippy::type_complexity)]
fn decide_under(
    cx: &mut Ctx,
    ty: Value,
    decidable: DataId,
    depth: usize,
) -> Result<Option<std::result::Result<Term, (Diagnostic, String)>>> {
    let g = cx.g();
    let mark = cx.mark();
    let mut binders = Vec::new();
    let mut ty = ty;
    let prop = loop {
        match force(g, ty)? {
            Value::Pi(x, icit, dom, cod) => {
                let var = Value::var(cx.level());
                cx.bind_hidden(x.clone(), (*dom).clone());
                binders.push((x, icit));
                ty = cod.apply(g, var)?;
            }
            Value::Data(d, params) if d == decidable => break params[0].clone(),
            _ => {
                cx.reset(mark);
                return Ok(None);
            }
        }
    };
    let body = match decide(cx, &prop, depth) {
        Ok(body) => Ok(binders
            .into_iter()
            .rev()
            .fold(body, |body, (x, icit)| Term::Lam(x, icit, Rc::new(body)))),
        Err(e) => match describe(cx, &prop) {
            Ok(what) => Err((e, what)),
            Err(fatal) => Err((fatal, String::new())),
        },
    };
    cx.reset(mark);
    Ok(Some(body))
}

/// Joins the two parts of a note saying why a candidate didn't work, and
/// marks such notes, so they can be passed on from a search inside another.
const GIVEN: &str = ", given a way to decide ";

/// `prop`, for a note: `=` on its type, if it's an equation.
fn describe(cx: &Ctx, prop: &Value) -> Result<String> {
    Ok(match force(cx.g(), prop.clone())? {
        Value::Eq(ty, _, _) => format!("`=` on `{}`", cx.show(&ty)),
        prop => format!("`{}`", cx.show(&prop)),
    })
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
    reasons: &mut Vec<String>,
) -> Result<Option<Term>> {
    let g = cx.g();
    let (ty, name) = (g.def(id).ty_value.clone(), g.def(id).name.to_string());
    instantiate_head(
        cx,
        Term::Def(id),
        ty,
        &name,
        decidable,
        prop,
        depth,
        reasons,
    )
}

/// Whether `ty`, after its arguments, is `Decidable …`.
fn returns(cx: &Ctx, ty: Value, decidable: DataId) -> Result<bool> {
    let g = cx.g();
    let mut ty = ty;
    let mut level = cx.level();
    loop {
        match force(g, ty)? {
            Value::Pi(_, _, _, cod) => {
                ty = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            Value::Data(d, _) => return Ok(d == decidable),
            _ => return Ok(false),
        }
    }
}

/// [`instantiate`] for any function `head` of type `ty`, called `name` in
/// notes.
#[allow(clippy::too_many_arguments)]
fn instantiate_head(
    cx: &mut Ctx,
    head: Term,
    ty: Value,
    name: &str,
    decidable: DataId,
    prop: &Value,
    depth: usize,
    reasons: &mut Vec<String>,
) -> Result<Option<Term>> {
    let g = cx.g();
    let mut term = head;
    let mut ty = ty;
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
            dom @ Value::Pi(..) => match decide_under(cx, dom, decidable, depth + 1)? {
                Some(Ok(found)) => Ok(found),
                Some(Err((e, inner))) => {
                    if e.code == "E-AUTO-NONE" {
                        let outer = describe(cx, prop)?;
                        reasons.push(format!("`{name}` could decide {outer}{GIVEN}{inner}"));
                        reasons.extend(e.notes.iter().filter(|n| n.contains(GIVEN)).cloned());
                    }
                    Err(e)
                }
                None => return Ok(None),
            },
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
