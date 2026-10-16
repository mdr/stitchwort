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
//!    `Decidable` or auto arguments it needs are found recursively. It's run at
//!    compile time, and must say `Yes`. The proof is then `fromYes d Trivial`,
//!    which the kernel re-checks by running `d` itself.

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
            .with_note("establish it first, with `if h : … then … else …`")),
    }
}

/// A term of type `Decidable prop`, from the decision procedures in scope.
pub fn decide(cx: &mut Ctx, prop: &Value, depth: usize) -> Result<Term> {
    let decidable = decidable(cx)?;
    if depth <= MAX_DEPTH {
        for id in decision_procedures(cx, decidable)? {
            if let Some(term) = attempt(cx, |cx| instantiate(cx, id, decidable, prop, depth))? {
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
    // `=` on a record whose `==` wasn't derived: say why.
    let error = match force(cx.g(), prop.clone())? {
        Value::Eq(ty, _, _) => match force(cx.g(), (*ty).clone())? {
            Value::Data(d, _) => match cx.e.records.get(&d).and_then(|r| r.no_eq.as_ref()) {
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
    Err(cx
        .e
        .auto_hints()
        .into_iter()
        .fold(error, Diagnostic::with_note))
}

/// Runs `f`, undoing any metavariable solutions it made unless it succeeds.
/// `Ok(None)` means this way didn't work, so another may be tried. An error
/// (running out of resources, say) means stop.
fn attempt<T>(cx: &mut Ctx, f: impl FnOnce(&mut Ctx) -> Result<Option<T>>) -> Result<Option<T>> {
    let snapshot = cx.g().metas.borrow().clone();
    let result = f(cx);
    if !matches!(result, Ok(Some(_))) {
        *cx.g().metas.borrow_mut() = snapshot;
    }
    result
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

/// Definitions whose result type is `Decidable …`, most recent first.
fn decision_procedures(cx: &Ctx, decidable: DataId) -> Result<Vec<DefId>> {
    let g = cx.g();
    let mut found = Vec::new();
    for id in (0..g.defs.len()).rev().map(DefId) {
        let def = g.def(id);
        if !cx.e.auto_eligible(id) {
            continue; // not checked yet, or below the use
        }
        let mut ty = def.ty_value.clone();
        let mut level = 0;
        while let Value::Pi(_, _, _, cod) = &ty {
            ty = cod.apply(g, Value::var(level))?;
            level += 1;
        }
        if matches!(ty, Value::Data(d, _) if d == decidable) {
            found.push(id);
        }
    }
    Ok(found)
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
