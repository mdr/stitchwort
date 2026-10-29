//! `cases` and `cases in t` (docs/syntax.md, "cases"; docs/proposals/simp.md
//! §5): a proof by case splitting on what the goal, and the hypotheses that
//! say "this is a constructor", are stuck on.
//!
//! ```text
//! split          -- split until each case is closed automatically
//! split in t     -- and try `t` in each case
//! ```
//!
//! At each case (a *node*), the closers are tried, cheapest first (§5.4):
//!
//! 1. **computation**: the goal is an equation whose sides compute to the
//!    same thing (`rfl`);
//! 2. **contradiction**: a hypothesis is an equation between different
//!    constructors (`False = True`), refuted by `J` along it into a family
//!    that is `Unit` at one constructor and `Void` at the other;
//! 3. **taking an equation apart**: a hypothesis `C a = C b` adds `a = b`
//!    (by `J` along it with a projection), and the node starts again;
//! 4. **a hypothesis** of exactly the goal's type;
//! 5. **`t`**, for `cases in t`, elaborated in the case;
//! 6. **`omega`**, only where nothing is left to split (D1319).
//!
//! If none closes it, `cases` finds an *atom* (§5.2): following what the
//! goal is stuck on inwards (a definition's case tree, run on its arguments,
//! stops at a `case` on a stuck value; that value may itself be a stuck call,
//! and so on), the innermost value whose type is *splittable* (data with two
//! or more constructors, not recursive, not an indexed family, not a
//! proposition). A one-constructor type (a record) is split only when
//! nothing else is stuck. The goal is searched first, then the hypotheses
//! that are an equation between a constructor and a stuck term (D1318),
//! latest first. Unfolding doesn't make a new atom: the atom is the value
//! the case tree tested, so `Float.isNaN x`, not its body.
//!
//! The split is the generated `match` that `match e: atom with` writes
//! (`matching::generalised_named`, lifted as `owner.%matchN`), one
//! alternative per constructor, the equation bound as `%splitN`, and each
//! alternative's body is this `cases` again: so the proof is ordinary
//! `match`es and the closers' terms, and the kernel checks it as such.
//!
//! A case nothing closes, with nothing left to split, is `E-CASES`, showing
//! the path of choices to it and the hypotheses in scope (only the latest
//! copy of each, as generalising copies them). More than [`CASES`] cases is
//! `E-CASES-BUDGET`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{
    Elim, Head, body_seen, conv, eval, force, is_folded, quote, unfold_folded,
};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Result, builtin_ctor, builtin_data, builtin_def};

/// The most cases one `cases` makes (§5.8): the largest tree the motivating
/// proofs need has 12.
pub(crate) const CASES: usize = 64;

/// The prefix of the names the split equations are bound to: not one a
/// program can write.
const EQUATION: &str = "%case";

/// One `cases`, while its cases are checked.
pub(crate) struct Run {
    /// `t`, for `cases in t`.
    body: Option<Box<Expr>>,
    /// The `cases` as written: the alternatives' bodies are `cases`s with
    /// this span, which continue this one.
    span: Span,
    /// Cases made so far.
    cases: Cell<usize>,
    /// The atoms split on, as shown, in the order first split.
    atoms: RefCell<Vec<String>>,
    /// How the closed cases were closed.
    closed: RefCell<Closed>,
    /// Set once the budget is exceeded: every case after that fails at once.
    over: Cell<bool>,
    /// The first case still open when the budget ran out, as shown.
    open_at: RefCell<Option<String>>,
    /// Facts added by taking equations apart, for their names.
    facts: Cell<usize>,
    /// Whether each data type is splittable, and its constructor count.
    splittable: RefCell<HashMap<DataId, Option<usize>>>,
}

#[derive(Default)]
struct Closed {
    computation: usize,
    contradiction: usize,
    hypothesis: usize,
    term: usize,
    omega: usize,
}

impl Closed {
    fn total(&self) -> usize {
        self.computation + self.contradiction + self.hypothesis + self.term + self.omega
    }

    fn describe(&self) -> String {
        let parts: Vec<String> = [
            (self.computation, "by computation"),
            (self.contradiction, "by contradiction"),
            (self.hypothesis, "by a hypothesis"),
            (self.term, "by the term after `in`"),
            (self.omega, "by `omega`"),
        ]
        .iter()
        .filter(|(n, _)| *n > 0)
        .map(|(n, how)| format!("{n} {how}"))
        .collect();
        parts.join(", ")
    }
}

/// `cases` where nothing says what it should prove.
pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-CASES", "`cases` needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(cases: P)`")
}

/// `cases` against the goal `expected`.
pub(crate) fn check_cases(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Cases { body, span } = expr else {
        unreachable!("only called on `cases`")
    };
    // An alternative of a split this `cases` made: go on splitting.
    if let Some(run) = cx.cases.clone()
        && run.span == *span
    {
        return node(cx, &run, expected);
    }
    let run = Rc::new(Run {
        body: body.clone(),
        span: *span,
        cases: Cell::new(1),
        atoms: RefCell::new(Vec::new()),
        closed: RefCell::new(Closed::default()),
        over: Cell::new(false),
        open_at: RefCell::new(None),
        facts: Cell::new(0),
        splittable: RefCell::new(HashMap::default()),
    });
    let saved = cx.cases.replace(run.clone());
    let errors = cx.e.branch_errors.borrow().len();
    let result = node(cx, &run, expected);
    cx.cases = saved;
    let error = match result {
        Ok(term) => return Ok(term),
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(e) => e,
    };
    // The other cases that failed were kept for the definition to report
    // after this one (`check_tree`): one error says it for the `cases`.
    let others = cx.e.branch_errors.borrow().len() - errors;
    cx.e.branch_errors.borrow_mut().truncate(errors);
    if run.over.get() {
        return Err(budget_error(&run));
    }
    let closed = run.closed.borrow();
    let mut error = error;
    if others > 0 {
        error = error.with_note(format!(
            "{others} other case{} couldn't be closed either",
            if others == 1 { "" } else { "s" }
        ));
    }
    if closed.total() > 0 {
        error = error.with_note(format!(
            "{} other case{} {} closed ({})",
            closed.total(),
            if closed.total() == 1 { "" } else { "s" },
            if closed.total() == 1 { "was" } else { "were" },
            closed.describe()
        ));
    }
    Err(error)
}

fn budget_error(run: &Run) -> Diagnostic {
    let atoms = run.atoms.borrow();
    let mut d = Diagnostic::error(
        "E-CASES-BUDGET",
        format!("`cases` made more than {CASES} cases without closing them all"),
    )
    .with_label(run.span, "this `cases`")
    .with_note(format!(
        "it split on {}: {}",
        atoms.len(),
        atoms
            .iter()
            .map(|a| format!("`{a}`"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    if let Some(open) = &*run.open_at.borrow() {
        d = d.with_note(format!("the first case still open: {open}"));
    }
    d.with_note(
        "prove a fact that decides some of the cases at once and give it as `cases in t`, \
         or split by hand with `match`",
    )
}

/// One case: close it, or split it.
fn node(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Term> {
    if run.over.get() {
        return Err(Diagnostic::error("E-CASES-BUDGET", "over budget"));
    }
    if let Some(term) = by_computation(cx, goal)? {
        run.closed.borrow_mut().computation += 1;
        return Ok(term);
    }
    if let Some(term) = by_contradiction(cx, goal)? {
        run.closed.borrow_mut().contradiction += 1;
        return Ok(term);
    }
    if let Some(term) = take_apart(cx, run, goal)? {
        return Ok(term);
    }
    if let Some(term) = by_hypothesis(cx, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    let mut failed_body = None;
    if let Some(body) = &run.body {
        let snapshot = crate::undo::Snapshot::take(cx);
        let errors = cx.e.branch_errors.borrow().len();
        match crate::check::check(cx, body, goal) {
            Ok(term) => {
                run.closed.borrow_mut().term += 1;
                return Ok(term);
            }
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => {
                cx.e.branch_errors.borrow_mut().truncate(errors);
                snapshot.restore(cx);
                failed_body = Some(e);
            }
        }
    }
    let (atom, stuck) = {
        let mut finder = Finder::new(cx, run);
        let atom = finder.find(goal)?;
        (atom, finder.stuck.take())
    };
    if let Some(atom) = atom {
        // Splitting on the goal's own side (`Nat.leq a b = True` into
        // `True = True` and `False = True`) is the last resort: `omega` may
        // prove it whole, which is one case instead of two.
        if atom.side
            && let Some(term) = crate::omega::prove_case(cx, goal, run.span)?
        {
            run.closed.borrow_mut().omega += 1;
            return Ok(term);
        }
        return split_on(cx, run, atom, goal);
    }
    let found = crate::omega::prove_case(cx, goal, run.span)?;
    if let Some(term) = found {
        run.closed.borrow_mut().omega += 1;
        return Ok(term);
    }
    Err(open_case(cx, run, goal, stuck, failed_body))
}

/// The equations of the splits made on the way to this case, oldest first,
/// as shown: the latest copy of each.
fn path(cx: &Ctx) -> Vec<String> {
    (0..cx.level())
        .filter(|&l| is_equation(cx, l) && cx.name_of_level(l).is_some())
        .map(|l| cx.show(&cx.types[l]))
        .collect()
}

/// Whether the variable at `level` is a hypothesis a generalising `match`
/// has copied: it can't be referred to, and a later variable of the same
/// name can.
pub(crate) fn stale(cx: &Ctx, level: usize) -> bool {
    cx.name_of_level(level).is_none()
        && (level + 1..cx.level())
            .any(|l| cx.names[l] == cx.names[level] && cx.name_of_level(l).is_some())
}

fn is_equation(cx: &Ctx, level: usize) -> bool {
    cx.names[level].starts_with(EQUATION)
}

/// `E-CASES` for a case nothing closed, with nothing left to split.
fn open_case(
    cx: &Ctx,
    run: &Run,
    goal: &Value,
    stuck: Option<(String, String)>,
    failed_body: Option<Diagnostic>,
) -> Diagnostic {
    let path = path(cx);
    let case = if path.is_empty() {
        String::new()
    } else {
        path.join(", ")
    };
    if let Some(e) = failed_body {
        let note = if case.is_empty() {
            "`cases` found nothing to split on, and this is what the term after `in` gave"
                .to_string()
        } else {
            format!("in the case {case}, this is what the term after `in` gave")
        };
        return e.with_note(note);
    }
    let mut d = if case.is_empty() {
        Diagnostic::error(
            "E-CASES",
            "`cases` found nothing to split on, and nothing closes the goal",
        )
        .with_label(run.span, "this `cases`")
    } else {
        Diagnostic::error("E-CASES", format!("`cases` can't close the case {case}"))
            .with_label(run.span, "this `cases`")
    };
    for level in 0..cx.level() {
        if is_equation(cx, level) {
            continue;
        }
        let Some(name) = cx.name_of_level(level) else {
            continue;
        };
        if is_fact(cx, &cx.types[level]) {
            d = d.with_note(format!("{name}: {}", cx.show(&cx.types[level])));
        }
    }
    d = d.with_note(format!("goal: {}", cx.show(goal)));
    // The case's own equations hold the atoms split on, where an unused
    // equation's left side may be (SW-882).
    let mut searched = vec![goal];
    searched.extend(
        (0..cx.level())
            .filter(|&l| is_equation(cx, l))
            .map(|l| &cx.types[l]),
    );
    d = cx.with_unused_equation_notes(d, &searched);
    match stuck {
        Some((what, ty)) => d.with_note(format!(
            "it stopped here because the goal is stuck on `{what}`, a `{ty}`, which `cases` \
             doesn't take apart; give this case's proof as `cases in t`"
        )),
        None => d.with_note(
            "the goal isn't stuck on anything `cases` can take apart, and neither `rfl`, a \
             contradiction, a hypothesis nor `omega` proves it; give this case's proof as \
             `cases in t`",
        ),
    }
}

/// Whether a hypothesis of type `ty` is worth showing: a proposition, as
/// far as can be told cheaply (an equation, or a type of proofs).
fn is_fact(cx: &Ctx, ty: &Value) -> bool {
    match force(cx.g(), ty.clone()) {
        Ok(Value::Eq(..)) => true,
        Ok(Value::Data(d, _)) => cx.g().data(d).sort == Sort::Prop,
        Ok(Value::Neutral(Head::Def(_), _)) => true,
        _ => false,
    }
}

// The closers.

fn by_computation(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    if let Value::Eq(_, l, r) = force(cx.g(), goal.clone())?
        && cx.conv_now(&l, &r)?
    {
        return Ok(Some(Term::Refl));
    }
    Ok(None)
}

/// The hypotheses that can be referred to, by level, latest first: a
/// variable's latest copy, never a stale one.
fn visible(cx: &Ctx) -> Vec<usize> {
    (0..cx.level())
        .rev()
        .filter(|&l| cx.name_of_level(l).is_some())
        .collect()
}

fn by_hypothesis(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    let levels = visible(cx);
    let found = |l: usize| Ok(Some(Term::Var(cx.level() - 1 - l)));
    for &level in &levels {
        if conv(cx.g(), cx.level(), &cx.types[level], goal)? {
            return found(level);
        }
    }
    // Again with what's been solved since the goal or a hypothesis was
    // computed (`Ctx::conv_now`), the goal computed again only once.
    if cx.g().meta_trail.borrow().is_empty() {
        return Ok(None);
    }
    let goal = crate::interfaces::refresh(cx, goal)?;
    for level in levels {
        let ty = crate::interfaces::refresh(cx, &cx.types[level])?;
        if conv(cx.g(), cx.level(), &ty, &goal)? {
            return found(level);
        }
    }
    Ok(None)
}

/// An equation `l = r` of data `d` whose sides compute to constructors.
struct CtorEquation {
    level: usize,
    ty: Value,
    d: DataId,
    left: (usize, Vec<Value>),
    right: (usize, Vec<Value>),
}

fn ctor_equations(cx: &Ctx) -> Result<Vec<CtorEquation>> {
    let mut out = Vec::new();
    for level in visible(cx) {
        out.extend(ctor_equation(cx, level)?);
    }
    Ok(out)
}

/// The variable at `level`, if its type equates two constructors of a data
/// type that isn't a proposition or an indexed family.
fn ctor_equation(cx: &Ctx, level: usize) -> Result<Option<CtorEquation>> {
    let g = cx.g();
    let Value::Eq(ty, l, r) = force(g, cx.types[level].clone())? else {
        return Ok(None);
    };
    let (Value::Ctor(d, c1, f1), Value::Ctor(d2, c2, f2)) =
        (force(g, (*l).clone())?, force(g, (*r).clone())?)
    else {
        return Ok(None);
    };
    if d != d2 || g.data(d).sort == Sort::Prop || !g.data(d).indices.is_empty() {
        return Ok(None);
    }
    Ok(Some(CtorEquation {
        level,
        ty: (*ty).clone(),
        d,
        left: (c1, f1.to_vec()),
        right: (c2, f2.to_vec()),
    }))
}

/// A proof of `goal` from the variable at `level`, when its type equates
/// two different constructors (an argument matched by `()`).
pub(crate) fn refute_equation(cx: &mut Ctx, level: usize, goal: &Value) -> Result<Option<Term>> {
    match ctor_equation(cx, level)? {
        Some(eq) if eq.left.0 != eq.right.0 => contradiction(cx, eq, goal).map(Some),
        _ => Ok(None),
    }
}

fn by_contradiction(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    let Some(eq) = ctor_equations(cx)?
        .into_iter()
        .find(|e| e.left.0 != e.right.0)
    else {
        return Ok(None);
    };
    contradiction(cx, eq, goal).map(Some)
}

/// `Void.exfalso` (or `Void.absurd`, for a goal that isn't a proposition)
/// of `J (y q => D y) Trivial h`, where `D` is a helper that is `Unit` at
/// `h`'s left constructor and `Void` at the others.
fn contradiction(cx: &mut Ctx, eq: CtorEquation, goal: &Value) -> Result<Term> {
    let g = cx.g();
    let h = Term::Var(cx.level() - 1 - eq.level);
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    let void_proof = if eq.d == bool_data {
        // `Bool.falseNotTrue h`, or for `h: True = False`, of `h` turned
        // round by `J (y q => y = True) rfl h`.
        let tru = builtin_ctor(cx, Builtin::True)?;
        let false_true = if eq.left.0 == tru.1 {
            let motive_body = Term::Eq(
                Some(Rc::new(Term::data(bool_data, Vec::new()))),
                Rc::new(Term::Var(1)),
                Rc::new(Term::ctor(tru.0, tru.1, Vec::new())),
            );
            let motive = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(motive_body))),
            );
            Term::J(Rc::new(motive), Rc::new(Term::Refl), Rc::new(h))
        } else {
            h
        };
        Term::app(
            Term::Def(builtin_def(cx, Builtin::FalseNotTrue)?),
            false_true,
        )
    } else {
        let unit = builtin_data(cx, Builtin::Unit)?;
        let void = builtin_data(cx, Builtin::Void)?;
        let trivial = builtin_ctor(cx, Builtin::Trivial)?;
        let data = g.data(eq.d);
        let branches: Vec<Branch> = data
            .ctors
            .iter()
            .enumerate()
            .map(|(c, ctor)| Branch {
                names: ctor.fields.iter().map(|(n, _)| n.clone()).collect(),
                body: Some(Rc::new(Term::data(
                    if c == eq.left.0 { unit } else { void },
                    Vec::new(),
                ))),
            })
            .collect();
        let left = force(g, cx.types[eq.level].clone())?;
        let Value::Eq(_, l, _) = left else {
            unreachable!("an equation")
        };
        let motive = family(cx, &eq.ty, &l, eq.d, branches, &Value::Sort(Sort::Prop))?;
        Term::J(
            Rc::new(motive),
            Rc::new(Term::ctor(trivial.0, trivial.1, Vec::new())),
            Rc::new(h),
        )
    };
    let goal_term = cx.quote_folded(goal)?;
    let (via, implicit) = if is_proposition(cx, goal)? {
        (builtin_def(cx, Builtin::VoidExfalso)?, goal_term)
    } else {
        (builtin_def(cx, Builtin::VoidAbsurd)?, goal_term)
    };
    Ok(Term::app(
        Term::app_icit(Term::Def(via), implicit, Icit::Implicit),
        void_proof,
    ))
}

/// `y q => helper … y`, a motive for `J` along an equation `l = y` of type
/// `ty`, where the helper is lifted with the case tree `case y of branches`
/// (of type `result`, which mustn't mention `y`).
fn family(
    cx: &mut Ctx,
    ty: &Value,
    l: &Value,
    d: DataId,
    branches: Vec<Branch>,
    result: &Value,
) -> Result<Term> {
    let mark = cx.mark();
    let y = cx.level();
    cx.bind_hidden("y".into(), ty.clone());
    cx.bind_hidden(
        "q".into(),
        Value::Eq(
            Rc::new(ty.clone()),
            Rc::new(l.clone()),
            Rc::new(Value::var(y)),
        ),
    );
    let body = Term::Case(1, d, branches.into());
    let call = crate::lift::draft(cx, cx.level(), Vec::new(), body, result, cx.span);
    cx.reset(mark);
    let call = call?;
    Ok(Term::Lam(
        "y".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(call))),
    ))
}

pub(crate) fn is_proposition(cx: &Ctx, goal: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(g, goal.clone())? {
        Value::Eq(..) => true,
        Value::Data(d, _) => g.data(d).sort == Sort::Prop,
        other => {
            let term = cx.quote(&other)?;
            let mut kcx = crate::rewrite::kernel_context(cx)?;
            match crate::kernel::without_glue(g, || crate::kernel::infer(&mut kcx, &term)) {
                Ok((_, ty)) => matches!(force(g, ty)?, Value::Sort(Sort::Prop)),
                Err(e) if crate::undo::fatal(&e) => return Err(e),
                Err(_) => true,
            }
        }
    })
}

/// A hypothesis `C a1 … = C b1 …` adds `ai = bi` for each field that
/// differs and isn't known equal already (§5.4, 3), as `let`s, and the case
/// starts again with them. `None` if there's nothing to add.
fn take_apart(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let mut facts: Vec<(usize, usize, Value, Value, Value)> = Vec::new();
    for eq in ctor_equations(cx)? {
        if eq.left.0 != eq.right.0 {
            continue;
        }
        let ctor = &g.data(eq.d).ctors[eq.left.0];
        for (i, (a, b)) in eq.left.1.iter().zip(&eq.right.1).enumerate() {
            if ctor.field_erased.get(i).copied().unwrap_or(false)
                || mentions_fields(&ctor.fields[i].1, i)
                || conv(g, cx.level(), a, b)?
            {
                continue;
            }
            let Value::Data(_, params) = force(g, eq.ty.clone())? else {
                continue;
            };
            let field_ty = eval(g, &params, &ctor.fields[i].1)?;
            let fact = Value::Eq(
                Rc::new(field_ty.clone()),
                Rc::new(a.clone()),
                Rc::new(b.clone()),
            );
            if visible(cx)
                .into_iter()
                .any(|l| conv(g, cx.level(), &cx.types[l], &fact).unwrap_or(false))
            {
                continue;
            }
            facts.push((eq.level, i, a.clone(), field_ty, fact));
        }
    }
    if facts.is_empty() {
        return Ok(None);
    }
    let mark = cx.mark();
    let mut lets = Vec::new();
    for (level, i, a, field_ty, fact) in facts {
        let Value::Eq(ty, l, _) = force(g, cx.types[level].clone())? else {
            unreachable!("an equation")
        };
        let Value::Data(d, _) = force(g, (*ty).clone())? else {
            unreachable!("data")
        };
        let data = g.data(d);
        let Value::Ctor(_, c, _) = force(g, (*l).clone())? else {
            unreachable!("a constructor")
        };
        // `case y of C … fi … => fi | _ => a`, under each branch's fields.
        let a_term = cx.quote(&a)?;
        let mut branches = Vec::new();
        for (k, ctor) in data.ctors.iter().enumerate() {
            let fields = ctor.fields.len();
            // The branch is under y, q and the fields.
            let body = if k == c {
                Term::Var(fields - 1 - i)
            } else {
                a_term.shift(g, 2 + fields, 0)?
            };
            branches.push(Branch {
                names: ctor.fields.iter().map(|(n, _)| n.clone()).collect(),
                body: Some(Rc::new(body)),
            });
        }
        let project = family(cx, &ty, &l, d, branches, &field_ty)?;
        // `J (y q => a = project y) rfl h : a = project r`, which computes to
        // `a = b`.
        let Term::Lam(_, _, inner) = &project else {
            unreachable!("a lambda")
        };
        let Term::Lam(_, _, call) = &**inner else {
            unreachable!("a lambda")
        };
        let motive_body = Term::Eq(
            Some(Rc::new(cx.quote(&field_ty)?.shift(g, 2, 0)?)),
            Rc::new(a_term.shift(g, 2, 0)?),
            call.clone(),
        );
        let motive = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::Lam("q".into(), Icit::Explicit, Rc::new(motive_body))),
        );
        let proof = Term::J(
            Rc::new(motive),
            Rc::new(Term::Refl),
            Rc::new(Term::Var(cx.level() - 1 - level)),
        );
        let fact_term = cx.quote(&fact)?;
        run.facts.set(run.facts.get() + 1);
        let name = format!("%fact{}", run.facts.get());
        lets.push((Name::from(name.as_str()), fact_term.clone(), proof.clone()));
        cx.define(Some(&name), name.as_str().into(), fact, fact_term, proof)?;
    }
    let body = node(cx, run, goal);
    cx.reset(mark);
    let mut body = body?;
    for (name, ty, value) in lets.into_iter().rev() {
        body = Term::let_(name, ty, value, body);
    }
    Ok(Some(body))
}

/// Whether field type `ty` (in the context of the parameters and the
/// previous `i` fields) mentions a previous field.
fn mentions_fields(ty: &Term, i: usize) -> bool {
    ty.subterms().any(|(t, under)| {
        matches!(t, Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..)
            if *ix >= under && *ix - under < i)
    })
}

// Finding what to split on.

/// What to split on: a value the goal or a hypothesis is stuck on, of data
/// type `d`.
struct Atom {
    value: Value,
    d: DataId,
    /// Whether it is a whole side of the goal's equation (`f x = True`), not
    /// something a definition tests.
    side: bool,
}

struct Finder<'a, 'e> {
    cx: &'a Ctx<'e>,
    run: &'a Run,
    /// The first one-constructor atom met, split only if nothing else is.
    single: Option<Atom>,
    /// The innermost value the goal is stuck on that isn't splittable, and
    /// its type, as shown: why a case with nothing to split stopped.
    stuck: Option<(String, String)>,
    /// The split equations' left sides, as types hold them: values known
    /// in this case, never split again.
    known: Vec<Term>,
    /// Values visited, against runaway sharing.
    visits: usize,
    in_goal: bool,
    /// How many stuck calls' arguments the walk is inside: a record
    /// is split only outside them.
    under_stuck: usize,
}

/// The most values the search for an atom visits in one case.
const VISITS: usize = 100_000;

impl<'a, 'e> Finder<'a, 'e> {
    fn new(cx: &'a Ctx<'e>, run: &'a Run) -> Self {
        let mut known = Vec::new();
        for level in 0..cx.level() {
            if !is_equation(cx, level) {
                continue;
            }
            if let Ok(Value::Eq(_, l, _)) = force(cx.g(), cx.types[level].clone())
                && let Ok(t) = quote(cx.g(), cx.level(), &l)
            {
                known.push(t);
            }
        }
        Finder {
            cx,
            run,
            single: None,
            stuck: None,
            known,
            visits: 0,
            in_goal: false,
            under_stuck: 0,
        }
    }

    /// The atom to split on in this case, if any (§5.2, §5.3).
    fn find(&mut self, goal: &Value) -> Result<Option<Atom>> {
        let cx = self.cx;
        let g = cx.g();
        self.in_goal = true;
        // The goal's whole side (`Nat.leq n 2 = True` on `Nat.leq n 2`) waits
        // for the hypotheses: what they are stuck on says more.
        let mut side = None;
        match self.walk(goal)? {
            Some(atom) if atom.side => side = Some(atom),
            Some(atom) => return Ok(Some(atom)),
            None => {}
        }
        self.in_goal = false;
        for level in visible(cx) {
            if is_equation(cx, level) {
                continue;
            }
            let Value::Eq(_, l, r) = force(g, cx.types[level].clone())? else {
                continue;
            };
            let (l, r) = (force(g, (*l).clone())?, force(g, (*r).clone())?);
            let stuck_side = if is_ctor_form(&r) && is_stuck(&l) {
                l
            } else if is_ctor_form(&l) && is_stuck(&r) {
                r
            } else {
                continue;
            };
            if let Some(atom) = self.walk(&stuck_side)? {
                return Ok(Some(atom));
            }
        }
        Ok(side.or_else(|| self.single.take()))
    }

    fn walk(&mut self, value: &Value) -> Result<Option<Atom>> {
        let g = self.cx.g();
        self.visits += 1;
        if self.visits > VISITS {
            return Ok(None);
        }
        g.budget.step()?;
        let forced = force(g, value.clone())?;
        match &forced {
            Value::Neutral(Head::Def(_), spine) => {
                if is_folded(g, &forced) {
                    return match unfold_folded(g, &forced)? {
                        Some(unfolded) => self.walk(&unfolded),
                        None => Ok(None),
                    };
                }
                if let Some(atom) = self.chain(&forced, None)? {
                    return Ok(Some(atom));
                }
                self.walk_stuck_spine(spine)
            }
            Value::Neutral(Head::Var(..), spine) => self.walk_spine(spine),
            Value::Ctor(_, _, fields) => {
                for f in fields.iter() {
                    if let Some(atom) = self.walk(f)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::Data(_, args) => {
                for a in args {
                    if let Some(atom) = self.walk(a)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::Eq(ty, l, r) => {
                // A side that is itself stuck, of a splittable type, is the
                // outermost candidate: `f x = True` splits on `f x` if
                // nothing inside it is splittable.
                let d = match force(g, (**ty).clone())? {
                    Value::Data(d, _) => Some(d),
                    _ => None,
                };
                for side in [l, r] {
                    let forced = force(g, (**side).clone())?;
                    if let (Some(d), Value::Neutral(Head::Def(_), spine)) = (d, &forced)
                        && !is_folded(g, &forced)
                    {
                        if let Some(atom) = self.chain(&forced, Some(((**side).clone(), d)))? {
                            return Ok(Some(atom));
                        }
                        if let Some(atom) = self.walk_stuck_spine(spine)? {
                            return Ok(Some(atom));
                        }
                        continue;
                    }
                    if let Some(atom) = self.walk(side)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::NatAdd(_, x) => self.walk(x),
            _ => Ok(None),
        }
    }

    fn walk_stuck_spine(&mut self, spine: &stitchwort_core::value::Spine) -> Result<Option<Atom>> {
        self.under_stuck += 1;
        let found = self.walk_spine(spine);
        self.under_stuck -= 1;
        found
    }

    fn walk_spine(&mut self, spine: &stitchwort_core::value::Spine) -> Result<Option<Atom>> {
        for elim in spine.iter() {
            if let Elim::App(a, _) = elim
                && let Some(atom) = self.walk(a)?
            {
                return Ok(Some(atom));
            }
        }
        Ok(None)
    }

    /// The innermost splittable value on the chain of what the stuck call
    /// `stuck` waits for.
    fn chain(&mut self, stuck: &Value, first: Option<(Value, DataId)>) -> Result<Option<Atom>> {
        let g = self.cx.g();
        let mut best: Option<Atom> = None;
        let mut current = stuck.clone();
        let mut last_unsplittable = None;
        let mut first = first;
        loop {
            // `stuck` itself first, if it's a candidate; then what it waits
            // for, and so on inwards.
            let (raw, d, is_first) = match first.take() {
                Some((raw, d)) => (raw, d, true),
                None => match blocker(self.cx, &current)? {
                    Some((raw, d)) => (raw, d, false),
                    None => break,
                },
            };
            match self.ctors(d) {
                Some(n) if !self.is_known(&raw)? && !has_meta(self.cx, &raw)? => {
                    let atom = Atom {
                        value: raw.clone(),
                        d,
                        side: is_first,
                    };
                    if n >= 2 {
                        best = Some(atom);
                    } else if self.single.is_none()
                        && last_unsplittable.is_none()
                        && self.under_stuck == 0
                    {
                        // A record is split only for what waits on it
                        // directly (`p.row`), never under a number
                        // (`Nat.leq x.bits y.bits` waits on `x.bits`): taking
                        // `x` apart doesn't decide that.
                        self.single = Some(atom);
                    }
                }
                Some(_) => {}
                None => last_unsplittable = Some((raw.clone(), d)),
            }
            if is_first {
                continue;
            }
            let next = force(g, raw)?;
            current = if is_folded(g, &next) {
                match unfold_folded(g, &next)? {
                    Some(u) => u,
                    None => break,
                }
            } else {
                next
            };
            if !matches!(current, Value::Neutral(Head::Def(_), _)) {
                break;
            }
        }
        if best.is_none()
            && self.in_goal
            && self.stuck.is_none()
            && let Some((raw, d)) = last_unsplittable
        {
            let shown = self.cx.show(&raw);
            self.stuck = Some((shown, g.data(d).name.to_string()));
        }
        Ok(best)
    }

    fn is_known(&self, value: &Value) -> Result<bool> {
        if self.known.is_empty() {
            return Ok(false);
        }
        let t = quote(self.cx.g(), self.cx.level(), value)?;
        Ok(self.known.iter().any(|k| crate::matching::same(k, &t)))
    }

    /// The number of constructors of `d` if it's splittable.
    fn ctors(&self, d: DataId) -> Option<usize> {
        if let Some(known) = self.run.splittable.borrow().get(&d) {
            return *known;
        }
        let answer = splittable(self.cx, d);
        self.run.splittable.borrow_mut().insert(d, answer);
        answer
    }
}

fn has_meta(cx: &Ctx, value: &Value) -> Result<bool> {
    let t = cx.quote(value)?;
    Ok(t.subterms().any(|(t, _)| matches!(t, Term::Meta(_))))
}

fn is_ctor_form(value: &Value) -> bool {
    matches!(value, Value::Ctor(..) | Value::Nat(_))
}

fn is_stuck(value: &Value) -> bool {
    matches!(value, Value::Neutral(..) | Value::NatAdd(..))
}

/// The constructor count of `d` if a value of it can be split: data that
/// isn't a proposition, an indexed family or recursive.
fn splittable(cx: &Ctx, d: DataId) -> Option<usize> {
    let g = cx.g();
    let data = g.data(d);
    if data.sort == Sort::Prop || !data.indices.is_empty() || data.ctors.is_empty() {
        return None;
    }
    let recursive = data.ctors.iter().any(|c| {
        c.fields.iter().any(|(_, ty)| {
            ty.subterms()
                .any(|(t, _)| matches!(t, Term::Data(x, _) if data.group.contains(x)))
        })
    });
    (!recursive).then_some(data.ctors.len())
}

/// What the stuck call `value` (forced) waits for: the value its case tree
/// tests where it can't take a step, as the call's arguments hold it (a
/// folded call is kept as the call, for display), with its type.
fn blocker(cx: &Ctx, value: &Value) -> Result<Option<(Value, DataId)>> {
    let g = cx.g();
    let Value::Neutral(Head::Def(id), spine) = value else {
        return Ok(None);
    };
    let def = g.def(*id);
    let Some(body) = body_seen(g, *id) else {
        return Ok(None);
    };
    if def.arity == 0 || spine.len() < def.arity {
        return Ok(None);
    }
    let mut env = Vec::with_capacity(def.arity);
    for elim in spine.iter().take(def.arity) {
        match elim {
            Elim::App(v, _) => env.push(v.clone()),
            Elim::J { .. } => return Ok(None),
        }
    }
    let mut tree = Term::peel_lams_rc(body, def.arity);
    loop {
        g.budget.step()?;
        let node = Term::strip_loc_rc(&tree);
        match &*node {
            Term::Case(ix, d, branches) => {
                let raw = env[env.len() - 1 - ix].clone();
                let mut scrutinee = force(g, raw.clone())?;
                if is_folded(g, &scrutinee)
                    && let Some(u) = unfold_folded(g, &scrutinee)?
                {
                    scrutinee = u;
                }
                match scrutinee {
                    Value::Ctor(_, c, fields) => {
                        let Some(next) = branches[c].body.clone() else {
                            return Ok(None);
                        };
                        env.extend(fields.iter().cloned());
                        tree = next;
                    }
                    Value::Neutral(..) => return Ok(Some((raw, *d))),
                    _ => return Ok(None),
                }
            }
            Term::NumCase(ix, ..) => {
                let raw = env[env.len() - 1 - ix].clone();
                let nat = g.builtins.nat;
                return Ok(match (force(g, raw.clone())?, nat) {
                    (Value::Neutral(..), Some(nat)) => Some((raw, nat)),
                    _ => None,
                });
            }
            _ => return Ok(None),
        }
    }
}

/// Splits the case on `atom`: the generated `match` with one alternative
/// per constructor, each going on with this `cases`.
fn split_on(cx: &mut Ctx, run: &Rc<Run>, atom: Atom, goal: &Value) -> Result<Term> {
    let g = cx.g();
    let data = g.data(atom.d);
    let shown = cx.show(&atom.value);
    {
        let mut atoms = run.atoms.borrow_mut();
        if !atoms.contains(&shown) {
            atoms.push(shown.clone());
        }
    }
    run.cases.set(run.cases.get() + data.ctors.len() - 1);
    if run.cases.get() > CASES {
        run.over.set(true);
        let path = path(cx);
        *run.open_at.borrow_mut() = Some(if path.is_empty() {
            "the first, before any split".to_string()
        } else {
            path.join(", ")
        });
        return Err(Diagnostic::error("E-CASES-BUDGET", "over budget"));
    }
    let term = cx.quote_folded(&atom.value)?;
    let ty = atom_type(cx, &term, atom.d)?;
    let depth = (0..cx.level()).filter(|&l| is_equation(cx, l)).count();
    let name = ast::Name {
        text: format!("{EQUATION}{}", depth + 1),
        span: run.span,
    };
    let alts: Vec<Alt> = data
        .ctors
        .iter()
        .enumerate()
        .map(|(c, ctor)| {
            let explicit = (0..ctor.fields.len())
                .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                .count();
            let fields = (0..explicit).map(|_| Pattern::Wildcard(run.span)).collect();
            Alt {
                patterns: vec![crate::internal_ctor_pattern(atom.d, c, fields, run.span)],
                body: Expr::Cases {
                    body: run.body.clone(),
                    span: run.span,
                },
                span: run.span,
            }
        })
        .collect();
    crate::matching::generalised_named(
        cx,
        term,
        ty,
        run.span,
        Some(name),
        Some(stale),
        &alts,
        &[],
        run.span,
        goal,
    )
}

/// The type of the atom `term`, of data `d`: `d` itself if it has no
/// parameters, and otherwise as the kernel infers it.
fn atom_type(cx: &Ctx, term: &Term, d: DataId) -> Result<Value> {
    let g = cx.g();
    if g.data(d).params.is_empty() {
        return Ok(Value::Data(d, Vec::new()));
    }
    let mut kcx = crate::rewrite::kernel_context(cx)?;
    let (_, ty) = crate::kernel::without_glue(g, || crate::kernel::infer(&mut kcx, term))?;
    Ok(ty)
}
