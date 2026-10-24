//! `rewrite` (docs/syntax.md, "rewrite"; docs/proposals/calc-rewrite.md §6).
//!
//! ```text
//! rewrite p in t        -- t proves the goal with p's left side replaced
//! rewrite p             -- the same as `rewrite p in rfl`
//! rewrite p, <- q in t  -- p, then q right to left, then t
//! rewrite p at h in t   -- in t, h has its type with p's left side replaced
//! rewrite p at h        -- the rewritten h itself
//! ```
//!
//! Given `p: a = b` and the goal `G`, the occurrences of `a` in `G` are
//! found (below), abstracted into a motive `M x := G[x]`, and the result is
//! `J M t (Eq.sym p)`, with `t` checked against `G[b]`. Elaboration only: the
//! kernel re-checks the `J`.
//!
//! **The search** walks the goal term in pre-order (a term before its parts,
//! an application's arguments left to right) and never looks inside a
//! selected occurrence, so matches don't overlap. Each candidate goes through
//! these tests in order, and the first failure moves on:
//!
//! 1. *key*: the same head (definition, constructor, variable, …) and number
//!    of arguments as `a`;
//! 2. it mentions no variable bound inside the goal (`J` can't rewrite under
//!    a binder without function extensionality, so those are skipped);
//! 3. *syntax*: it is the same term as `a`, which is a match;
//! 4. *carrier type*: its type unifies with the equation's type;
//! 5. *conversion*: it unifies with `a`.
//!
//! Tests 4 and 5 are one transaction ([`crate::undo`]): only the rule's own
//! metavariables (those made while elaborating `p`) may be solved, and
//! whatever failed is undone, so a candidate that fails leaves nothing
//! behind. They draw on one evaluation budget for the whole `rewrite`; the
//! budget isn't refunded when a candidate fails. Running out is never read
//! as "no match": it's `E-REWRITE-BUDGET`.
//!
//! After abstracting, the motive must be a well-formed proposition
//! (`E-REWRITE-MOTIVE`: an `auto` proof about the replaced term is the usual
//! cause) and applied to `a` it must compute back to the goal ([`round_trip`]).
//!
//! **`at h`** (docs/proposals/rewrite-hypothesis.md) runs the same search
//! and checks over the type `H` of `h` instead of the goal. The motive is
//! `M x := H[x]` with its proof binder over `a = x`, and the result is
//! `J M h p : H[b]`, the `J`s nesting the other way from the goal's. With
//! `in t`, `h` is a `let` of that term for `t`.
//!
//! Set `STITCHWORT_REWRITE_METRICS` to print, per `rewrite`, how much the
//! search did (candidates visited, conversions, evaluation steps).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, apply, eval, force};
use stitchwort_core::{DataId, DefId, Icit, Term, Value};
use stitchwort_syntax::ast::{Expr, Name as AstName, RewriteRule};
use stitchwort_syntax::{Diagnostic, Span};

use crate::calc::lemma;
use crate::check::{Ctx, Piped, Result, check, infer, insert};
use crate::lift::replace_with;
use crate::matching::same;
use crate::undo::{Snapshot, fatal};

/// Evaluation steps all the comparisons of one `rewrite` may use between
/// them (docs/proposals/calc-rewrite.md §6.2). Cheap comparisons use a few
/// hundred; this is what an expensive candidate runs out of.
const SEARCH_BUDGET: u64 = 1_000_000;

/// Where the rules of a `rewrite` look: the goal, or the type of the term
/// after `at`.
#[derive(Clone, Copy)]
enum Place<'a> {
    Goal,
    /// The target's name, if it is one.
    Target(Option<&'a str>),
}

impl Place<'_> {
    /// For messages: "the goal", "the type of `h`".
    fn the(self) -> String {
        match self {
            Place::Goal => "the goal".into(),
            Place::Target(Some(name)) => format!("the type of `{name}`"),
            Place::Target(None) => "the type of the term after `at`".into(),
        }
    }
}

/// `rewrite` where nothing says what to prove.
pub(crate) fn infer_rewrite(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let Expr::Rewrite { rules, target, .. } = expr else {
        unreachable!("only called on a rewrite");
    };
    if target.is_some() {
        return rewrite_at(cx, expr, None);
    }
    Err(Diagnostic::error(
        "E-REWRITE-NO-GOAL",
        "`rewrite` needs to know what it has to prove",
    )
    .with_label(
        rules[0].span,
        "there is no expected type here to look for this rule's left side in",
    )
    .with_note("write the type with an ascription: `(rewrite p in t: a = b)`")
    .with_note(
        "the goal is known where a proof is checked against a type: an argument, a definition's \
         body, a `calc` step",
    )
    .with_note("to rewrite the type of a fact `t` instead of a goal, write `rewrite p at t`"))
}

/// `rewrite p at h in t` and `rewrite p at h`: the rules rewrite the type
/// of `h`, and `t` (if any) is checked with `h` rebound to the result.
fn rewrite_at(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    let Expr::Rewrite {
        rules,
        target: Some(target),
        body,
        span,
    } = expr
    else {
        unreachable!("only called on a rewrite with a target");
    };
    let name = match &**target {
        Expr::Var(n) if cx.lookup(&n.text).is_some() || cx.local(&n.text)?.is_some() => Some(n),
        _ => None,
    };
    if body.is_some() && name.is_none() {
        return Err(Diagnostic::error(
            "E-REWRITE-TARGET",
            "`rewrite … at … in` needs a local name after `at`",
        )
        .with_label(
            target.span(),
            "this isn't a local name, so there is nothing to give the new type for the rest of the proof",
        )
        .with_note(
            "only a name can be given a new type for the rest of the proof; drop `in …` to use \
             the rewritten term directly, or name it first with `let`",
        ));
    }
    let place = Place::Target(name.map(|n| n.text.as_str()));
    let (fact, ty) = infer(cx, target)?;
    let (fact, ty) = insert(cx, fact, ty)?;
    let budget = cx.e.rewrite_budget.unwrap_or(SEARCH_BUDGET);
    let mut remaining = budget;
    let mut stats = Stats::default();
    let mut ty = match cx.e.interfaces.is_empty() {
        true => ty,
        false => crate::interfaces::find_ready_dictionaries(cx, &ty, None)?.unwrap_or(ty),
    };
    let mut term = fact;
    let mut outcome = Ok(());
    for (index, rule) in rules.iter().enumerate() {
        match rewrite_once(
            cx,
            rule,
            index,
            place,
            &ty,
            None,
            &mut remaining,
            &mut stats,
        ) {
            Ok(step) => {
                ty = step.goal;
                term = Term::J(Rc::new(step.motive), Rc::new(term), Rc::new(step.proof));
            }
            Err(e) => {
                outcome = Err(e);
                break;
            }
        }
    }
    report(*span, rules.len(), &stats, budget - remaining);
    outcome?;
    let Some(body) = body else {
        let Some(expected) = expected else {
            return Ok((term, ty));
        };
        return match crate::check::compare(cx, term, &ty, expected) {
            Err(e) if e.code == "E-TYPE-MISMATCH" => Err(e.with_note(format!(
                "after `rewrite … at`, {} is `{}`",
                match name {
                    Some(n) => format!("`{}`", n.text),
                    None => "the term".into(),
                },
                cx.show(&ty)
            ))),
            result => Ok((result?, expected.clone())),
        };
    };
    let name = name.expect("checked above");
    let ty_term = cx.quote(&ty)?;
    let mark = cx.mark();
    let x: stitchwort_core::Name = name.text.as_str().into();
    let result = cx
        .define(
            Some(&name.text),
            x.clone(),
            ty,
            ty_term.clone(),
            term.clone(),
        )
        .and_then(|()| match expected {
            Some(t) => check(cx, body, t).map(|b| (b, t.clone())),
            None => infer(cx, body),
        });
    cx.reset(mark);
    let (body, block_ty) = result?;
    Ok((Term::let_(x, ty_term, term, body), block_ty))
}

/// `rewrite` against a goal.
pub(crate) fn check_rewrite(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Rewrite {
        rules,
        target,
        body,
        span,
    } = expr
    else {
        unreachable!("only called on a rewrite");
    };
    if target.is_some() {
        return Ok(rewrite_at(cx, expr, Some(expected))?.0);
    }
    let budget = cx.e.rewrite_budget.unwrap_or(SEARCH_BUDGET);
    let mut remaining = budget;
    let mut stats = Stats::default();
    let mut written = cx.written_goal.take();
    // A dictionary the goal mentions whose type is known is found first, so
    // what it adds or compares computes (`xs.sumBy f`'s `+`).
    let mut goal = match cx.e.interfaces.is_empty() {
        true => expected.clone(),
        false => crate::interfaces::find_ready_dictionaries(cx, expected, None)?
            .unwrap_or_else(|| expected.clone()),
    };
    let mut steps: Vec<Step> = Vec::new();
    let mut outcome = Ok(());
    for (index, rule) in rules.iter().enumerate() {
        match rewrite_once(
            cx,
            rule,
            index,
            Place::Goal,
            &goal,
            written.take(),
            &mut remaining,
            &mut stats,
        ) {
            Ok(step) => {
                goal = step.goal.clone();
                steps.push(step);
            }
            Err(e) => {
                outcome = Err(e);
                break;
            }
        }
    }
    report(*span, rules.len(), &stats, budget - remaining);
    outcome?;
    let base = match body {
        Some(body) => check(cx, body, &goal)?,
        None => {
            let rfl = Expr::Var(AstName {
                text: "rfl".into(),
                span: rules.last().expect("a rule").span,
            });
            match check(cx, &rfl, &goal) {
                Err(e) if e.code == "E-REFL" => {
                    return Err(e.with_note(format!(
                        "this is the goal after rewriting; `rewrite p` without `in` closes it with `rfl`: `{}`",
                        cx.show(&goal)
                    )));
                }
                result => result?,
            }
        }
    };
    let mut term = base;
    for step in steps.into_iter().rev() {
        term = Term::J(Rc::new(step.motive), Rc::new(term), Rc::new(step.proof));
    }
    Ok(term)
}

/// One rule's rewrite of the goal (or of a target's type).
struct Step {
    /// `x _ => G[x]`.
    motive: Term,
    /// For the goal, proves `rhs = lhs`, which `J` takes the base `G[rhs]`
    /// along. For a target, proves `lhs = rhs`, which `J` takes the target
    /// `G[lhs]` along.
    proof: Term,
    /// `G[rhs]`: what the rest of the `rewrite` proves (or the target's new
    /// type).
    goal: Value,
}

/// What the searches did, for [`report`].
#[derive(Default)]
struct Stats {
    /// Subterms the search looked at.
    visited: u64,
    /// ...with the right head and number of arguments.
    keyed: u64,
    /// ...that mention a variable bound inside the goal.
    bound: u64,
    /// Matches found by syntax alone.
    syntactic: u64,
    /// Comparisons by type and conversion.
    conversions: u64,
    /// Occurrences replaced.
    matched: u64,
}

fn report(span: Span, rules: usize, stats: &Stats, steps: u64) {
    if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_none() {
        return;
    }
    // There is no conversion cache to hit: every comparison computes afresh.
    eprintln!(
        "rewrite-metrics: at={}..{} rules={rules} visited={} keyed={} bound={} syntactic={} \
         conversions={} matched={} steps={steps} cache_hits=0",
        span.start,
        span.end,
        stats.visited,
        stats.keyed,
        stats.bound,
        stats.syntactic,
        stats.conversions,
        stats.matched
    );
}

#[allow(clippy::too_many_arguments)]
fn rewrite_once(
    cx: &mut Ctx,
    rule: &RewriteRule,
    // How many rules of the same `rewrite` came before this one.
    index: usize,
    place: Place,
    goal: &Value,
    written: Option<Term>,
    remaining: &mut u64,
    stats: &mut Stats,
) -> Result<Step> {
    let g = cx.g();
    let rule_metas = g.metas.borrow().len();
    let (proof, ty) = infer(cx, &rule.proof)?;
    let (proof, ty) = insert(cx, proof, ty)?;
    let Value::Eq(carrier, left, right) = force(g, ty.clone())? else {
        return Err(
            Diagnostic::error("E-REWRITE-RULE", "`rewrite` needs a proof of an equation")
                .with_label(
                    rule.proof.span(),
                    format!("this has type `{}`, which isn't an equation", cx.show(&ty)),
                )
                .with_note("give a function its arguments: `rewrite Nat.addComm a b`"),
        );
    };
    let carrier = (*carrier).clone();
    let (lhs, rhs) = if rule.reverse {
        ((*right).clone(), (*left).clone())
    } else {
        ((*left).clone(), (*right).clone())
    };
    // For the goal, `J` carries the base `G[rhs]` along a proof of
    // `rhs = lhs`; for a target, the target `G[lhs]` along `lhs = rhs`.
    let to_lhs = if rule.reverse == matches!(place, Place::Goal) {
        proof
    } else {
        let piped = Piped {
            term: proof,
            ty: ty.clone(),
            span: rule.proof.span(),
        };
        lemma(cx, Builtin::EqSym, &[piped])?
    };

    let lhs_term = cx.quote(&lhs)?;
    let Some(key) = key(&lhs_term, 0) else {
        return Err(unknown_head(rule, place));
    };
    let goal_value = force(g, goal.clone())?;
    let mut goal_term = cx.quote(&goal_value)?;
    // An `auto` proof still to be found inside the goal could depend on what
    // is replaced, which only shows once it is found.
    let pending: Vec<usize> = goal_term
        .subterms()
        .filter_map(|(t, _)| {
            if let Term::Meta(m) = t {
                Some(*m)
            } else {
                None
            }
        })
        .collect();
    if !pending.is_empty() && cx.e.prove_now(&|m| pending.contains(&m))? {
        goal_term = cx.quote(&goal_value)?;
    }
    let level = cx.level();

    let kcx = kernel_context(cx)?;
    let search = Search {
        kcx: RefCell::new(kcx),
        cx: RefCell::new(cx),
        rule,
        place,
        carrier: &carrier,
        lhs: &lhs,
        lhs_term: RefCell::new(lhs_term),
        key,
        rule_metas,
        remaining: Cell::new(*remaining),
        stats: RefCell::new(Stats::default()),
        error: RefCell::new(None),
        first: RefCell::new(None),
    };
    // The goal with the occurrences replaced by `x`, under `x _ =>`.
    let body = replace_with(
        g,
        &goal_term,
        level,
        &|l| Ok(Term::Var(level + 2 - 1 - l)),
        &|t, under| search.visit(t, under),
    );
    *remaining = search.remaining.get();
    let found = search.stats.take();
    stats.visited += found.visited;
    stats.keyed += found.keyed;
    stats.bound += found.bound;
    stats.syntactic += found.syntactic;
    stats.conversions += found.conversions;
    stats.matched += found.matched;
    if let Some(e) = search.error.take() {
        return Err(e);
    }
    let first = search.first.take();
    drop(search);
    let body = body?;
    if found.matched == 0 {
        let as_written = match place {
            Place::Goal => goal_as_written(cx, written, &goal_value)?,
            Place::Target(_) => None,
        };
        let done = match place {
            Place::Goal => holds_by_computing(cx, &goal_value, remaining)?,
            Place::Target(_) => false,
        };
        return Err(nothing_found(
            cx,
            rule,
            Searched {
                index,
                place,
                as_written,
                done,
            },
            &lhs,
            &goal_value,
            &found,
        ));
    }

    let motive = Term::Lam(
        "x'".into(),
        Icit::Explicit,
        Rc::new(Term::Lam("_".into(), Icit::Explicit, Rc::new(body))),
    );
    // The motive's proof binder is over `from = x`, where `J` starts.
    let (from, proof_value) = match place {
        Place::Goal => (&rhs, cx.eval(&to_lhs)?),
        Place::Target(_) => (&lhs, Value::Refl),
    };
    check_motive(cx, rule, place, &motive, &carrier, from, &lhs)?;
    match round_trip(cx, &motive, &lhs, &proof_value, &goal_value, remaining)? {
        Some(true) => {}
        Some(false) => {
            return Err(round_trip_error(cx, rule, place, &lhs, first.as_ref()));
        }
        None => {
            return Err(budget_error(
                cx,
                rule,
                place,
                first.as_ref().unwrap_or(&goal_term),
                &lhs,
            ));
        }
    }
    let motive_value = cx.eval(&motive)?;
    let next = apply(g, apply(g, motive_value, rhs)?, Value::Refl)?;
    Ok(Step {
        motive,
        proof: to_lhs,
        goal: next,
    })
}

/// The occurrence search over one goal term.
struct Search<'a, 'e> {
    cx: RefCell<&'a mut Ctx<'e>>,
    /// The kernel's view of the same context, for the types of candidates.
    kcx: RefCell<kernel::Ctx<'e>>,
    rule: &'a RewriteRule,
    place: Place<'a>,
    carrier: &'a Value,
    lhs: &'a Value,
    /// The left side as a term. Read back again after each match, so the
    /// metavariables it solved show, and later copies match by syntax.
    lhs_term: RefCell<Term>,
    key: Key,
    /// Metavariables from this index on were made for the rule.
    rule_metas: usize,
    remaining: Cell<u64>,
    stats: RefCell<Stats>,
    /// Why the search stopped, if it did.
    error: RefCell<Option<Diagnostic>>,
    /// The first occurrence selected, in the goal's own context.
    first: RefCell<Option<Term>>,
}

impl Search<'_, '_> {
    /// The hook of [`replace_with`]: replaces `t`, a subterm under `under`
    /// binders of the goal, by the motive's variable if it's an occurrence.
    fn visit(&self, t: &Term, under: usize) -> Option<Term> {
        if self.error.borrow().is_some() {
            return Some(t.clone());
        }
        // A location wraps the term that is the candidate.
        if matches!(t, Term::Loc(..)) {
            return None;
        }
        self.stats.borrow_mut().visited += 1;
        if key(t, under).as_ref() != Some(&self.key) {
            return None;
        }
        self.stats.borrow_mut().keyed += 1;
        if mentions_bound(t, under) {
            self.stats.borrow_mut().bound += 1;
            return None;
        }
        match self.decide(t, under) {
            Ok(Some(candidate)) => {
                self.stats.borrow_mut().matched += 1;
                let mut first = self.first.borrow_mut();
                if first.is_none() {
                    *first = Some(candidate);
                }
                // Under the motive's `x` and `_`, and the goal's own binders.
                Some(Term::Var(under + 1))
            }
            Ok(None) => None,
            Err(e) => {
                *self.error.borrow_mut() = Some(e);
                Some(t.clone())
            }
        }
    }

    /// Whether `t` is an occurrence of the left side, solving the rule's
    /// metavariables if it is and nothing if it isn't. An occurrence comes
    /// back as a term in the goal's own context.
    fn decide(&self, t: &Term, under: usize) -> Result<Option<Term>> {
        let mut cx = self.cx.borrow_mut();
        let cx: &mut Ctx = &mut cx;
        let g = cx.g();
        let level = cx.level();
        // The candidate in the goal's own context, where it mentions no
        // variable bound inside the goal.
        let candidate = if under == 0 {
            t.clone()
        } else {
            replace_with(
                g,
                t,
                level + under,
                &|l| Ok(Term::Var(level - 1 - l)),
                &|_, _| None,
            )?
        };
        if same(&candidate, &self.lhs_term.borrow()) {
            self.stats.borrow_mut().syntactic += 1;
            return Ok(Some(candidate));
        }
        self.stats.borrow_mut().conversions += 1;
        let snapshot = Snapshot::take(cx);
        let mut remaining = self.remaining.get();
        let outcome = g.budget.limited(&mut remaining, || -> Result<bool> {
            let value = eval(g, &cx.env, &candidate)?;
            if !has_carrier(cx, &mut self.kcx.borrow_mut(), &candidate, self.carrier)? {
                return Ok(false);
            }
            cx.unify(&value, self.lhs)
        });
        self.remaining.set(remaining);
        match outcome {
            Ok(Some(true)) => {
                // One way: nothing but the rule's own metavariables.
                let foreign = snapshot
                    .solved_since(cx)
                    .into_iter()
                    .any(|m| m < self.rule_metas);
                if foreign {
                    snapshot.restore(cx);
                    return Ok(None);
                }
                let solved = cx.quote(self.lhs)?;
                *self.lhs_term.borrow_mut() = solved;
                Ok(Some(candidate))
            }
            Ok(Some(false)) => {
                snapshot.restore(cx);
                Ok(None)
            }
            Ok(None) => {
                snapshot.restore(cx);
                Err(budget_error(
                    cx, self.rule, self.place, &candidate, self.lhs,
                ))
            }
            Err(e) => {
                if !fatal(&e) {
                    snapshot.restore(cx);
                }
                Err(e)
            }
        }
    }
}

/// The kernel's context for `cx`'s variables. The kernel never sees a
/// metavariable (it compares a solved one's head as it is), so what the
/// variables' types and values mention is read back with them replaced.
fn kernel_context<'e>(cx: &Ctx<'e>) -> Result<kernel::Ctx<'e>> {
    let zonked = |v: &Value| cx.eval(&cx.quote(v)?);
    let plain = |v: &Value| matches!(v, Value::Neutral(Head::Var(_), s) if s.is_empty());
    let env = cx
        .env
        .iter()
        .map(|v| if plain(v) { Ok(v.clone()) } else { zonked(v) })
        .collect::<Result<Vec<_>>>()?;
    let types = cx.types.iter().map(zonked).collect::<Result<Vec<_>>>()?;
    Ok(kernel::Ctx::with_variables(
        cx.g(),
        &env,
        &types,
        &cx.names,
        cx.span,
    ))
}

/// Whether `term`, a term in `cx`'s context, has type `carrier` (solving the
/// rule's metavariables in `carrier` if its type can be found).
///
/// The kernel infers the type of most terms, but a constructor or a
/// function is only checked against a type. Those are checked against the
/// carrier, if it has no unsolved metavariable to solve. If it has, or the
/// term has one the goal hasn't solved yet, nothing can be said and the
/// comparison by conversion is left to decide.
fn has_carrier(cx: &Ctx, kcx: &mut kernel::Ctx, term: &Term, carrier: &Value) -> Result<bool> {
    match kernel::without_glue(cx.g(), || kernel::infer(kcx, term)) {
        Ok((_, ty)) => return cx.unify(&ty, carrier),
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {}
    }
    let unsolved = |t: &Term| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_)));
    let carrier_term = cx.quote(carrier)?;
    if unsolved(term) || unsolved(&carrier_term) {
        return Ok(true);
    }
    let carrier = cx.eval(&carrier_term)?;
    match kernel::without_glue(cx.g(), || kernel::check(kcx, term, &carrier)) {
        Ok(_) => Ok(true),
        Err(e) if fatal(&e) => Err(e),
        Err(_) => Ok(false),
    }
}

/// The part of a term that decides which candidates are worth comparing.
#[derive(Clone, PartialEq)]
enum Key {
    Def(DefId, usize),
    Ctor(DataId, usize, usize),
    Data(DataId, usize),
    /// A variable, by its index in the goal's own context, and its number of
    /// arguments.
    Var(usize, usize),
    Nat(Rc<num_bigint::BigUint>),
    /// Anything else, by what kind of term it is.
    Other(&'static str),
}

/// The key of `term`, a subterm under `under` binders; `None` if it can't be
/// an occurrence: a metavariable, or a bound variable, at its head.
fn key(term: &Term, under: usize) -> Option<Key> {
    let mut args = 0;
    let mut head = term.strip_loc();
    while let Term::App(f, _, _) = head {
        args += 1;
        head = f.strip_loc();
    }
    Some(match head {
        Term::Def(id) => Key::Def(*id, args),
        Term::Var(ix) if *ix >= under => Key::Var(ix - under, args),
        Term::Var(_) | Term::Meta(_) => return None,
        Term::Ctor(d, c, fields) if args == 0 => Key::Ctor(*d, *c, fields.len()),
        Term::Data(d, params) if args == 0 => Key::Data(*d, params.len()),
        Term::Nat(n) if args == 0 => Key::Nat(n.clone()),
        Term::Ctor(..) | Term::Data(..) | Term::Nat(_) => Key::Other("applied"),
        Term::Chars(_) => Key::Other("text"),
        Term::Sort(_) => Key::Other("sort"),
        Term::Pi(..) => Key::Other("function type"),
        Term::Lam(..) => Key::Other("function"),
        Term::Eq(..) => Key::Other("equation"),
        Term::Refl => Key::Other("rfl"),
        Term::J(..) => Key::Other("J"),
        Term::Quot(form, ..) => Key::Other(form.name()),
        Term::Ann(..) => Key::Other("annotation"),
        Term::Let(..) => Key::Other("let"),
        Term::Case(..) | Term::NumCase(..) => Key::Other("case"),
        Term::App(..) | Term::Loc(..) => unreachable!("stripped above"),
    })
}

/// Whether `term`, under `under` binders of the goal, mentions one of them.
fn mentions_bound(term: &Term, under: usize) -> bool {
    under > 0
        && term.subterms().any(|(t, binders)| match t {
            Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
                *ix >= binders && *ix - binders < under
            }
            _ => false,
        })
}

/// Checks that `x _ => body` is a motive: the body is a type with `x` of
/// the equation's type and `_ : rhs = x` in scope (`rhs` is the side `J`
/// starts from). The kernel would reject a `J` whose motive isn't, but here
/// the message can say why.
fn check_motive(
    cx: &Ctx,
    rule: &RewriteRule,
    place: Place,
    motive: &Term,
    carrier: &Value,
    rhs: &Value,
    lhs: &Value,
) -> Result<()> {
    let Term::Lam(_, _, inner) = motive else {
        unreachable!("a motive is a function");
    };
    let Term::Lam(_, _, body) = &**inner else {
        unreachable!("a motive takes two arguments");
    };
    // Unsolved metavariables can't be kernel-checked; the `J` is checked
    // whole once they are solved.
    if body.subterms().any(|(t, _)| matches!(t, Term::Meta(_))) {
        return Ok(());
    }
    let zonked = |v: &Value| cx.eval(&cx.quote(v)?);
    let (carrier, rhs) = (zonked(carrier)?, zonked(rhs)?);
    let mut kcx = kernel_context(cx)?;
    let x = Value::var(kcx.level());
    kcx.bind("x'".into(), carrier.clone());
    kcx.bind(
        "_".into(),
        Value::Eq(Rc::new(carrier), Rc::new(rhs), Rc::new(x)),
    );
    match kernel::without_glue(cx.g(), || kernel::check_type(&mut kcx, body)) {
        Ok(_) => Ok(()),
        Err(e) if fatal(&e) => Err(e),
        Err(e) => Err(Diagnostic::error(
            "E-REWRITE-MOTIVE",
            format!(
                "replacing `{}` everywhere in {} doesn't give a valid proposition",
                shown(cx, lhs),
                place.the()
            ),
        )
        .with_label(
            rule.span,
            format!(
                "{} with this replaced by a variable doesn't type-check",
                place.the()
            ),
        )
        .with_note(format!(
            "the checker says: {}",
            e.labels.first().map_or(e.message.clone(), |l| format!(
                "{} ({})",
                e.message, l.message
            ))
        ))
        .with_note(format!(
            "something in {} can depend on the term being replaced, such as the proof an \
                 `auto` argument carries (the `d != 0` in `x % d`)",
            place.the()
        ))
        .with_note(
            "rewrite a larger term that contains it (such as `x % d`), or state the step with \
             `calc`",
        )),
    }
}

/// Whether the motive applied to the left side and the proof computes back to
/// the goal. The result of the `J` is what the motive gives there, so this is
/// what makes it prove the goal. `None`: out of search budget.
///
/// It follows from a match when comparison is congruent. It need not once
/// comparison ignores some parts (calc-rewrite.md §6.2, the round-trip check).
fn round_trip(
    cx: &Ctx,
    motive: &Term,
    lhs: &Value,
    proof: &Value,
    goal: &Value,
    remaining: &mut u64,
) -> Result<Option<bool>> {
    let g = cx.g();
    g.budget.limited(remaining, || -> Result<bool> {
        let motive = cx.eval(motive)?;
        let back = apply(g, apply(g, motive, lhs.clone())?, proof.clone())?;
        cx.unify(&back, goal)
    })
}

/// A term for a message. An unknown the rule left open is shown as `?3`,
/// not applied to every variable in scope as it is made.
fn written(cx: &Ctx, term: &Term) -> String {
    stitchwort_core::pretty::term_for_message(cx.g(), &cx.names, &tidy(cx, term))
}

/// Whether [`written`] shortens `term` (to `…` inside).
fn shortened(cx: &Ctx, term: &Term) -> bool {
    let tidy = tidy(cx, term);
    let short = stitchwort_core::pretty::term_for_message(cx.g(), &cx.names, &tidy);
    short != stitchwort_core::pretty::term(cx.g(), &cx.names, &tidy)
}

/// `term` with each unknown the rule left open bare, as [`written`] shows it.
fn tidy(cx: &Ctx, term: &Term) -> Term {
    let level = cx.level();
    let bare = |t: &Term, _: usize| {
        let (head, args) = t.spine();
        match head {
            Term::Meta(m)
                if !args.is_empty()
                    && args.iter().all(|a| matches!(a.strip_loc(), Term::Var(_))) =>
            {
                Some(Term::Meta(*m))
            }
            _ => None,
        }
    };
    replace_with(
        cx.g(),
        term,
        level,
        &|l| Ok(Term::Var(level - 1 - l)),
        &bare,
    )
    .unwrap_or_else(|_| term.clone())
}

/// A value for a message, as [`written`], with calls as calls (`n / 1`),
/// as other messages show them (docs/proposals/folded-calls.md, stage 3).
fn shown(cx: &Ctx, value: &Value) -> String {
    match folded(cx, value) {
        Some(term) => written(cx, &term),
        None => "…".into(),
    }
}

/// `value` read back with calls as calls, if it can be.
fn folded(cx: &Ctx, value: &Value) -> Option<Term> {
    cx.quote_folded(value).ok()
}

/// A value for a message, as [`written`], as it computes: what the search
/// compares (D484).
fn shown_computed(cx: &Ctx, value: &Value) -> String {
    match cx.quote(value) {
        Ok(term) => written(cx, &term),
        Err(_) => "…".into(),
    }
}

/// Whether the goal, an equation, already holds by computing (`rfl`):
/// within what is left of the search budget, and solving nothing.
fn holds_by_computing(cx: &mut Ctx, goal: &Value, remaining: &mut u64) -> Result<bool> {
    let g = cx.g();
    let Value::Eq(_, left, right) = force(g, goal.clone())? else {
        return Ok(false);
    };
    let snapshot = Snapshot::take(cx);
    match g.budget.limited(remaining, || cx.unify(&left, &right)) {
        Err(e) if fatal(&e) => Err(e),
        outcome => {
            let solved_nothing = snapshot.solved_since(cx).is_empty();
            snapshot.restore(cx);
            Ok(matches!(outcome, Ok(Some(true))) && solved_nothing)
        }
    }
}

fn unknown_head(rule: &RewriteRule, place: Place) -> Diagnostic {
    let side = if rule.reverse { "right" } else { "left" };
    Diagnostic::error(
        "E-REWRITE-RULE",
        format!("this equation's {side} side starts with an unknown function"),
    )
    .with_label(
        rule.proof.span(),
        format!(
            "there is no function or constructor of its {side} side to look for in {}",
            place.the()
        ),
    )
    .with_note("give the implicit arguments explicitly, such as `[f := …]`")
}

/// The goal as it was written (a `calc` step's line, or the type of the
/// definition being checked), if that is what `goal` computes from: for
/// messages, since `rewrite` searches the goal as it computes.
fn goal_as_written(cx: &mut Ctx, written: Option<Term>, goal: &Value) -> Result<Option<Term>> {
    let own = cx
        .goal
        .as_ref()
        .and_then(|(level, term)| (*level == cx.level()).then(|| Term::clone(term)));
    for term in written.into_iter().chain(own) {
        let Ok(value) = cx.eval(&term) else { continue };
        if crate::undo::unify(cx, &value, goal)? {
            return Ok(Some(term));
        }
    }
    Ok(None)
}

/// What a search that found nothing looked through, for [`nothing_found`].
struct Searched<'a> {
    /// How many rules of the same `rewrite` came before.
    index: usize,
    place: Place<'a>,
    /// The goal as it was written, if that is what it computes from.
    as_written: Option<Term>,
    /// The goal already holds by computing.
    done: bool,
}

fn nothing_found(
    cx: &Ctx,
    rule: &RewriteRule,
    searched: Searched,
    lhs: &Value,
    goal: &Value,
    found: &Stats,
) -> Diagnostic {
    let Searched {
        index,
        place,
        as_written,
        done,
    } = searched;
    let shown_lhs = shown(cx, lhs);
    let computed_lhs = shown_computed(cx, lhs);
    let goal_text = cx.show(goal);
    let mut error = Diagnostic::error(
        "E-REWRITE-NOTHING",
        format!("`rewrite` found no `{shown_lhs}` in {}", place.the()),
    )
    .with_label(rule.span, format!("looking for `{shown_lhs}`"));
    let what = match place {
        Place::Goal => "goal".to_string(),
        Place::Target(Some(name)) => format!("`{name}`"),
        Place::Target(None) => "its type".to_string(),
    };
    let after = match index {
        0 => String::new(),
        1 => " after the rule before this one".to_string(),
        _ => format!(" after the {index} rules before this one"),
    };
    match as_written.map(|t| written(cx, &t)) {
        Some(text) if text != goal_text => {
            error = error
                .with_note(format!("{what} as written: `{text}`"))
                .with_note(format!("{what} as it computes{after}: `{goal_text}`"));
        }
        _ => error = error.with_note(format!("{what}{after}: `{goal_text}`")),
    }
    if computed_lhs != shown_lhs {
        error = error.with_note(format!(
            "the search compares what terms compute to: it looked for `{computed_lhs}`, what \
             `{shown_lhs}` computes to, in what {} computes to",
            place.the()
        ));
    }
    if done {
        // Only a goal is tested (an equation `rfl` would prove).
        error = error.with_note(match index {
            0 => "the goal already holds by computing, so `rfl` proves it without a `rewrite`"
                .to_string(),
            _ => format!(
                "the goal already holds by computing{after}, so `rfl` proves it: this rule and \
                 what follows it aren't needed"
            ),
        });
    }
    error = error.with_note(format!(
        "occurrences are looked for by their outer function and compared by computing, \
         and only where they don't mention a variable bound inside {}",
        match place {
            Place::Goal => "the goal",
            Place::Target(_) => "the type",
        }
    ));
    error = error.with_note(if rule.reverse {
        "to replace the left side by the right, write the rule without `<-`"
    } else {
        "to replace the right side by the left, write `rewrite <- …`"
    });
    if found.bound > 0 {
        error = error.with_note(
            "an occurrence under a binder that uses the bound variable can't be rewritten; \
             prove it pointwise and use a lemma like `List.mapCong`",
        );
    }
    error
}

/// `candidate` is a term of the goal (or the target's type) in `cx`'s
/// context, as the search saw it: computed, so it can be long. Both terms
/// are put in notes, shortened.
fn budget_error(
    cx: &Ctx,
    rule: &RewriteRule,
    place: Place,
    candidate: &Term,
    lhs: &Value,
) -> Diagnostic {
    let side = if rule.reverse { "right" } else { "left" };
    let long = shortened(cx, candidate) || folded(cx, lhs).is_some_and(|term| shortened(cx, &term));
    let mut error = Diagnostic::error(
        "E-REWRITE-BUDGET",
        format!(
            "`rewrite` couldn't decide whether a part of {} is the rule's {side} side",
            place.the()
        ),
    )
    .with_label(
        rule.span,
        "comparing them by computing ran out of budget, so the rewrite can't tell which \
         occurrences to replace",
    )
    .with_note(format!(
        "the part of {}, as it computes: `{}`",
        place.the(),
        written(cx, candidate)
    ))
    .with_note(format!("the rule's {side} side: `{}`", shown(cx, lhs)))
    .with_note("this is about cost, not truth: the two may well be equal");
    if long {
        error = error.with_note(
            "the terms are shortened (`…`); set `STITCHWORT_FULL_TERMS=1` to see them whole",
        );
    }
    error.with_note("state the step with `calc`, or rewrite with a more specific equation")
}

fn round_trip_error(
    cx: &Ctx,
    rule: &RewriteRule,
    place: Place,
    lhs: &Value,
    first: Option<&Term>,
) -> Diagnostic {
    let lhs = shown(cx, lhs);
    let message = match first {
        Some(first) => format!(
            "`{}` matched `{lhs}` only up to a detail that comparison ignores",
            written(cx, first)
        ),
        None => format!(
            "replacing `{lhs}` changes {} in a way that can't be undone",
            place.the()
        ),
    };
    Diagnostic::error("E-REWRITE-MOTIVE", message)
        .with_label(
            rule.span,
            format!(
                "after replacing it, {} no longer computes to what it was",
                place.the()
            ),
        )
        .with_note("rewrite a larger term that contains it, or state the step with `calc`")
}

#[cfg(test)]
mod tests {
    use stitchwort_core::Sort;
    use stitchwort_syntax::SourceMap;

    use super::*;
    use crate::Elaborator;

    fn span() -> Span {
        let mut sources = SourceMap::new();
        Span::point(sources.add("test", ""), 0)
    }

    fn ty(n: u32) -> Term {
        Term::Sort(Sort::Type(n))
    }

    #[test]
    fn a_motive_that_does_not_give_the_goal_back_fails_the_round_trip() {
        let e = Elaborator::new();
        let cx = Ctx::new(&e, span());
        // The goal is `Type0 = Type0`. The motive for replacing `Type0` by `Type1`
        // is `x _ => x = Type0`: applied to `Type0` it gives the goal...
        let goal = Value::Eq(
            Rc::new(Value::Sort(Sort::Type(1))),
            Rc::new(Value::Sort(Sort::Type(0))),
            Rc::new(Value::Sort(Sort::Type(0))),
        );
        let lam = |body: Term| {
            Term::Lam(
                "x".into(),
                Icit::Explicit,
                Rc::new(Term::Lam("_".into(), Icit::Explicit, Rc::new(body))),
            )
        };
        let eq = |a: Term, b: Term| Term::Eq(Some(Rc::new(ty(1))), Rc::new(a), Rc::new(b));
        let right = lam(eq(Term::Var(1), ty(0)));
        let lhs = Value::Sort(Sort::Type(0));
        let mut remaining = 1_000_000;
        assert_eq!(
            round_trip(&cx, &right, &lhs, &Value::Refl, &goal, &mut remaining).unwrap(),
            Some(true)
        );
        // ...and one that dropped an occurrence, `x _ => x = x`, gives
        // `Type0 = Type0` too, but `x _ => Type1 = x` doesn't.
        let wrong = lam(eq(ty(1), Term::Var(1)));
        assert_eq!(
            round_trip(&cx, &wrong, &lhs, &Value::Refl, &goal, &mut remaining).unwrap(),
            Some(false)
        );
        // Out of budget is neither.
        let mut none = 0;
        assert_eq!(
            round_trip(&cx, &right, &lhs, &Value::Refl, &goal, &mut none).unwrap(),
            None
        );
    }

    #[test]
    fn a_candidate_of_another_type_is_not_of_the_carrier() {
        let e = Elaborator::new();
        let mut cx = Ctx::new(&e, span());
        // `x: Type0` and `p: x`: the variable `p` has type `x`.
        cx.bind_hidden("x".into(), Value::Sort(Sort::Type(0)));
        cx.bind_hidden("p".into(), Value::var(0));
        let p = Term::Var(0);
        let mut kcx = kernel_context(&cx).unwrap();
        assert!(has_carrier(&cx, &mut kcx, &p, &Value::var(0)).unwrap());
        assert!(!has_carrier(&cx, &mut kcx, &p, &Value::Sort(Sort::Type(0))).unwrap());
        // A type with an unsolved metavariable in it is solved by the check.
        let m = cx.g().new_meta(span());
        let spine = vec![stitchwort_core::value::Elim::App(
            Value::var(0),
            Icit::Explicit,
        )];
        let unknown = Value::Neutral(stitchwort_core::value::Head::Meta(m), spine.into());
        assert!(has_carrier(&cx, &mut kcx, &p, &unknown).unwrap());
        assert!(cx.g().meta_solution(m).is_some());
    }

    #[test]
    fn keys_compare_the_head_and_the_number_of_arguments() {
        let app = |f: Term, a: Term| Term::app(f, a);
        let f = Term::Def(DefId(3));
        assert!(key(&app(f.clone(), Term::Var(0)), 0) == key(&app(f.clone(), Term::Var(5)), 0));
        assert!(key(&app(f.clone(), Term::Var(0)), 0) != key(&f, 0));
        // A variable's key is its index in the goal's context.
        assert!(key(&Term::Var(2), 1) == Some(Key::Var(1, 0)));
        // A bound variable or a metavariable at the head can't be an occurrence.
        assert!(key(&app(Term::Var(0), Term::Var(1)), 1).is_none());
        assert!(key(&Term::Meta(0), 0).is_none());
    }

    #[test]
    fn a_term_mentions_a_bound_variable_only_below_its_own_binders() {
        let app = |f: Term, a: Term| Term::app(f, a);
        let f = Term::Def(DefId(0));
        // Under one binder of the goal: `f #0` mentions it, `f #1` doesn't.
        assert!(mentions_bound(&app(f.clone(), Term::Var(0)), 1));
        assert!(!mentions_bound(&app(f.clone(), Term::Var(1)), 1));
        // A binder of its own shifts: `f (y => #1)` mentions the goal's `#0`.
        let lam = |b: Term| Term::Lam("y".into(), Icit::Explicit, Rc::new(b));
        assert!(mentions_bound(&app(f.clone(), lam(Term::Var(1))), 1));
        assert!(!mentions_bound(&app(f, lam(Term::Var(0))), 1));
        assert!(!mentions_bound(&Term::Var(0), 0));
    }
}
