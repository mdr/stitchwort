//! `rewrite repeatedly [r1, r2]` (docs/proposals/simp-revisited.md, stage 1;
//! D3647 for the name).
//!
//! ```text
//! rewrite repeatedly [r1, <- r2, f]           -- rewrite until no rule fits, then close
//! rewrite repeatedly [r1, r2] then t          -- t proves what is left
//! rewrite repeatedly [r1, r2] then ?          -- shows what is left
//! ```
//!
//! The rules are tried in turn, in the order listed and round again, each
//! by `rewrite`'s own search ([`super::rewrite_once`]: the goal as written
//! first, then what it computes to). A rule that finds nothing, or whose
//! premise isn't proved, is skipped, and not tried again until another rule
//! has changed the goal. It stops when every rule in turn has found
//! nothing, and then closes the goal: by
//! computing (`byComputing`), by hypotheses that contradict each other, or
//! by a hypothesis, or a part of one, of the goal's type (`cases`' closers,
//! without splitting or `arithmetic`). The proof is the `J` chain the same
//! `rewrite`s write, so the kernel checks it like any other.
//!
//! **Rules.** As `rewrite`'s: a proof of an equation (hypotheses and
//! `Bool` facts among them), its arguments left open if not given. A
//! definition's name, `f`, stands for its generated arm equations `f.eqK`
//! (`function-equations.md`), or, when it has none (a body that isn't a
//! `match`), one step of it, `f x… = <body>`, proved by `byComputing`. Before
//! anything is rewritten each rule is checked: it must be an equation whose
//! left side has a head, and whose right side has no instance of its left
//! (`a + b = b + a` would rewrite forever): `E-REWRITE-REPEATEDLY-RULE`.
//!
//! **Limits.** At most [`STEP_LIMIT`] rewrites; past that it is
//! `E-REWRITE-REPEATEDLY-BUDGET`, naming the rules that kept applying.
//! Each rule's search has `rewrite`'s own evaluation budget.
//!
//! **Stated, not chained** (D3656, readable-proofs.md R7). What a rule set
//! leaves is not fixed by the proof text, so a `then t` that depends on its
//! exact form breaks far from the cause when a rule changes. `t` should be
//! a stated fact (an ascription, a typed `let`, `calc`) or a closer that
//! doesn't depend on the form (`arithmetic`, `cases`, ...);
//! otherwise it is `W-REWRITE-REPEATEDLY-UNSTATED`.

use std::rc::Rc;

use stitchwort_core::value::{Elim, Spine, force, unfold_once};
use stitchwort_core::{DefId, Term, Value};
use stitchwort_syntax::ast::{Expr, Name as AstName, RewriteRule};
use stitchwort_syntax::{Diagnostic, Span};

use super::{Equation, Key, Place, Stats, Step, elaborate_rule, key, rewrite_once, search_budget};
use crate::check::{Ctx, Result, check, infer};
use crate::undo::{Snapshot, fatal};

/// The most rewrites one `rewrite repeatedly` makes. The toy formatter's
/// proofs use 1 to 5 (simp-revisited.md §1.2); a set that rewrites more than
/// this is almost always going round in a cycle.
pub(crate) const STEP_LIMIT: usize = 500;

/// Errors from a rule's search that mean only "this rule doesn't apply
/// here": it is skipped, as a rule that isn't there would be.
const DOES_NOT_APPLY: [&str; 4] = [
    "E-REWRITE-NOTHING",
    "E-REWRITE-PREMISE",
    "E-REWRITE-MOTIVE",
    "E-REWRITE-CONG",
];

/// A rule as used: a written one, or one of the equations a definition's
/// name stands for.
struct Listed {
    rule: RewriteRule,
    /// Which written rule it comes from.
    origin: usize,
    /// What its left side is looked for by ([`Shape`]).
    shape: Shape,
}

/// What a rule's left side needs a goal to have for it to fit: its head as
/// written, or its head and every definition it calls once computed. A
/// goal with neither has no place the rule can fit, so the search, the
/// costly part, is skipped: matching what it computes to compares by
/// computing, which for a large left side (a call that unfolds into the
/// printer's whole state) is most of the time a `rewrite repeatedly` takes.
struct Shape {
    written: Option<(Key, Vec<DefId>)>,
    computed: Option<(Key, Vec<DefId>)>,
}

/// The same for a goal: every key and called definition in it.
struct Present {
    written: Option<(Vec<Key>, Vec<DefId>)>,
    computed: Option<(Vec<Key>, Vec<DefId>)>,
}

/// The keys of every part of the goal, as it computes and as written: what
/// a rule's [`Listed::keys`] are looked up in. `None` where the goal is too
/// large to read back, and every rule is tried.
fn goal_keys(cx: &Ctx, goal: &Value, written: Option<&Term>) -> Present {
    let collect = |term: &Term, keys: &mut Vec<Key>| {
        for (t, under) in term.subterms() {
            if let Some(k) = key(t, under)
                && !keys.contains(&k)
            {
                keys.push(k);
            }
        }
    };
    let g = cx.g();
    let computed = force(&g, goal.clone())
        .ok()
        .and_then(|v| cx.quote(&v).ok())
        .map(|t| {
            let mut keys = Vec::new();
            collect(&t, &mut keys);
            (keys, calls(&t))
        });
    let shown = cx.quote_folded(goal).ok().map(|t| {
        let mut keys = Vec::new();
        collect(&t, &mut keys);
        let mut called = calls(&t);
        if let Some(written) = written {
            collect(written, &mut keys);
            called.extend(calls(written));
        }
        (keys, called)
    });
    Present {
        written: shown,
        computed,
    }
}

/// The definitions `term` calls.
fn calls(term: &Term) -> Vec<DefId> {
    let mut out = Vec::new();
    for (t, _) in term.subterms() {
        if let Term::Def(d) = t
            && !out.contains(d)
        {
            out.push(*d);
        }
    }
    out
}

/// Whether a rule of `shape` may fit somewhere in a goal with `present`.
fn may_fit(shape: &Shape, present: &Present) -> bool {
    let fits = |shape: &Option<(Key, Vec<DefId>)>, present: &Option<(Vec<Key>, Vec<DefId>)>| match (
        shape, present,
    ) {
        (_, None) => true,
        (Some((k, needs)), Some((keys, calls))) => {
            keys.contains(k) && needs.iter().all(|d| calls.contains(d))
        }
        (None, Some(_)) => false,
    };
    fits(&shape.written, &present.written) || fits(&shape.computed, &present.computed)
}

/// `rewrite repeatedly [rules]` against `expected`, with or without `then`.
pub(super) fn rewrite_repeatedly(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Rewrite {
        rules: written,
        body,
        keyword,
        repeatedly,
        then,
        ..
    } = expr
    else {
        unreachable!("only called on a rewrite");
    };
    let header = keyword.to(written.last().map_or(*keyword, |r| r.span));
    let mut rules = Vec::new();
    for (origin, rule) in written.iter().enumerate() {
        for rule in expand(cx, rule)? {
            let shape = check_rule(cx, &rule)?;
            rules.push(Listed {
                rule,
                origin,
                shape,
            });
        }
    }
    let mut written_goal = cx.written_goal.take();
    let mut goal = match cx.e.tables.interfaces.is_empty() {
        true => expected.clone(),
        false => crate::interfaces::find_ready_dictionaries(cx, expected, None)?
            .unwrap_or_else(|| expected.clone()),
    };
    let mut steps: Vec<Step> = Vec::new();
    // Per rewrite: the rule used, and for `goal --at`, the goal before and
    // the equation as used.
    let mut trail: Vec<(usize, Value, Option<Value>)> = Vec::new();
    // Round robin: after a rule rewrites, the next one is tried, not the
    // first, and it stops once every rule in turn has found nothing. A rule
    // that found nothing isn't tried again until something has changed.
    let mut failed_at: Vec<Option<usize>> = vec![None; rules.len()];
    let mut present = (
        usize::MAX,
        Present {
            written: None,
            computed: None,
        },
    );
    let mut idle = 0;
    let mut index = 0;
    while idle < rules.len() {
        let listed = &rules[index];
        let version = trail.len();
        let this = index;
        index = (index + 1) % rules.len();
        if failed_at[this] == Some(version) {
            idle += 1;
            continue;
        }
        if present.0 != version {
            present = (version, goal_keys(cx, &goal, written_goal.as_ref()));
        }
        failed_at[this] = Some(version);
        idle += 1;
        if !may_fit(&listed.shape, &present.1) {
            continue;
        }
        let snapshot = Snapshot::take(cx);
        let errors = cx.e.attempt.branch_errors.borrow().len();
        let mut remaining = search_budget(cx);
        let mut stats = Stats::default();
        let found = rewrite_once(
            cx,
            &listed.rule,
            // Not 0: that asks whether the body proves the goal without
            // the rule, which is for a message this never shows.
            this + 1,
            Place::Goal,
            &goal,
            written_goal.clone(),
            None,
            &mut remaining,
            &mut stats,
            true,
        );
        if std::env::var_os("STITCHWORT_REWRITE_METRICS").is_some() {
            eprintln!(
                "rewrite-repeatedly-metrics: at={}..{} rule={} applied={} steps={}",
                listed.rule.span.start,
                listed.rule.span.end,
                rule_name(&listed.rule),
                matches!(&found, Ok(f) if !f.is_empty()),
                search_budget(cx) - remaining,
            );
        }
        match found {
            Ok(found) if !found.is_empty() => {
                let after = found.last().expect("not empty").goal.clone();
                let shown = match &written_goal {
                    Some(written) => written.clone(),
                    None => cx.quote_folded(&goal)?,
                };
                let next_written = written_after(cx, &shown, &found)?;
                // A rewrite that leaves the goal as written as it was (a
                // definition's step found where it has already computed) is
                // no progress: the rule didn't apply.
                let next_shown = match &next_written {
                    Some(written) => written.clone(),
                    None => cx.quote_folded(&after)?,
                };
                if crate::matching::same(&shown, &next_shown) {
                    restore(cx, snapshot, errors);
                    continue;
                }
                let used = cx.e.take_rule();
                let before = std::mem::replace(&mut goal, after);
                steps.extend(found);
                written_goal = next_written;
                trail.push((this, before, used));
                idle = 0;
                if trail.len() > STEP_LIMIT {
                    return Err(budget_error(header, &rules, &trail));
                }
            }
            Ok(_) => restore(cx, snapshot, errors),
            Err(e) if fatal(&e) => return Err(e),
            Err(e) if DOES_NOT_APPLY.contains(&e.code) => restore(cx, snapshot, errors),
            Err(e) => return Err(e),
        }
    }
    let mut notes = trail
        .iter()
        .enumerate()
        .filter(|(_, (index, _, _))| cx.e.records_steps(rules[*index].rule.span))
        .map(|(k, _)| k)
        .collect::<Vec<_>>();
    if !notes.is_empty() {
        let extra = [Some(*keyword), *repeatedly, *then]
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let afters = trail
            .iter()
            .skip(1)
            .map(|(_, before, _)| before.clone())
            .chain(std::iter::once(goal.clone()))
            .collect::<Vec<_>>();
        for k in notes.drain(..) {
            let (index, before, used) = &trail[k];
            cx.e.note_step(
                cx,
                crate::goals::StepNote {
                    form: crate::goals::StepForm::RepeatedRule,
                    head: rules[*index].rule.span,
                    index: Some((k, trail.len())),
                    before: Some(before.clone()),
                    after: afters[k].clone(),
                    after_term: None,
                    adds: Vec::new(),
                    rule: used.clone(),
                    parts: Vec::new(),
                    target: None,
                    extra: extra.clone(),
                },
            );
        }
    }
    let base = match body {
        Some(body) => {
            if !stated(body) {
                warn_unstated(cx, header, body);
            }
            check(cx, body, &goal)?
        }
        None => close(cx, header, written, &rules, &trail, &goal)?,
    };
    let mut term = base;
    for step in steps.into_iter().rev() {
        term = Term::J(Rc::new(step.motive), Rc::new(term), Rc::new(step.proof));
    }
    Ok(term)
}

fn restore(cx: &mut Ctx, snapshot: Snapshot, errors: usize) {
    cx.e.attempt.branch_errors.borrow_mut().truncate(errors);
    snapshot.restore(cx);
    cx.e.take_rule();
}

/// The goal as written after `found`'s rewrites of `written`: each step's
/// left side, as written, replaced by its right side, where it is written
/// so; `None` where a step's left side isn't (it was found in what the goal
/// computes to). Read back from the goal's value, a call that computes at
/// once is shown as what it computes to (`printer.write indent " " 1` as its
/// `if`), so without this a rule about the call, written in the goal before
/// another rule's step, isn't there to see after it.
fn written_after(cx: &Ctx, written: &Term, found: &[Step]) -> Result<Option<Term>> {
    let g = cx.g();
    let depth = cx.level();
    let mut written = written.clone();
    for step in found {
        let lhs = cx.quote_folded(&step.sides.0)?;
        let rhs = cx.quote_folded(&step.sides.1)?;
        if !written
            .subterms()
            .any(|(t, under)| under == 0 && crate::matching::same(t, &lhs))
        {
            return Ok(None);
        }
        written = crate::lift::replace_with(
            &g,
            &written,
            depth,
            &|level| Ok(Term::Var(depth - 1 - level)),
            &|t, binders| (binders == 0 && crate::matching::same(t, &lhs)).then(|| rhs.clone()),
        )?;
    }
    Ok(Some(written))
}

/// Closes what the rules left: by computing, by contradicting hypotheses,
/// or by a hypothesis (or a part of one) of its type.
fn close(
    cx: &mut Ctx,
    header: Span,
    written: &[RewriteRule],
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    goal: &Value,
) -> Result<Term> {
    let rfl = Expr::Var(AstName {
        text: "byComputing".into(),
        span: header,
    });
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let refl = crate::Elaborator::unnoted_in(cx, |cx| check(cx, &rfl, goal));
    let refl = match refl {
        Ok(term) => return Ok(term),
        Err(e) if e.code == "E-REFL" => {
            restore(cx, snapshot, errors);
            Some(e)
        }
        Err(e) if fatal(&e) => return Err(e),
        Err(_) => {
            restore(cx, snapshot, errors);
            None
        }
    };
    if let Some(term) = crate::cases::close_by_hypotheses(cx, goal)? {
        return Ok(term);
    }
    Err(left_open(cx, header, written, rules, trail, goal, refl))
}

/// `E-REWRITE-REPEATEDLY`: the goal the rules left, which nothing closed.
fn left_open(
    cx: &Ctx,
    header: Span,
    written: &[RewriteRule],
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
    goal: &Value,
    refl: Option<Diagnostic>,
) -> Diagnostic {
    let mut error = Diagnostic::error(
        "E-REWRITE-REPEATEDLY",
        "`rewrite repeatedly` left a goal it can't close",
    )
    .with_label(
        header,
        "no rule applies any more, and what is left isn't closed",
    )
    .with_note(format!("what is left: `{}`", cx.show(goal)));
    // `E-REFL`'s notes say where the two sides differ.
    if let Some(refl) = refl {
        for note in refl.notes {
            error = error.with_note(note);
        }
    }
    let mut counts = vec![0usize; written.len()];
    for (index, _, _) in trail {
        counts[rules[*index].origin] += 1;
    }
    let applied = written
        .iter()
        .zip(&counts)
        .filter(|(_, n)| **n > 0)
        .map(|(rule, n)| format!("`{}` ({n}×)", rule_name(rule)))
        .collect::<Vec<_>>();
    let unused = written
        .iter()
        .zip(&counts)
        .filter(|(_, n)| **n == 0)
        .map(|(rule, _)| format!("`{}`", rule_name(rule)))
        .collect::<Vec<_>>();
    error = match applied.is_empty() {
        true => error.with_note("no rule applied: the goal is as it was"),
        false => error.with_note(format!("the rules applied: {}", applied.join(", "))),
    };
    if !unused.is_empty() {
        error = error.with_note(format!(
            "never applied: {} (a rule applies where its left side is in the goal, as written \
             or as it computes, with its premises proved)",
            unused.join(", ")
        ));
    }
    error.with_note(
        "prove what is left with `then t` (state it: `then (t: P)`), or see it as a goal with \
         `then ?`",
    )
}

/// `E-REWRITE-REPEATEDLY-BUDGET`: the rules made [`STEP_LIMIT`] rewrites.
fn budget_error(
    header: Span,
    rules: &[Listed],
    trail: &[(usize, Value, Option<Value>)],
) -> Diagnostic {
    let names = trail
        .iter()
        .map(|(index, _, _)| rule_name(&rules[*index].rule))
        .collect::<Vec<_>>();
    let last = &names[names.len().saturating_sub(8)..];
    let error = Diagnostic::error(
        "E-REWRITE-REPEATEDLY-BUDGET",
        format!("`rewrite repeatedly` made {STEP_LIMIT} rewrites without finishing"),
    )
    .with_label(header, "the rules keep applying")
    .with_note(format!(
        "the last rules applied: {}",
        last.iter()
            .map(|n| format!("`{n}`"))
            .collect::<Vec<_>>()
            .join(", ")
    ));
    let error = match cycle(trail) {
        Some(period) => {
            let turn = trail[trail.len() - period..]
                .iter()
                .map(|(index, _, _)| format!("`{}`", rule_name(&rules[*index].rule)))
                .collect::<Vec<_>>();
            error.with_note(match period {
                1 => format!("{} keeps applying to its own result", turn[0]),
                _ => format!(
                    "they go round in a cycle: {} undo each other's work",
                    turn.join(", ")
                ),
            })
        }
        None => error,
    };
    error.with_note(
        "take out a rule that turns another's result back, or one that rewrites a term into a \
         larger one containing it; a fact such as `a + b = b + a` belongs in `algebra` or \
         `arithmetic`",
    )
}

/// The shortest period, up to 4, with which the trail's last rewrites repeat
/// (twice over), if any.
fn cycle(trail: &[(usize, Value, Option<Value>)]) -> Option<usize> {
    let rules = trail.iter().map(|(index, _, _)| *index).collect::<Vec<_>>();
    (1..=4).find(|&p| {
        rules.len() >= 2 * p && {
            let n = rules.len();
            rules[n - p..] == rules[n - 2 * p..n - p]
        }
    })
}

/// How a rule is named in messages: its proof as written when that is a
/// name (`List.appendAssoc`, `<- h`), else the rule's place in the list.
fn rule_name(rule: &RewriteRule) -> String {
    fn path(e: &Expr) -> Option<String> {
        match e {
            Expr::Var(n) => Some(n.text.to_string()),
            Expr::Field(base, n) => Some(format!("{}.{}", path(base)?, n.text)),
            Expr::App(f, _) => Some(format!("{} …", path(f)?.trim_end_matches(" …"))),
            _ => None,
        }
    }
    let name = path(&rule.proof).unwrap_or_else(|| "this rule".into());
    match rule.reverse {
        true => format!("<- {name}"),
        false => name,
    }
}

/// The rules a written rule stands for: itself, or for a definition's name,
/// its arm equations, or one step of it.
fn expand(cx: &mut Ctx, rule: &RewriteRule) -> Result<Vec<RewriteRule>> {
    let Some(d) = definition_named(cx, &rule.proof)? else {
        return Ok(vec![rule.clone()]);
    };
    let g = cx.g();
    let def = g.def(d);
    let has_arms = def.body().is_some_and(|body| {
        matches!(
            Term::peel_lams_rc(body, def.arity()).strip_loc(),
            Term::Case(..) | Term::NumCase(..)
        )
    });
    if !has_arms {
        return Ok(vec![RewriteRule {
            unfold: true,
            ..rule.clone()
        }]);
    }
    let field = |base: &Expr, name: String| {
        Expr::Field(
            Box::new(base.clone()),
            AstName {
                text: name.as_str().into(),
                span: rule.proof.span(),
            },
        )
    };
    let exists = |cx: &mut Ctx, e: &Expr| -> Result<Option<bool>> {
        let snapshot = Snapshot::take(cx);
        let errors = cx.e.attempt.branch_errors.borrow().len();
        let found = infer(cx, e);
        restore(cx, snapshot, errors);
        match found {
            Ok(_) => Ok(Some(true)),
            Err(e) if fatal(&e) => Err(e),
            // Not generated, for a reason recorded with the definition: the
            // arm's equation doesn't exist, the next one may.
            Err(e) if e.code == "E-NO-EQUATION" => Ok(Some(false)),
            Err(_) => Ok(None),
        }
    };
    let mut out = Vec::new();
    for k in 1.. {
        let arm = field(&rule.proof, format!("eq{k}"));
        match exists(cx, &arm)? {
            Some(true) => out.push(arm),
            Some(false) => {}
            None => {
                // An arm with alternatives has one equation per alternative.
                let mut alternatives = Vec::new();
                for n in 1.. {
                    let alternative = field(&arm, format!("or{n}"));
                    match exists(cx, &alternative)? {
                        Some(true) => alternatives.push(alternative),
                        _ => break,
                    }
                }
                if alternatives.is_empty() {
                    break;
                }
                out.extend(alternatives);
            }
        }
    }
    if out.is_empty() {
        return Err(Diagnostic::error(
            "E-REWRITE-REPEATEDLY-RULE",
            "this definition has no equations to rewrite with",
        )
        .with_label(
            rule.proof.span(),
            "a definition by arms, with no arm equation generated",
        )
        .with_note(
            "a definition's name stands for its arm equations `f.eq1`, `f.eq2`, …; state the \
             step you need as a lemma and list that instead",
        ));
    }
    let mut rules = Vec::new();
    for proof in out {
        let arm = RewriteRule {
            reverse: false,
            unfold: false,
            proof,
            span: rule.span,
        };
        if waits(cx, &arm, d)? {
            rules.push(RewriteRule {
                reverse: rule.reverse,
                ..arm
            });
        }
    }
    Ok(rules)
}

/// Whether the arm equation `arm` of `d` is about a call that waits: one
/// whose arguments don't already pick the arm. An arm whose patterns are
/// constructors (`len [x, ..rest]`) computes at once wherever it applies,
/// so computing already does what it would, and as a rule it would be
/// matched against what it computes to.
fn waits(cx: &mut Ctx, arm: &RewriteRule, d: DefId) -> Result<bool> {
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let outcome = (|| -> Result<bool> {
        let equation = elaborate_rule(cx, arm, Place::Goal)?;
        let g = cx.g();
        Ok(match &equation.lhs {
            Value::Call(id, spine, _) if *id == d => {
                !stitchwort_core::value::matches_at_once(&g, d, spine)?
            }
            _ => false,
        })
    })();
    restore(cx, snapshot, errors);
    match outcome {
        Err(e) if !fatal(&e) => Ok(false),
        outcome => outcome,
    }
}

/// The definition `proof` names, if it is one that isn't a proof: a
/// function or value, not a theorem or a hypothesis.
fn definition_named(cx: &mut Ctx, proof: &Expr) -> Result<Option<DefId>> {
    if !matches!(proof, Expr::Var(_) | Expr::Field(..)) {
        return Ok(None);
    }
    if let Expr::Var(n) = proof
        && (cx.lookup(&n.text).is_some() || cx.local(&n.text)?.is_some())
    {
        return Ok(None);
    }
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let found = infer(cx, proof);
    restore(cx, snapshot, errors);
    let (term, _) = match found {
        Ok(found) => found,
        Err(e) if fatal(&e) => return Err(e),
        // The search reports it, with `rewrite`'s own message.
        Err(_) => return Ok(None),
    };
    let Term::Def(d) = term.strip_loc() else {
        return Ok(None);
    };
    let g = cx.g();
    let def = g.def(*d);
    if def.theorem() || def.opaque() || def.body().is_none() {
        return Ok(None);
    }
    // A definition whose result is an equation is a proof of one.
    let (_, result) = crate::decreasing::split_pis(def.ty(), None);
    if matches!(result.strip_loc(), Term::Eq(..)) {
        return Ok(None);
    }
    Ok(Some(*d))
}

/// The equation of one step of the definition `rule.proof` names: `f x… =
/// <its body applied to x…>`, its arguments open, proved by `byComputing`.
pub(super) fn unfold_equation(cx: &mut Ctx, rule: &RewriteRule) -> Result<Equation> {
    let g = cx.g();
    let (term, _) = infer(cx, &rule.proof)?;
    let Term::Def(d) = term.strip_loc().clone() else {
        unreachable!("an unfold rule names a definition")
    };
    let rule_metas = cx.metas().metas.borrow().len();
    let def = g.def(d);
    let mut ty = def.ty_value().clone();
    let mut call = Term::Def(d);
    let mut spine = Spine::new();
    for _ in 0..def.arity() {
        let Value::Pi(_, icit, domain, rest) = force(&g, ty.clone())? else {
            break;
        };
        let meta = cx.fresh_meta_of(&domain);
        let value = cx.eval(&meta)?;
        call = Term::app_icit(call, meta, icit);
        spine.push(Elim::App(value.clone(), icit));
        ty = rest.apply(&g, value)?;
    }
    let lhs = cx.eval(&call)?;
    let rhs = unfold_once(&g, d, spine)?;
    // `byComputing`, with its type: `J` is checked against the type of its
    // proof, which a bare `byComputing` doesn't give.
    let stated = Term::Eq(
        Some(Rc::new(cx.quote(&ty)?)),
        Rc::new(cx.quote_folded(&rhs)?),
        Rc::new(call),
    );
    let to_lhs = Term::Ann(Rc::new(Term::Refl), Rc::new(stated));
    let (lhs, rhs) = match rule.reverse {
        true => (rhs, lhs),
        false => (lhs, rhs),
    };
    Ok(Equation {
        carrier: ty,
        lhs,
        rhs,
        to_lhs,
        rule_metas,
        premises: Vec::new(),
    })
}

/// Refuses a rule that can't be used: one that isn't an equation, whose
/// left side has no head to look for, or that rewrites forever by itself
/// (its right side holds an instance of its left).
fn check_rule(cx: &mut Ctx, rule: &RewriteRule) -> Result<Shape> {
    let snapshot = Snapshot::take(cx);
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let outcome = check_rule_inner(cx, rule);
    restore(cx, snapshot, errors);
    outcome
}

fn check_rule_inner(cx: &mut Ctx, rule: &RewriteRule) -> Result<Shape> {
    let bad = |e: Diagnostic| -> Diagnostic {
        match e.code {
            "E-REWRITE-RULE" => Diagnostic {
                code: "E-REWRITE-REPEATEDLY-RULE",
                ..e
            },
            _ => e,
        }
    };
    let equation = elaborate_rule(cx, rule, Place::Goal).map_err(bad)?;
    let lhs = cx.quote_folded(&equation.lhs)?;
    let Some(lhs_key) = key(&lhs, 0) else {
        return Err(Diagnostic::error(
            "E-REWRITE-REPEATEDLY-RULE",
            "this rule's left side has nothing to look for",
        )
        .with_label(
            rule.proof.span(),
            format!(
                "its left side is `{}`, an unknown or a variable it binds",
                cx.show(&equation.lhs)
            ),
        )
        .with_note("give the arguments that fix its left side, or turn the rule round with `<-`"));
    };
    let g = cx.g();
    let computed = cx.quote(&force(&g, equation.lhs.clone())?)?;
    let shape = Shape {
        written: Some((lhs_key.clone(), calls(&lhs))),
        // Not the definitions it calls: computed with the rule's unknowns
        // open, a call can stay that computes away once they are solved.
        computed: key(&computed, 0).map(|k| (k, Vec::new())),
    };
    let mut remaining = search_budget(cx);
    // A rule whose sides compute to each other (a definition's step) can't
    // loop: what it gives back is only progress where it is written
    // differently, which the search checks.
    let snapshot = Snapshot::take(cx);
    let computes = g
        .machine
        .budget
        .limited(&mut remaining, || cx.unify(&equation.lhs, &equation.rhs));
    let solved = snapshot.solved_since(cx);
    snapshot.restore(cx);
    match computes {
        Ok(Some(true)) if solved.is_empty() => return Ok(shape),
        Err(e) if fatal(&e) => return Err(e),
        _ => {}
    }
    let rhs = cx.quote_folded(&equation.rhs)?;
    for (sub, under) in rhs.subterms() {
        if under > 0 || key(sub, 0).as_ref() != Some(&lhs_key) {
            continue;
        }
        let snapshot = Snapshot::take(cx);
        let value = cx.eval(sub)?;
        let unified = g
            .machine
            .budget
            .limited(&mut remaining, || cx.unify(&equation.lhs, &value));
        snapshot.restore(cx);
        match unified {
            Ok(Some(true)) => {
                return Err(Diagnostic::error(
                    "E-REWRITE-REPEATEDLY-RULE",
                    "this rule would rewrite forever",
                )
                .with_label(
                    rule.proof.span(),
                    format!(
                        "it rewrites `{}` to `{}`, which it fits again",
                        cx.show(&equation.lhs),
                        cx.show(&equation.rhs)
                    ),
                )
                .with_note(
                    "its right side holds an instance of its left side, so each rewrite makes \
                     another place it applies",
                )
                .with_note(
                    "use it once with `rewrite`, with its arguments given; reordering a sum or \
                     product is `algebra`'s or `arithmetic`'s job",
                ));
            }
            Err(e) if fatal(&e) => return Err(e),
            _ => {}
        }
    }
    Ok(shape)
}

/// Whether the term after `then` is one R7 allows after flexible rewriting:
/// a stated fact, or a closer that doesn't depend on the goal's exact form.
fn stated(body: &Expr) -> bool {
    match body {
        Expr::Ann(..)
        | Expr::Calc { .. }
        | Expr::Goal(_)
        | Expr::Hole(_)
        | Expr::Omega { .. }
        | Expr::Ring { .. }
        | Expr::Cases { .. }
        | Expr::LocalDefs { .. }
        | Expr::Rewrite {
            repeatedly: Some(_),
            ..
        } => true,
        Expr::Let { ty, .. } => ty.is_some(),
        Expr::Var(n) => matches!(n.text.as_ref(), "byComputing" | "byDecision"),
        _ => false,
    }
}

/// `W-REWRITE-REPEATEDLY-UNSTATED`, once per `rewrite repeatedly`.
fn warn_unstated(cx: &Ctx, header: Span, body: &Expr) {
    let warning = Diagnostic::warning(
        "W-REWRITE-REPEATEDLY-UNSTATED",
        "the proof after `rewrite repeatedly … then` depends on exactly what the rules left",
    )
    .with_label(header, "what this leaves isn't written in the proof")
    .with_label(body.span(), "this proves it as it is now")
    .with_note(
        "if a rule changes, this step breaks with no goal to compare against; state what is \
         left, `then (t: P)` or a typed `let`, or end with a closer (`arithmetic`, `cases`)",
    );
    let mut warnings = cx.e.attempt.lambda_warnings.borrow_mut();
    let span = Some(header);
    if !(warnings.iter())
        .any(|w| w.code == warning.code && w.labels.first().map(|l| l.span) == span)
    {
        warnings.push(warning);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_syntax::ast::Name;

    fn rule(text: &str, reverse: bool) -> RewriteRule {
        let span = Span::NOWHERE;
        let mut parts = text.split('.');
        let mut proof = Expr::Var(Name {
            text: parts.next().expect("a name").into(),
            span,
        });
        for part in parts {
            proof = Expr::Field(
                Box::new(proof),
                Name {
                    text: part.into(),
                    span,
                },
            );
        }
        RewriteRule {
            reverse,
            unfold: false,
            proof,
            span,
        }
    }

    #[test]
    fn a_rule_is_named_by_its_path_and_direction() {
        assert_eq!(
            rule_name(&rule("List.appendAssoc", false)),
            "List.appendAssoc"
        );
        assert_eq!(rule_name(&rule("h", true)), "<- h");
    }
}
