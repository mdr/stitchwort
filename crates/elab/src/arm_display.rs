//! Goals at a `match` arm show the arm as written (SW-3317,
//! docs/proposals/catch-all-goals.md, option A).
//!
//! The case tree splits a variable wherever *some* row needs it, and an arm
//! reached through a split its own patterns didn't ask for (a catch-all after
//! `"ab"`, `Some True`) is checked once per leaf, each with the variable
//! replaced by that leaf's constructor. What a hole there shows is the last
//! leaf's goal: cells nobody named, and one case of several. This module
//! keeps what it takes to show the goal the arm's own patterns give instead:
//! the case tree's splits on the way to the leaf, and which of them the arm
//! needed. It changes only what a goal displays; the term, its hash and
//! the kernel never see it.
//!
//! The checker records a [`Split`] as it enters each branch of a case, and
//! the leaf an [`Arm`] with the levels the arm's row left alone
//! ([`crate::Row::unsplit`]). A hole asks for a [`View`]: the context and goal
//! as they would be with only the splits the arm needed, found by replaying
//! the splits from the state before the first (so a goal `p o ∧ q None` at
//! the `None` leaf is not taken for `p o ∧ q o`: nothing is searched for).
//! A part of the state the arm's own body has changed since (a hypothesis
//! it rewrote, a goal it stepped) is left as it is: only what still equals
//! the leaf's own state is replaced by the arm's.

use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::value::{eval, quote, quote_folded};
use stitchwort_core::{Term, Value};
use stitchwort_syntax::Span;

use crate::Tree;
use crate::check::Ctx;
use crate::kernel;

/// What the first split of a case tree found, shared by all its splits.
pub(crate) struct Root {
    env: Vec<Value>,
    types: Vec<Value>,
    goal: Value,
    /// The arm whose right-hand side holds this `match`, if it is checked
    /// inside one: its own undoing applies after this tree's.
    outer: Option<Rc<Arm>>,
}

/// One split on the way to a leaf: variable `x` made a constructor (or a
/// number), and the fields it bound after it.
pub(crate) struct Split {
    parent: Option<Rc<Split>>,
    root: Rc<Root>,
    x: usize,
    value: Value,
    /// The number of variables before the fields.
    base: usize,
    /// The fields' types, as they were bound.
    fields: Vec<Value>,
}

/// A leaf's arm, while its right-hand side is checked.
pub(crate) struct Arm {
    path: Rc<Split>,
    /// The levels the arm's patterns left as variables or `_`
    /// ([`crate::Row::unsplit`]).
    unsplit: Vec<usize>,
    /// How many leaves check the arm.
    cases: usize,
}

/// What a goal at an arm shows, besides the arm's own state.
pub(crate) struct View {
    /// The variables as the arm's patterns leave them.
    pub(crate) env: Vec<Value>,
    pub(crate) types: Vec<Value>,
    /// The goal as the arm's patterns leave it, if the hole's is the arm's.
    pub(crate) goal: Option<Value>,
    /// What the leaf's goal computes to, with the leaf's value for a
    /// variable written as the variable: the "computes to" line.
    pub(crate) computed: Option<Value>,
    /// How many times the arm is checked (1 if once).
    pub(crate) cases: usize,
    /// Whether anything above differs from what the leaf has.
    pub(crate) changed: bool,
}

/// An expression a `match` on it generalises: the variable standing for it
/// in the arms is shown as the expression where an arm leaves it alone.
#[derive(Clone)]
pub(crate) struct Scrutinee {
    /// The variable standing for it.
    x: usize,
    /// The expression, in the context of the first `vars` variables.
    term: Term,
    vars: usize,
    /// The variable of the equation `match h: e` binds, if it names one.
    equation: Option<usize>,
}

/// Notes the scrutinees of a generalised `match` whose arms are about to be
/// checked: scrutinee `i` is the variable at level `base + i`, its equation
/// the one `equations` gives for `i`. Returns how many were there before,
/// for [`forget_scrutinees`].
pub(crate) fn note_scrutinees<'t>(
    cx: &Ctx,
    terms: impl Iterator<Item = &'t Term>,
    base: usize,
    equations: &[(usize, usize)],
) -> usize {
    let mut goals = cx.e.goals.borrow_mut();
    let before = goals.scrutinees.len();
    for (i, term) in terms.enumerate() {
        goals.scrutinees.push(Scrutinee {
            x: base + i,
            term: term.clone(),
            vars: base,
            equation: equations.iter().find(|&&(j, _)| j == i).map(|&(_, l)| l),
        });
    }
    before
}

/// Takes back what [`note_scrutinees`] noted.
pub(crate) fn forget_scrutinees(cx: &Ctx, before: usize) {
    cx.e.goals.borrow_mut().scrutinees.truncate(before);
}

/// Sets how many leaves check each arm in `tree`.
pub(crate) fn count_cases(tree: &mut Tree) {
    fn tally(tree: &Tree, counts: &mut HashMap<Span, usize>) {
        match tree {
            Tree::Leaf { span, .. } => *counts.entry(*span).or_default() += 1,
            Tree::Guard {
                leaf, otherwise, ..
            } => {
                tally(leaf, counts);
                tally(otherwise, counts);
            }
            Tree::Absurd { .. } | Tree::Missing { .. } => {}
            Tree::Case { branches, .. } => branches.iter().for_each(|(_, t)| tally(t, counts)),
            Tree::NumCase { arms, default, .. } => {
                arms.iter().for_each(|(_, t)| tally(t, counts));
                tally(default, counts);
            }
        }
    }
    fn set(tree: &mut Tree, counts: &HashMap<Span, usize>) {
        match tree {
            Tree::Leaf { span, cases, .. } => *cases = counts[span],
            Tree::Guard {
                leaf, otherwise, ..
            } => {
                set(leaf, counts);
                set(otherwise, counts);
            }
            Tree::Absurd { .. } | Tree::Missing { .. } => {}
            Tree::Case { branches, .. } => branches.iter_mut().for_each(|(_, t)| set(t, counts)),
            Tree::NumCase { arms, default, .. } => {
                arms.iter_mut().for_each(|(_, t)| set(t, counts));
                set(default, counts);
            }
        }
    }
    let mut counts = HashMap::default();
    tally(tree, &mut counts);
    set(tree, &counts);
}

/// The shared start of the splits a case makes now: the state before them,
/// unless a case above already made it.
pub(crate) fn root_of(cx: &Ctx, goal: &Value) -> (Option<Rc<Split>>, Rc<Root>) {
    let goals = cx.e.goals.borrow();
    match &goals.split_path {
        Some(parent) => (Some(parent.clone()), parent.root.clone()),
        None => (
            None,
            Rc::new(Root {
                env: cx.env.clone(),
                types: cx.types.clone(),
                goal: goal.clone(),
                outer: goals.arm.clone(),
            }),
        ),
    }
}

/// Puts back the path a split replaced when dropped, so an early return
/// from the branch's check can't leave a stale one.
pub(crate) struct SplitGuard<'e> {
    e: &'e crate::Elaborator,
    saved: Option<Rc<Split>>,
}

impl Drop for SplitGuard<'_> {
    fn drop(&mut self) {
        self.e.goals.borrow_mut().split_path = self.saved.take();
    }
}

/// Records the split of `x` into `value` whose `base..` fields are now
/// bound, until the guard is dropped.
pub(crate) fn enter_split<'e>(
    cx: &Ctx<'e>,
    start: &(Option<Rc<Split>>, Rc<Root>),
    x: usize,
    value: &Value,
    base: usize,
) -> SplitGuard<'e> {
    let (parent, root) = start;
    let node = Rc::new(Split {
        parent: parent.clone(),
        root: root.clone(),
        x,
        value: value.clone(),
        base,
        fields: cx.types[base.min(cx.types.len())..].to_vec(),
    });
    let saved = cx.e.goals.borrow_mut().split_path.replace(node);
    SplitGuard { e: cx.e, saved }
}

/// A leaf's arm is about to be checked: what [`view`] needs of it. Returns
/// what [`leave_arm`] puts back. Nothing is kept for an arm that needs
/// nothing undone and is checked once, which is nearly all of them.
pub(crate) fn enter_arm(
    cx: &Ctx,
    unsplit: &[usize],
    cases: usize,
) -> (Option<Rc<Split>>, Option<Rc<Arm>>) {
    let mut goals = cx.e.goals.borrow_mut();
    let path = goals.split_path.take();
    let arm = match &path {
        Some(path) if !unsplit.is_empty() || cases > 1 => Some(Rc::new(Arm {
            path: path.clone(),
            unsplit: unsplit.to_vec(),
            cases,
        })),
        _ => None,
    };
    let saved_arm = match arm {
        Some(arm) => goals.arm.replace(arm),
        None => goals.arm.clone(),
    };
    (path, saved_arm)
}

/// Puts back what [`enter_arm`] returned.
pub(crate) fn leave_arm(cx: &Ctx, saved: (Option<Rc<Split>>, Option<Rc<Arm>>)) {
    let mut goals = cx.e.goals.borrow_mut();
    goals.split_path = saved.0;
    goals.arm = saved.1;
}

/// The state as the case tree left it at `path`, with the splits of the
/// levels in `skip` not made. `cx` stands in for what the tree didn't
/// record (variables an indexed family's split or a guard bound).
fn replay(cx: &Ctx, path: &Split, skip: &[usize]) -> Option<(Vec<Value>, Vec<Value>, Value)> {
    let g = cx.g();
    let mut chain = vec![path];
    while let Some(parent) = &chain.last()?.parent {
        chain.push(parent);
    }
    chain.reverse();
    let root = &chain[0].root;
    let (mut env, mut types, mut goal) = (root.env.clone(), root.types.clone(), root.goal.clone());
    for node in chain {
        while env.len() < node.base {
            let l = env.len();
            env.push(cx.env.get(l)?.clone());
            types.push(cx.types.get(l)?.clone());
        }
        if env.len() != node.base {
            return None;
        }
        if !skip.contains(&node.x) {
            let goal_term = quote_folded(&g, env.len(), &goal).ok()?;
            let goal_value = eval(&g, &env, &goal_term).ok()?;
            let mut next_env =
                kernel::substitute_folded(&g, &env, node.x, &node.value, &env).ok()?;
            next_env[node.x] = node.value.clone();
            let next_types =
                kernel::substitute_folded(&g, &env, node.x, &node.value, &types).ok()?;
            goal = kernel::substitute_folded(&g, &env, node.x, &node.value, &[goal_value])
                .ok()?
                .pop()?;
            env = next_env;
            types = next_types;
        }
        for (i, ty) in node.fields.iter().enumerate() {
            env.push(Value::var(node.base + i));
            types.push(ty.clone());
        }
    }
    Some((env, types, goal))
}

/// Whether two values are the same as the context holds them.
fn same(cx: &Ctx, a: &Value, b: &Value) -> bool {
    match (cx.quote_folded(a), cx.quote_folded(b)) {
        (Ok(a), Ok(b)) => crate::matching::same(&a, &b),
        _ => false,
    }
}

/// How a goal at a hole in the current arm is shown: `None` if there is
/// nothing to say about the arm (the usual case).
pub(crate) fn view(cx: &Ctx, expected: &Value) -> Option<View> {
    let innermost = cx.e.goals.borrow().arm.clone()?;
    let mut view = View {
        env: cx.env.clone(),
        types: cx.types.clone(),
        goal: None,
        computed: None,
        cases: 1,
        changed: false,
    };
    let mut goal = expected.clone();
    let mut current = Some(innermost);
    while let Some(arm) = current {
        view.cases *= arm.cases;
        if !arm.unsplit.is_empty() {
            undo(cx, &arm, &mut view, &mut goal);
        }
        current = arm.path.root.outer.clone();
    }
    if view.changed {
        scrutinee_expressions(cx, &mut view);
    }
    Some(view)
}

/// `view` with `arm`'s unneeded splits undone, where the state is still the
/// leaf's. `goal` is the goal as the arms inside this one left it.
fn undo(cx: &Ctx, arm: &Arm, view: &mut View, goal: &mut Value) {
    let Some((all_env, all_types, all_goal)) = replay(cx, &arm.path, &[]) else {
        return;
    };
    let Some((env, types, shown_goal)) = replay(cx, &arm.path, &arm.unsplit) else {
        return;
    };
    // A `match e:` equation keeps what the leaf has: its proof is about the
    // case, which `rewrite` can use.
    let equations: Vec<usize> = (cx.e.goals.borrow().scrutinees.iter())
        .filter_map(|s| s.equation)
        .collect();
    for l in 0..all_env.len().min(view.env.len()) {
        if same(cx, &view.env[l], &all_env[l]) {
            view.changed |= !same(cx, &env[l], &all_env[l]);
            view.env[l] = env[l].clone();
        }
        if !equations.contains(&l) && same(cx, &view.types[l], &all_types[l]) {
            view.changed |= !same(cx, &types[l], &all_types[l]);
            view.types[l] = types[l].clone();
        }
    }
    if same(cx, goal, &all_goal) && !same(cx, &shown_goal, &all_goal) {
        view.computed = computed_back(cx, arm, view, &all_env, goal);
        view.changed = true;
        *goal = shown_goal.clone();
        view.goal = Some(shown_goal);
    }
}

/// The levels the arm's path binds as fields of a split.
fn skipped_fields(arm: &Arm) -> Vec<usize> {
    let mut fields = Vec::new();
    let mut node = Some(&arm.path);
    while let Some(n) = node {
        fields.extend(n.base..n.base + n.fields.len());
        node = n.parent.as_ref();
    }
    fields
}

/// What `leaf_goal` computes to, with each value the leaf gave a variable the
/// arm left alone written as that variable.
fn computed_back(
    cx: &Ctx,
    arm: &Arm,
    view: &View,
    leaf_env: &[Value],
    leaf_goal: &Value,
) -> Option<Value> {
    let g = cx.g();
    let level = cx.level();
    let mut term = quote(&g, level, leaf_goal).ok()?;
    let fields = skipped_fields(arm);
    for &x in &arm.unsplit {
        // Only where the user can write the variable, and for a value that
        // has cells of its own (`MkText [MkChar code✝ valid✝, ..tail✝]`),
        // which nothing else could be mistaken for: a closed value like
        // `Blue` also occurs where it has nothing to do with the variable.
        if fields.contains(&x) || cx.name_of_level(x).is_none() {
            continue;
        }
        let value = quote(&g, level, leaf_env.get(x)?).ok()?;
        if matches!(value.strip_loc(), Term::Var(i) if level - 1 - *i == x) {
            continue;
        }
        if !crate::goals::levels_in(&value, level)?
            .iter()
            .any(|l| fields.contains(l))
        {
            continue;
        }
        let hook = |t: &Term, under: usize| {
            crate::matching::same_shifted(&value, t, under, 0)
                .then(|| Term::Var(under + level - 1 - x))
        };
        term =
            crate::lift::replace_with(&g, &term, level, &|l| Ok(Term::Var(level - 1 - l)), &hook)
                .ok()?;
    }
    eval(&g, &view.env, &term).ok()
}

/// A `match` on an expression binds a variable for it, which a goal at an
/// arm that left it alone would show as that variable's compiler-made name:
/// shown as the expression instead, unless the arm names it. The `match
/// e: …` equation is left as the leaf has it.
fn scrutinee_expressions(cx: &Ctx, view: &mut View) {
    let g = cx.g();
    let noted: Vec<(usize, Term, usize, Option<usize>)> = (cx.e.goals.borrow().scrutinees.iter())
        .map(|s| (s.vars, s.term.clone(), s.x, s.equation))
        .collect();
    for (vars, term, x, equation) in &noted {
        let own = matches!(view.env.get(*x),
            Some(Value::Neutral(stitchwort_core::value::Head::Var(l, _), s)) if l == x && s.is_empty());
        if !own || cx.name_of_level(*x).is_some() || *vars > view.env.len() {
            continue;
        }
        let Ok(value) = eval(&g, &view.env[..*vars], term) else {
            continue;
        };
        let mut types = Vec::new();
        let mut at = Vec::new();
        for (l, ty) in view.types.iter().enumerate() {
            if l != *x && Some(l) != *equation {
                types.push(ty.clone());
                at.push(l);
            }
        }
        let Ok(mut substituted) = kernel::substitute_folded(&g, &view.env, *x, &value, &types)
        else {
            continue;
        };
        for l in at.into_iter().rev() {
            view.types[l] = substituted.pop().expect("one in, one out");
        }
        let mut values: Vec<Value> = view
            .goal
            .iter()
            .chain(view.computed.iter())
            .cloned()
            .collect();
        let Ok(out) = kernel::substitute_folded(&g, &view.env, *x, &value, &values) else {
            continue;
        };
        values = out;
        let mut it = values.into_iter();
        if view.goal.is_some() {
            view.goal = it.next();
        }
        if view.computed.is_some() {
            view.computed = it.next();
        }
    }
}

/// Where the arm is checked, for a goal's or an error's note: what each
/// variable the arm left alone is, here. `None` if the arm is checked once.
pub(crate) fn case_note(cx: &Ctx) -> Option<(usize, Option<String>)> {
    let arm = cx.e.goals.borrow().arm.clone()?;
    if arm.cases < 2 {
        return None;
    }
    let (env, _, _) = replay(cx, &arm.path, &[])?;
    // The fields of a split say nothing the variable they are part of
    // doesn't.
    let fields = skipped_fields(&arm);
    let names = cx.shown_names(false);
    let noted: Vec<(usize, usize, Term)> = (cx.e.goals.borrow().scrutinees.iter())
        .map(|s| (s.x, s.vars, s.term.clone()))
        .collect();
    let g = cx.g();
    let mut parts = Vec::new();
    for &x in arm.unsplit.iter().filter(|x| !fields.contains(x)) {
        let value = env.get(x)?;
        if matches!(value, Value::Neutral(stitchwort_core::value::Head::Var(l, _), s) if *l == x && s.is_empty())
        {
            continue;
        }
        let name = match noted.iter().find(|(l, _, _)| *l == x) {
            Some((_, vars, term)) => eval(&g, &cx.env[..(*vars).min(cx.env.len())], term)
                .ok()
                .map(|v| cx.show(&v)),
            None => match cx.name_of_level(x) {
                Some(n) => Some(n.to_string()),
                None if !names[x].starts_with('%') && !names[x].contains('✝') => {
                    Some(names[x].to_string())
                }
                None => None,
            },
        };
        parts.push(match name {
            Some(name) => format!("`{name}` is `{}`", case_text(&cx.show(value))),
            None => format!("the matched value is `{}`", case_text(&cx.show(value))),
        });
    }
    let case = (!parts.is_empty()).then(|| format!("where {}", parts.join(" and ")));
    Some((arm.cases, case))
}

/// `error` from the arm's right-hand side, saying which case it is in when
/// the arm is checked in several: its first failing case is the one
/// reported.
pub(crate) fn in_case(
    cx: &Ctx,
    error: stitchwort_syntax::Diagnostic,
) -> stitchwort_syntax::Diagnostic {
    if error.code == crate::goals::UNFINISHED || error.code == "E-RESOURCE" {
        return error;
    }
    if error
        .notes
        .iter()
        .any(|n| n.starts_with("this arm is checked in"))
    {
        return error;
    }
    match case_note(cx) {
        Some((n, Some(case))) => error.with_note(format!(
            "this arm is checked in {n} cases, and this error is in the case {case}"
        )),
        _ => error,
    }
}

/// A text's cases as `"ab" ++ …`, not `MkText ['a', 'b', head✝, ..tail✝]`;
/// anything else as it is.
fn case_text(shown: &str) -> String {
    let Some(inner) = shown
        .strip_prefix("MkText [")
        .and_then(|rest| rest.strip_suffix(']'))
    else {
        return shown.to_string();
    };
    let mut text = String::new();
    let mut rest = false;
    for item in inner.split(", ") {
        let literal = item
            .strip_prefix('\'')
            .and_then(|i| i.strip_suffix('\''))
            .filter(|c| c.chars().count() == 1);
        match (literal, rest) {
            (Some(c), false) => text.push_str(c),
            _ => rest = true,
        }
    }
    match (text.is_empty(), rest) {
        (_, false) => crate::quoted_text(&text),
        (true, true) => "…".to_string(),
        (false, true) => format!("{} ++ …", crate::quoted_text(&text)),
    }
}
