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
//!
//! A `match` in an arm's right-hand side starts its splits from that arm's
//! leaf, so an arm of the inner `match` is shown by replaying its splits
//! from the outer arm as written instead (the same rule again: only what
//! the outer arm's body left as the leaf had it), and it is checked once
//! per leaf of each: the counts multiply.

use std::rc::Rc;

use crate::check::quote_internal;
use stitchwort_core::collections::HashMap;
use stitchwort_core::value::eval;
use stitchwort_core::{Term, Value};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::Expr;

use crate::Tree;
use crate::check::{Ctx, quote_folded};
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
    /// What an indexed family's split also decided: variables made another
    /// value (an index `n` made `Succ n✝`), after the split's own `x`.
    /// Worked out when first needed, since comparing every variable is
    /// costly and only an arm's goal shown in a message needs it.
    solved: Solved,
    /// The fields' values, where the split solved some of them; otherwise
    /// they are the variables themselves.
    field_values: Option<Vec<Value>>,
}

/// What an indexed family's split decided, found by comparing the context's
/// values before and after the split the first time it is asked for.
struct Solved {
    /// The context's values before and after the split, up to its `base`,
    /// and the level they are compared at; none for a split that solved
    /// nothing.
    compare: Option<(Vec<Value>, Vec<Value>, usize)>,
    x: usize,
    found: std::cell::OnceCell<Vec<(usize, Value)>>,
}

impl Solved {
    fn none() -> Self {
        Solved {
            compare: None,
            x: 0,
            found: std::cell::OnceCell::from(Vec::new()),
        }
    }

    fn get(&self, cx: &Ctx) -> &[(usize, Value)] {
        self.found.get_or_init(|| {
            let Some((before, after, level)) = &self.compare else {
                return Vec::new();
            };
            let g = cx.g();
            let same = |a: &Value, b: &Value| match (
                quote_folded(&g, *level, a),
                quote_folded(&g, *level, b),
            ) {
                (Ok(a), Ok(b)) => crate::matching::same(&a, &b),
                _ => false,
            };
            (0..before.len().min(after.len()))
                .filter(|&l| l != self.x && !same(&after[l], &before[l]))
                .map(|l| (l, after[l].clone()))
                .collect()
        })
    }
}

/// A leaf's arm, while its right-hand side is checked.
pub(crate) struct Arm {
    path: Rc<Split>,
    /// The levels the arm's patterns left as variables or `_`
    /// ([`crate::Row::unsplit`]).
    unsplit: Vec<usize>,
    /// How many leaves check the arm.
    cases: usize,
    /// What the arm is known not to be, from the literal arms above it.
    facts: Rc<[ArmFact]>,
}

/// A fact about an arm's catch-all column: the variable at `level` is not
/// the literal, written as in the arm above (`5`, `'k'`, `"ab"`).
#[derive(Clone, Debug)]
pub(crate) struct ArmFact {
    pub(crate) level: usize,
    pub(crate) literal: String,
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
    /// Whether the goal the arm's cases give depends on which case it is:
    /// the case tree's splits changed the match's goal.
    pub(crate) depends: bool,
    /// What the arms around the hole are known not to be.
    pub(crate) facts: Vec<ArmFact>,
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

/// Which arm a leaf takes: its right-hand side (the alternatives of an
/// or-pattern are leaves of their own spans, but one arm), or its span for an
/// arm with none.
#[derive(PartialEq, Eq, Hash)]
enum ArmKey {
    Rhs(usize),
    Span(Span),
}

fn arm_key(rhs: &Option<&Expr>, span: Span) -> ArmKey {
    match rhs {
        Some(rhs) => ArmKey::Rhs(std::ptr::from_ref(*rhs) as usize),
        None => ArmKey::Span(span),
    }
}

/// Sets how many leaves check each arm in `tree`.
pub(crate) fn count_cases(tree: &mut Tree) {
    fn tally(tree: &Tree, counts: &mut HashMap<ArmKey, usize>, times: usize) {
        match tree {
            Tree::Leaf { span, rhs, .. } => {
                let n = counts.entry(arm_key(rhs, *span)).or_default();
                *n = n.saturating_add(times);
            }
            Tree::Guard {
                leaf, otherwise, ..
            } => {
                tally(leaf, counts, times);
                tally(otherwise, counts, times);
            }
            Tree::Absurd { .. } | Tree::Missing { .. } => {}
            Tree::Case { branches, .. } => {
                branches.iter().for_each(|(_, t)| tally(t, counts, times));
            }
            Tree::NumCase { arms, default, .. } => {
                arms.iter().for_each(|(_, t)| tally(t, counts, times));
                tally(default, counts, times);
            }
            Tree::FinNumbers { numbers, .. } => {
                for (tree, once) in numbers.weighted_subtrees() {
                    tally(tree, counts, times.saturating_mul(once));
                }
            }
        }
    }
    fn set(tree: &mut Tree, counts: &HashMap<ArmKey, usize>) {
        match tree {
            Tree::Leaf {
                span, rhs, cases, ..
            } => *cases = counts[&arm_key(rhs, *span)],
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
            Tree::FinNumbers { numbers, .. } => {
                Rc::make_mut(numbers)
                    .subtrees_mut()
                    .for_each(|t| set(t, counts));
            }
        }
    }
    let mut counts = HashMap::default();
    tally(tree, &mut counts, 1);
    set(tree, &counts);
}

/// Puts on each leaf the facts of its arm, from `facts` (by the address of
/// the arm's right-hand side).
pub(crate) fn set_facts(tree: &mut Tree, facts: &HashMap<usize, Rc<[ArmFact]>>) {
    match tree {
        Tree::Leaf {
            rhs, facts: own, ..
        } => {
            if let Some(found) = rhs.and_then(|r| facts.get(&(std::ptr::from_ref(r) as usize))) {
                *own = found.clone();
            }
        }
        Tree::Guard {
            leaf, otherwise, ..
        } => {
            set_facts(leaf, facts);
            set_facts(otherwise, facts);
        }
        Tree::Absurd { .. } | Tree::Missing { .. } => {}
        Tree::Case { branches, .. } => branches.iter_mut().for_each(|(_, t)| set_facts(t, facts)),
        Tree::NumCase { arms, default, .. } => {
            arms.iter_mut().for_each(|(_, t)| set_facts(t, facts));
            set_facts(default, facts);
        }
        Tree::FinNumbers { numbers, .. } => {
            Rc::make_mut(numbers)
                .subtrees_mut()
                .for_each(|t| set_facts(t, facts));
        }
    }
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
    push_split(cx, start, x, value, base, Solved::none(), None)
}

/// [`enter_split`] for the split of `x` on an indexed family, after the
/// unifier ran: `before` is the context's values as it left them, so what
/// else the split decided shows as the variables that differ.
pub(crate) fn enter_family_split<'e>(
    cx: &Ctx<'e>,
    start: &(Option<Rc<Split>>, Rc<Root>),
    x: usize,
    before: &[Value],
) -> SplitGuard<'e> {
    let base = before.len();
    let n = base.min(cx.env.len());
    let solved = Solved {
        compare: Some((before[..n].to_vec(), cx.env[..n].to_vec(), cx.level())),
        x,
        found: std::cell::OnceCell::new(),
    };
    let fields = cx.env.get(base..).map(<[Value]>::to_vec);
    push_split(cx, start, x, &cx.env[x], base, solved, fields)
}

fn push_split<'e>(
    cx: &Ctx<'e>,
    start: &(Option<Rc<Split>>, Rc<Root>),
    x: usize,
    value: &Value,
    base: usize,
    solved: Solved,
    field_values: Option<Vec<Value>>,
) -> SplitGuard<'e> {
    let (parent, root) = start;
    let node = Rc::new(Split {
        parent: parent.clone(),
        root: root.clone(),
        x,
        value: value.clone(),
        base,
        fields: cx.types[base.min(cx.types.len())..].to_vec(),
        solved,
        field_values,
    });
    let saved = cx.e.goals.borrow_mut().split_path.replace(node);
    SplitGuard { e: cx.e, saved }
}

/// A leaf's arm is about to be checked: what [`view`] needs of it. Returns
/// what [`leave_arm`] puts back. Nothing is kept for an arm that needs
/// nothing undone, is checked once and is in no arm that does, which is
/// nearly all of them.
pub(crate) fn enter_arm(
    cx: &Ctx,
    unsplit: &[usize],
    cases: usize,
    facts: &Rc<[ArmFact]>,
) -> (Option<Rc<Split>>, Option<Rc<Arm>>) {
    let mut goals = cx.e.goals.borrow_mut();
    let path = goals.split_path.take();
    let arm = match &path {
        Some(path)
            if !unsplit.is_empty() || cases > 1 || goals.arm.is_some() || !facts.is_empty() =>
        {
            Some(Rc::new(Arm {
                path: path.clone(),
                unsplit: unsplit.to_vec(),
                cases,
                facts: facts.clone(),
            }))
        }
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

/// The variables' values and types, and the goal.
type State = (Vec<Value>, Vec<Value>, Value);

/// The state its case tree started from.
fn root_state(path: &Split) -> State {
    let root = &path.root;
    (root.env.clone(), root.types.clone(), root.goal.clone())
}

/// The state as the case tree left it at `path`, starting from `start`
/// (the tree's own, or that state as an outer arm is written), with the
/// splits of the levels in `skip` not made. `cx` stands in for what the
/// tree didn't record (variables an indexed family's split or a guard
/// bound).
fn replay(cx: &Ctx, path: &Split, skip: &[usize], start: State) -> Option<State> {
    let g = cx.g();
    let mut chain = vec![path];
    while let Some(parent) = &chain.last()?.parent {
        chain.push(parent);
    }
    chain.reverse();
    let (mut env, mut types, mut goal) = start;
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
            // What the split decided can mention its fields, so they are
            // in scope for each substitution.
            let mut scope = env.clone();
            scope.extend((0..node.fields.len()).map(|i| Value::var(node.base + i)));
            let split = std::iter::once((node.x, &node.value))
                .chain(node.solved.get(cx).iter().map(|(l, v)| (*l, v)));
            for (x, value) in split {
                let goal_term = quote_folded(&g, scope.len(), &goal).ok()?;
                let goal_value = eval(&g, &scope, &goal_term).ok()?;
                let mut next_env = kernel::substitute_folded(&g, &scope, x, value, &env).ok()?;
                next_env[x] = value.clone();
                types = kernel::substitute_folded(&g, &scope, x, value, &types).ok()?;
                goal = kernel::substitute_folded(&g, &scope, x, value, &[goal_value])
                    .ok()?
                    .pop()?;
                scope[x] = value.clone();
                env = next_env;
            }
        }
        for (i, ty) in node.fields.iter().enumerate() {
            let value = (node.field_values.as_ref()).and_then(|values| values.get(i));
            env.push(value.cloned().unwrap_or_else(|| Value::var(node.base + i)));
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

/// `arm` and the arms it is in, innermost first.
fn arms(arm: Rc<Arm>) -> Vec<Rc<Arm>> {
    let mut out = vec![arm];
    while let Some(outer) = out.last().and_then(|a| a.path.root.outer.clone()) {
        out.push(outer);
    }
    out
}

/// The levels of `match e:` equations: they keep what the leaf has, as
/// their proofs are about the case, which `rewrite` can use.
fn equations(cx: &Ctx) -> Vec<usize> {
    (cx.e.goals.borrow().scrutinees.iter())
        .filter_map(|s| s.equation)
        .collect()
}

/// `arm`'s leaf state, and that state with the splits undone that neither
/// it nor an arm it is in needed.
fn leaf_and_shown(cx: &Ctx, arm: &Arm, equations: &[usize]) -> Option<(State, State)> {
    let leaf = replay(cx, &arm.path, &[], root_state(&arm.path))?;
    let shown = replay(cx, &arm.path, &arm.unsplit, shown_start(cx, arm, equations))?;
    Some((leaf, shown))
}

/// Where `arm`'s splits start for the display: its tree's starting state,
/// with what still equals the enclosing arm's leaf (what that arm's body
/// left alone before this `match`) as the enclosing arm is written.
fn shown_start(cx: &Ctx, arm: &Arm, equations: &[usize]) -> State {
    let mut start = root_state(&arm.path);
    let Some((leaf, shown)) =
        (arm.path.root.outer.as_ref()).and_then(|outer| leaf_and_shown(cx, outer, equations))
    else {
        return start;
    };
    let (env, types, goal) = &mut start;
    for l in 0..env.len().min(leaf.0.len()).min(shown.0.len()) {
        if same(cx, &env[l], &leaf.0[l]) {
            env[l] = shown.0[l].clone();
        }
        if !equations.contains(&l) && same(cx, &types[l], &leaf.1[l]) {
            types[l] = shown.1[l].clone();
        }
    }
    if same(cx, goal, &leaf.2) {
        *goal = shown.2;
    }
    start
}

/// How a goal at a hole in the current arm is shown: `None` if there is
/// nothing to say about the arm (the usual case).
pub(crate) fn view(cx: &Ctx, expected: &Value) -> Option<View> {
    let innermost = cx.e.goals.borrow().arm.clone()?;
    let arms = arms(innermost.clone());
    let mut view = View {
        env: cx.env.clone(),
        types: cx.types.clone(),
        goal: None,
        computed: None,
        cases: arms.iter().map(|a| a.cases).product(),
        changed: false,
        depends: false,
        facts: arms.iter().flat_map(|a| a.facts.iter().cloned()).collect(),
    };
    if arms.iter().any(|a| !a.unsplit.is_empty()) {
        undo(cx, &arms, &mut view, expected);
    }
    if view.changed {
        scrutinee_expressions(cx, &mut view);
    }
    if view.cases > 1
        && let Some((_, _, leaf_goal)) =
            replay(cx, &innermost.path, &[], root_state(&innermost.path))
    {
        view.depends = !same(cx, &leaf_goal, &innermost.path.root.goal);
    }
    Some(view)
}

/// `view` with the unneeded splits of `arms` (innermost first) undone,
/// where the state is still the leaf's.
///
/// A hole whose goal isn't the arm's (an argument's, a lambda's body's
/// goal that the arm's goal is a function type of) leaves the context as
/// the leaf has it when the goal mentions a variable the display would
/// change, so that the two agree; the note then says the goal is the last
/// case's ([`View::goal`] is `None`).
fn undo(cx: &Ctx, arms: &[Rc<Arm>], view: &mut View, goal: &Value) {
    let equations = equations(cx);
    let Some(((all_env, all_types, all_goal), (env, types, shown_goal))) =
        leaf_and_shown(cx, &arms[0], &equations)
    else {
        return;
    };
    let peeled = peeled(cx, &all_goal, &shown_goal, all_env.len(), goal);
    let hole_goal = peeled.as_ref().map(|p| (p.0.clone(), p.1.clone()));
    if hole_goal.is_none() && mentions_changed(cx, goal, &all_env, &env) {
        return;
    }
    for l in 0..all_env.len().min(view.env.len()).min(env.len()) {
        if same(cx, &view.env[l], &all_env[l]) {
            view.changed |= !same(cx, &env[l], &all_env[l]);
            view.env[l] = env[l].clone();
        }
        if !equations.contains(&l) && same(cx, &view.types[l], &all_types[l]) {
            view.changed |= !same(cx, &types[l], &all_types[l]);
            view.types[l] = types[l].clone();
        }
    }
    // What the hole's own arguments are, as the arm as written gives them.
    for (l, leaf_type, shown_type) in peeled.iter().flat_map(|p| p.2.iter()) {
        if view.types.get(*l).is_some_and(|t| same(cx, t, leaf_type)) {
            view.changed |= !same(cx, shown_type, leaf_type);
            view.types[*l] = shown_type.clone();
        }
    }
    if let Some((leaf_goal, shown_goal)) = hole_goal
        && !same(cx, &shown_goal, &leaf_goal)
    {
        view.computed = computed_back(cx, arms, view, &all_env, goal, &shown_goal);
        view.changed = true;
        view.goal = Some(shown_goal);
    }
}

/// The arm's goal, `leaf` as the leaf has it and `shown` as the arm is
/// written, in the form `hole` has: the arm's goal itself, or what it is
/// after the function arguments `hole`'s lambdas bound (the variables from
/// `bound` on). `None` if `hole` is neither.
fn peeled(cx: &Ctx, leaf: &Value, shown: &Value, bound: usize, hole: &Value) -> Option<Peeled> {
    let g = cx.g();
    let (mut leaf, mut shown) = (leaf.clone(), shown.clone());
    let mut domains = Vec::new();
    for l in bound..=cx.level() {
        if same(cx, hole, &leaf) {
            return Some((leaf, shown, domains));
        }
        let (Value::Pi(_, _, a, ac, _), Value::Pi(_, _, b, bc, _)) = (&leaf, &shown) else {
            return None;
        };
        domains.push((l, (**a).clone(), (**b).clone()));
        let arg = Value::var(l);
        let (next_leaf, next_shown) = (ac.apply(&g, arg.clone()).ok()?, bc.apply(&g, arg).ok()?);
        (leaf, shown) = (next_leaf, next_shown);
    }
    None
}

/// The arm's goal as the leaf has it and as the arm is written, after the
/// arguments a hole's lambdas bound: each one's level and type in the two.
type Peeled = (Value, Value, Vec<(usize, Value, Value)>);

/// Whether `goal` mentions a variable whose value the arm as written has
/// different from the leaf's.
fn mentions_changed(cx: &Ctx, goal: &Value, leaf: &[Value], shown: &[Value]) -> bool {
    let level = cx.level();
    let Some(levels) =
        (cx.quote_folded(goal).ok()).and_then(|term| crate::goals::levels_in(&term, level))
    else {
        return true;
    };
    levels
        .into_iter()
        .any(|l| matches!((leaf.get(l), shown.get(l)), (Some(a), Some(b)) if !same(cx, a, b)))
}

/// The levels the arms' paths bind as fields of a split.
fn skipped_fields(arms: &[Rc<Arm>]) -> Vec<usize> {
    let mut fields = Vec::new();
    for arm in arms {
        let mut node = Some(&arm.path);
        while let Some(n) = node {
            fields.extend(n.base..n.base + n.fields.len());
            node = n.parent.as_ref();
        }
    }
    fields
}

/// The levels bound as fields of a split `arm` didn't need, or of a split
/// of such a field: cells of a variable the arm left alone.
fn fields_of_unsplit(arm: &Arm) -> Vec<usize> {
    let mut nodes = Vec::new();
    let mut node = Some(&arm.path);
    while let Some(n) = node {
        nodes.push(n);
        node = n.parent.as_ref();
    }
    let mut fields = Vec::new();
    for n in nodes.into_iter().rev() {
        if arm.unsplit.contains(&n.x) || fields.contains(&n.x) {
            fields.extend(n.base..n.base + n.fields.len());
        }
    }
    fields
}

/// The levels the arms' patterns left alone, and those an indexed family's
/// split they didn't need decided with them.
fn unsplit(cx: &Ctx, arms: &[Rc<Arm>]) -> Vec<usize> {
    let mut levels = Vec::new();
    for arm in arms {
        levels.extend(arm.unsplit.iter().copied());
        let mut node = Some(&arm.path);
        while let Some(n) = node {
            if arm.unsplit.contains(&n.x) {
                levels.extend(n.solved.get(cx).iter().map(|&(l, _)| l));
            }
            node = n.parent.as_ref();
        }
    }
    levels
}

/// What `leaf_goal` computes to, with each value the leaf gave a variable the
/// arms left alone written as that variable.
fn computed_back(
    cx: &Ctx,
    arms: &[Rc<Arm>],
    view: &View,
    leaf_env: &[Value],
    leaf_goal: &Value,
    shown_goal: &Value,
) -> Option<Value> {
    let g = cx.g();
    let level = cx.level();
    let mut term = quote_internal(&g, level, leaf_goal).ok()?;
    // Nothing computed: the leaf's goal is the shown one with the case's
    // values put in, which the shown goal already says.
    let unsplit = unsplit(cx, arms);
    let values: Vec<(usize, Term)> = unsplit
        .iter()
        .filter_map(|&x| Some((x, quote_internal(&g, level, leaf_env.get(x)?).ok()?)))
        .collect();
    let shown = quote_folded(&g, level, shown_goal).ok()?;
    let instance = crate::lift::replace_with(
        &g,
        &shown,
        level,
        &|l| match values.iter().find(|(x, _)| *x == l) {
            Some((_, v)) => Ok(v.clone()),
            None => Ok(Term::Var(level - 1 - l)),
        },
        &|_, _| None,
    )
    .ok()?;
    if crate::matching::same(&term, &instance) {
        return None;
    }
    let fields = skipped_fields(arms);
    for &x in &unsplit {
        // Only where the user can write the variable, and for a value that
        // has cells of its own (`MkText [MkChar code✝ valid✝, ..tail✝]`),
        // which nothing else could be mistaken for: a closed value like
        // `Blue` also occurs where it has nothing to do with the variable.
        if fields.contains(&x) || cx.name_of_level(x).is_none() {
            continue;
        }
        let value = quote_internal(&g, level, leaf_env.get(x)?).ok()?;
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
            Some(Value::Neutral(stitchwort_core::value::Head::Var(l, _, _), s)) if l == x && s.is_empty());
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

/// Where the arm is checked, for a goal's or an error's note: how many
/// times (with the arms it is in), and what each variable they left alone
/// is, here. `None` if the arm is checked once.
pub(crate) fn case_note(cx: &Ctx) -> Option<(usize, Option<String>)> {
    let innermost = cx.e.goals.borrow().arm.clone()?;
    let mut arms = arms(innermost);
    let cases: usize = arms.iter().map(|a| a.cases).product();
    if cases < 2 {
        return None;
    }
    // A matched expression is named as the arms are written: in a `match x`
    // inside an arm that leaves `x` alone, as `x`, not the outer case.
    let shown_env = leaf_and_shown(cx, &arms[0], &equations(cx))
        .map(|(_, (env, _, _))| env)
        .unwrap_or_else(|| cx.env.clone());
    arms.reverse();
    let names = cx.shown_names(false);
    let noted: Vec<(usize, usize, Term)> = (cx.e.goals.borrow().scrutinees.iter())
        .map(|s| (s.x, s.vars, s.term.clone()))
        .collect();
    let g = cx.g();
    let mut parts = Vec::new();
    let mut named = Vec::new();
    for arm in &arms {
        let (env, _, _) = replay(cx, &arm.path, &[], root_state(&arm.path))?;
        // The fields of a split say nothing the variable they are part of
        // doesn't.
        let fields = fields_of_unsplit(arm);
        for &x in arm.unsplit.iter().filter(|x| !fields.contains(x)) {
            let value = env.get(x)?;
            if matches!(value, Value::Neutral(stitchwort_core::value::Head::Var(l, _, _), s) if *l == x && s.is_empty())
            {
                continue;
            }
            let name = match noted.iter().find(|(l, _, _)| *l == x) {
                Some((_, vars, term)) => eval(&g, &shown_env[..(*vars).min(shown_env.len())], term)
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
            // An inner `match` on an outer arm's variable matches a value
            // standing for it, which has its own case.
            let name = name.filter(|n| !named.contains(n));
            named.extend(name.clone());
            parts.push(match name {
                Some(name) => format!("`{name}` is `{}`", case_text(&cx.show(value))),
                None => format!("the matched value is `{}`", case_text(&cx.show(value))),
            });
        }
    }
    let case = (!parts.is_empty()).then(|| format!("where {}", parts.join(" and ")));
    Some((cases, case))
}

/// `error` from the arm's right-hand side, saying which case it is in when
/// the arm is checked in several: its first failing case is the one
/// reported.
pub(crate) fn in_case(
    cx: &Ctx,
    error: stitchwort_syntax::Diagnostic,
) -> stitchwort_syntax::Diagnostic {
    if error.code == crate::goals::UNFINISHED || crate::undo::fatal(&error) {
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
