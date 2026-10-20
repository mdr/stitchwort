//! Unification of indices, for `case` on an indexed data type
//! (docs/proposals/indexed-families.md §6.3). The kernel runs it for each
//! branch of a `case`, and the elaborator calls the same function to find
//! impossible branches (D149), so there's one implementation.
//!
//! **Constraints** are typed: `{ ty, lhs, rhs }`, three values, and both
//! sides have type `ty` (up to conversion, in the current refined context)
//! before every rule is applied. They're formed from a **stack of
//! telescopes**. Each entry has binders (each binder's type a term in the
//! context of `base` and the earlier binders), the values the binders stand
//! for on the left and on the right, and how many are solved. A binder's
//! constraint is formed only once every earlier one is solved, so its type
//! evaluated with the earlier left values and with the earlier right values
//! agree; if they don't, the problem is stuck.
//!
//! The rules, on the constraint just formed, in this order:
//!
//! - **Deletion**: `lhs ≡ rhs`. Solved. (This is axiom K, D138.)
//! - **Solution**: one side is a flexible variable `y` (a context entry
//!   that still stands for itself, and isn't the matched variable). If both
//!   are, the one bound later is solved as the earlier one; if its occurs
//!   check fails, the other way. The occurs check looks in the other side,
//!   in the types of its variables, and transitively in theirs. A failed
//!   occurs check is stuck, never impossible. A solution `y := t` is
//!   substituted into the whole context (values and types), the extra
//!   values (the goal) and every value on the stack.
//! - **Injectivity**: `ty` is a data type in `Type i` (never `Prop`), and
//!   both sides are the same constructor: the binder is solved, and the
//!   constructor's fields are pushed as a new entry.
//! - **Conflict**: `ty` is a data type in `Type i`, and the sides are
//!   different constructors. The branch is impossible.
//! - Numbers are `Succ` of their predecessor, `k + x` is `Succ` applied `k`
//!   times, and a compact list expands one cell, for both rules above.
//! - **Anything else is stuck**: a type former on a side (types are never
//!   taken apart, D139), an application that doesn't compute, an equation
//!   between proofs (its type is a proposition, §6.3.2) that deletion and
//!   solution don't settle, a failed occurs check, a binder whose two types
//!   differ.
//!
//! Only a conflict makes a branch impossible.

use crate::budget::Result;
use crate::check::substitute;
use crate::globals::Globals;
use crate::native;
use crate::term::{Name, Sort, Term};
use crate::value::{Head, Value, conv, eval, expand_step, force, quote};

/// The context unification refines: what each variable stands for and its
/// type (both by level), other values to keep refined along with them (a
/// `case` branch's goal), and the variables that are never solved (the
/// matched variable).
pub struct Scope {
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    pub extra: Vec<Value>,
    pub rigid: Vec<usize>,
}

impl Scope {
    pub fn level(&self) -> usize {
        self.env.len()
    }

    /// The level of `value`, if it's a flexible variable: one that still
    /// stands for itself, and isn't rigid.
    pub fn flexible(&self, value: &Value) -> Option<usize> {
        match value {
            Value::Neutral(Head::Var(l), spine)
                if spine.is_empty() && *l < self.level() && !self.rigid.contains(l) =>
            {
                match &self.env[*l] {
                    Value::Neutral(Head::Var(l2), s) if l2 == l && s.is_empty() => Some(*l),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// An equation between two values of one type.
#[derive(Clone, Debug)]
pub struct Constraint {
    pub ty: Value,
    pub lhs: Value,
    pub rhs: Value,
}

/// Why a problem is stuck.
#[derive(Clone, Debug)]
pub enum Reason {
    /// A side that isn't a constructor or a flexible variable: an
    /// application that doesn't compute, or a variable that can't be solved.
    NotConstructor,
    /// A side that's a type former (`Data`, `Pi`, `Sort`): types are never
    /// taken apart (D139).
    TypeFormer,
    /// A variable occurs in what it would be solved as, or in the types of
    /// its variables (D143: stuck, not impossible).
    Occurs,
    /// An equation between proofs (its type is a proposition): only
    /// deletion and solution apply to it (D137).
    Proof,
    /// A binder whose type, with the earlier left values, differs from its
    /// type with the earlier right values: this is `ty_right`.
    TypesDiffer { ty_right: Value },
}

/// What unifying a problem found.
#[derive(Clone, Debug)]
pub enum Outcome {
    /// Every constraint is solved, by these solutions in order: each a
    /// variable's level and the value it was replaced by (in the context as
    /// it was at that point).
    Solved(Vec<(usize, Value)>),
    /// Two different constructors of a data type in `Type`: no value can
    /// have both sets of indices.
    Conflict(Constraint),
    /// Neither: the kernel refuses the `case`.
    Stuck(Constraint, Reason),
}

/// A telescope on the stack.
struct Entry<'g> {
    binders: &'g [(Name, Term)],
    base: Vec<Value>,
    lhs: Vec<Value>,
    rhs: Vec<Value>,
    solved: usize,
}

/// Unifies `lhs` with `rhs`, values for the telescope `binders` (each
/// binder's type in the context of `base` and the earlier binders),
/// refining `scope` by every solution. For a `case` branch: the index
/// telescope, the scrutinee type's parameters, its indices, and the
/// constructor's result indices.
///
/// On `Conflict` or `Stuck`, `scope` may have been refined part way.
pub fn unify<'g>(
    g: &'g Globals,
    scope: &mut Scope,
    binders: &'g [(Name, Term)],
    base: Vec<Value>,
    lhs: Vec<Value>,
    rhs: Vec<Value>,
) -> Result<Outcome> {
    debug_assert!(lhs.len() == binders.len() && rhs.len() == binders.len());
    let mut stack = vec![Entry {
        binders,
        base,
        lhs,
        rhs,
        solved: 0,
    }];
    let mut solutions = Vec::new();
    loop {
        g.budget.step()?;
        let level = scope.level();
        let Some(top) = stack.last() else {
            return Ok(Outcome::Solved(solutions));
        };
        let k = top.solved;
        if k == top.binders.len() {
            stack.pop();
            continue;
        }
        // The next constraint: its type with the earlier left values, which
        // must be its type with the earlier right values.
        let binder_ty = &top.binders[k].1;
        let env_left: Vec<Value> = top.base.iter().chain(&top.lhs[..k]).cloned().collect();
        let ty = eval(g, &env_left, binder_ty)?;
        let lhs = force(g, top.lhs[k].clone())?;
        let rhs = force(g, top.rhs[k].clone())?;
        if (0..k).any(|j| binder_ty.mentions(j)) {
            let env_right: Vec<Value> = top.base.iter().chain(&top.rhs[..k]).cloned().collect();
            let ty_right = eval(g, &env_right, binder_ty)?;
            if !conv(g, level, &ty, &ty_right)? {
                let constraint = Constraint { ty, lhs, rhs };
                return Ok(Outcome::Stuck(constraint, Reason::TypesDiffer { ty_right }));
            }
        }
        // Deletion.
        if conv(g, level, &lhs, &rhs)? {
            stack.last_mut().expect("an entry").solved += 1;
            continue;
        }
        // Solution.
        let solution = match (scope.flexible(&lhs), scope.flexible(&rhs)) {
            (Some(a), Some(b)) => {
                let (later, earlier) = if a > b { (a, b) } else { (b, a) };
                if !occurs(g, scope, later, &Value::var(earlier))? {
                    Some(Ok((later, Value::var(earlier))))
                } else if !occurs(g, scope, earlier, &Value::var(later))? {
                    Some(Ok((earlier, Value::var(later))))
                } else {
                    Some(Err(()))
                }
            }
            (Some(y), None) => Some(if occurs(g, scope, y, &rhs)? {
                Err(())
            } else {
                Ok((y, rhs.clone()))
            }),
            (None, Some(y)) => Some(if occurs(g, scope, y, &lhs)? {
                Err(())
            } else {
                Ok((y, lhs.clone()))
            }),
            (None, None) => None,
        };
        match solution {
            Some(Ok((y, t))) => {
                stack.last_mut().expect("an entry").solved += 1;
                solve(g, scope, &mut stack, y, &t)?;
                solutions.push((y, t));
                continue;
            }
            Some(Err(())) => {
                return Ok(Outcome::Stuck(Constraint { ty, lhs, rhs }, Reason::Occurs));
            }
            None => {}
        }
        // Injectivity and conflict: only at a data type in `Type`.
        let stuck = |reason| {
            Ok(Outcome::Stuck(
                Constraint {
                    ty: ty.clone(),
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                },
                reason,
            ))
        };
        if is_type_former(&lhs) || is_type_former(&rhs) {
            return stuck(Reason::TypeFormer);
        }
        let (d, type_args) = match &ty {
            Value::Data(d, args) => (*d, args),
            Value::Eq(..) => return stuck(Reason::Proof),
            _ => return stuck(Reason::NotConstructor),
        };
        let data = g.data(d);
        if data.sort == Sort::Prop {
            return stuck(Reason::Proof);
        }
        let (Some((cl, fields_l)), Some((cr, fields_r))) =
            (constructor(g, d, &lhs), constructor(g, d, &rhs))
        else {
            return stuck(Reason::NotConstructor);
        };
        if cl != cr {
            return Ok(Outcome::Conflict(Constraint { ty, lhs, rhs }));
        }
        let params = type_args[..data.params.len()].to_vec();
        stack.last_mut().expect("an entry").solved += 1;
        stack.push(Entry {
            binders: &data.ctors[cl].fields,
            base: params,
            lhs: fields_l,
            rhs: fields_r,
            solved: 0,
        });
    }
}

fn is_type_former(value: &Value) -> bool {
    matches!(value, Value::Data(..) | Value::Pi(..) | Value::Sort(_))
}

/// `value` as a constructor of data type `d` and its fields, if it is one:
/// a constructor value, a number (for `Nat`) or a compact list, one cell.
fn constructor(g: &Globals, d: crate::term::DataId, value: &Value) -> Option<(usize, Vec<Value>)> {
    match value {
        Value::Ctor(d2, c, fields) if *d2 == d => Some((*c, fields.to_vec())),
        Value::Nat(_) | Value::NatAdd(..) if Some(d) == g.builtins.nat => {
            native::split_value(value)
        }
        Value::Chars(_) => match expand_step(g, value.clone()) {
            Value::Ctor(d2, c, fields) if d2 == d => Some((c, fields.to_vec())),
            _ => None,
        },
        _ => None,
    }
}

/// Whether variable `y` occurs in `t`, or in the type of a variable of `t`,
/// or, transitively, in the types of the variables those types mention.
pub fn occurs(g: &Globals, scope: &Scope, y: usize, t: &Value) -> Result<bool> {
    let level = scope.level();
    let mut seen = vec![false; level];
    let mut todo = free_levels(&quote(g, level, t)?, level);
    while let Some(v) = todo.pop() {
        if v == y {
            return Ok(true);
        }
        if v >= level || std::mem::replace(&mut seen[v], true) {
            continue;
        }
        todo.extend(free_levels(&quote(g, level, &scope.types[v])?, level));
    }
    Ok(false)
}

/// The levels of the free variables of `term`, with `level` variables in
/// scope.
fn free_levels(term: &Term, level: usize) -> Vec<usize> {
    term.subterms()
        .filter_map(|(t, binders)| match t {
            Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
                let ix = ix.checked_sub(binders)?;
                level.checked_sub(ix + 1)
            }
            _ => None,
        })
        .collect()
}

/// Substitutes `t` for variable `y` everywhere: the context, the extra
/// values and the stack.
fn solve(g: &Globals, scope: &mut Scope, stack: &mut [Entry], y: usize, t: &Value) -> Result<()> {
    let level = scope.level();
    let sub = |values: &[Value]| substitute(g, level, y, t, values);
    let mut env = sub(&scope.env)?;
    env[y] = t.clone();
    scope.env = env;
    scope.types = sub(&scope.types)?;
    scope.extra = sub(&scope.extra)?;
    for entry in stack {
        entry.base = sub(&entry.base)?;
        entry.lhs = sub(&entry.lhs)?;
        entry.rhs = sub(&entry.rhs)?;
    }
    Ok(())
}
