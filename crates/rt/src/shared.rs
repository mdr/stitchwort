//! What the machine and native code's runtime share, outside the machine's
//! module (stage NO6 of docs/proposals/native-only.md): the limits, a
//! number switch's table, the arity of a function value, and the depth
//! note. An executable built with `--native` links these and none of
//! [`crate::machine`], [`crate::code`] or [`crate::codec`].

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::Limits as CoreLimits;

use crate::ir::Program;
use crate::value::{Fun, Value};

/// How much a run may use.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    /// Frames entered (calls) between two operations or ticks.
    pub steps: u64,
    /// Frames pending at once: how deeply a program may recurse.
    pub frames: usize,
}

impl Limits {
    /// The reference evaluator's limits: its work limit as steps, and its
    /// frame limit.
    pub fn from_core(limits: CoreLimits) -> Limits {
        Limits {
            steps: limits.work,
            frames: limits.frames,
        }
    }
}

impl Default for Limits {
    fn default() -> Limits {
        Limits::from_core(CoreLimits::default())
    }
}

/// A number switch's targets (the machine's `NumSwitch`, and native code's
/// through `Tables::num_tables`).
#[derive(Debug)]
pub struct NumTable {
    pub small: Vec<(u64, u32)>,
    pub big: Vec<(BigUint, u32)>,
    pub default: u32,
}

/// How many arguments a program's globals and lambdas take: the program's
/// own ([`Program`]), or its outline in an executable built with `--native`
/// (`crate::linked::Outline`).
pub(crate) trait Arities {
    /// How many runtime arguments a call of global `g` passes.
    fn global_params(&self, g: u32) -> u32;
    /// How many arguments lambda `lambda` takes.
    fn lambda_params(&self, lambda: u32) -> u32;
}

impl Arities for Program {
    #[inline]
    fn global_params(&self, g: u32) -> u32 {
        self.globals[g as usize].kind.params()
    }

    #[inline]
    fn lambda_params(&self, lambda: u32) -> u32 {
        self.lambdas[lambda as usize].params
    }
}

/// The arity of a function value that isn't a partial application.
pub(crate) fn arity(program: &impl Arities, head: &Value) -> usize {
    let Value::Fun(fun) = head else {
        unreachable!("a function")
    };
    match &**fun {
        Fun::Global(g) => program.global_params(*g) as usize,
        Fun::Closure { lambda, .. } => program.lambda_params(*lambda) as usize,
        Fun::DoneK | Fun::Resume(..) | Fun::StateRun(_) | Fun::StateK(_) | Fun::DelayK(_) => 1,
        Fun::JumpK => 2,
        Fun::Jumped(..) => panic!("internal error: a jump applied"),
        Fun::Pap { .. } => unreachable!("a partial application's head"),
    }
}

/// The bodies with the most of `codes` (the pending frames' bodies, one
/// each): the three with the most, and how many each has, most first.
/// Shared with native code's executor, which counts the frames that left
/// with the error (stage NO5 of docs/proposals/native-only.md).
pub(crate) fn deepest(codes: impl IntoIterator<Item = u32>) -> Vec<(u32, usize)> {
    let mut counts: stitchwort_core::collections::HashMap<u32, usize> = Default::default();
    for code in codes {
        *counts.entry(code).or_insert(0) += 1;
    }
    let mut counts: Vec<(u32, usize)> = counts.into_iter().collect();
    counts.sort_by_key(|&(code, count)| (std::cmp::Reverse(count), code));
    counts.truncate(3);
    counts
}

/// What the depth note calls body `code`: the global whose body it is
/// (`global_code`, by global, and `name`), the entry (`entry_code`), or an
/// anonymous function.
pub(crate) fn body_name<'a>(
    global_code: &[Option<u32>],
    entry_code: u32,
    name: impl Fn(usize) -> &'a Rc<str>,
    code: u32,
) -> String {
    if let Some(g) = global_code.iter().position(|c| *c == Some(code)) {
        return format!("`{}`", name(g));
    }
    if code == entry_code {
        return "the program's entry".to_string();
    }
    "an anonymous function".to_string()
}

/// The depth note for `deepest` ([`deepest`]), naming each body with
/// `name` ([`body_name`]): `Machine::depth_report`, and native code's.
pub(crate) fn depth_report(
    deepest: &[(u32, usize)],
    name: impl Fn(u32) -> String,
) -> Option<String> {
    let &(_, most) = deepest.first()?;
    let parts: Vec<String> = deepest
        .iter()
        // Only the ones with a real share (the entry has one frame).
        .filter(|&&(_, count)| count * 10 >= most)
        .map(|&(code, count)| format!("{} ({count} frames pending)", name(code)))
        .collect();
    Some(parts.join(", "))
}
