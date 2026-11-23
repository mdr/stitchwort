//! Which variables' types a generalised `match` can leave unread (SW-4635).
//!
//! The occurrence test reads every variable's type back unfolded and looks
//! for each scrutinee's normal form in it. A hypothesis such as `inner:
//! FullHungBelow depth`, along for the ride, unfolds to tens of thousands
//! of nodes, read back again at every `match` in its scope. Its type can be
//! seen not to hold the scrutinee without reading it back, from which
//! variables it mentions.
//!
//! The argument. A value's read-back unfolded mentions no variable that
//! the value itself doesn't: a call's unfolding is its closed definition
//! applied to its arguments, a closure's body sees only its environment and
//! its own binder, and an unknown's solution is closed (`x1 … xn => rhs`,
//! applied to its spine). So [`mentioned`], a walk over the value as it is,
//! never forcing a call, finds every variable its normal form can mention.
//! On the other side, [`rigid`] finds variables the scrutinee's normal form
//! certainly mentions: the head of a stuck application, or such a variable
//! in an argument of a definition that doesn't unfold. If the scrutinee is
//! certain to mention `r` and a type can't mention it, the scrutinee
//! doesn't occur in that type, read back unfolded or folded: a subterm
//! equal to it by computation would compute to a term mentioning `r` too.
//! Proofs are skipped by comparison, so `r` is never taken from a position
//! where a proof is ignored (a definition's inert parameter, a
//! constructor's field).
//!
//! A variable is copied when its type holds a scrutinee or mentions a
//! copied variable, so one left unread must also mention no variable that
//! is read: the levels left unread are the greatest set closed under that.
//! Such a variable is never copied, by the usual test or as written, so the
//! `match` comes out exactly as it did when every type was read.

use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::value::{Elim, Head, force};
use stitchwort_core::{Term, Value};

use super::Scrut;
use crate::check::{Ctx, Result};

/// Nodes [`mentioned`] visits in one type before giving up, which leaves
/// that type to be read. Far below the read-backs it saves (SW-4631:
/// 61.6K and 273K nodes), and enough for the types that are calls, as most
/// large hypotheses are.
const SCAN_NODES: usize = 4096;

/// Evaluation steps [`rigid`] may take forcing a scrutinee: forcing runs
/// what it computes, which the occurrence test may not need to run at all
/// (SW-1096). Past this, nothing is left unread.
const FORCE_STEPS: u64 = 20_000;

/// How deep [`rigid`] looks into arguments for a variable.
const RIGID_DEPTH: usize = 4;

/// For each level below `base`, whether the generalisation of a `match` on
/// `exprs` needn't read that variable's type (the module's argument).
/// All `false` where some scrutinee is certain to mention no variable.
pub(super) fn levels(cx: &Ctx, exprs: &[Scrut], base: usize) -> Result<Vec<bool>> {
    let none = vec![false; base];
    let g = cx.g();
    let mut certain: Vec<HashSet<usize>> = Vec::with_capacity(exprs.len());
    for s in exprs {
        let value = cx.eval(&s.term)?;
        let mut found = HashSet::default();
        let mut remaining = FORCE_STEPS;
        let done = g.machine.budget.limited(&mut remaining, || {
            rigid(cx, value, base, RIGID_DEPTH, &mut found)
        });
        match done {
            Ok(Some(())) if !found.is_empty() => certain.push(found),
            Ok(_) => return Ok(none),
            Err(e) if crate::undo::recoverable(cx, &e) => {
                crate::undo::recovered(cx);
                return Ok(none);
            }
            Err(e) => return Err(e),
        }
    }
    if certain.is_empty() {
        return Ok(none);
    }
    // Each type's variables, or `None` where the walk gave up.
    let mentions: Vec<Option<HashSet<usize>>> =
        (0..base).map(|l| mentioned(&cx.types[l])).collect();
    let mut unread: Vec<bool> = mentions
        .iter()
        .map(|m| {
            m.as_ref()
                .is_some_and(|m| certain.iter().all(|c| c.iter().any(|r| !m.contains(r))))
        })
        .collect();
    loop {
        let mut changed = false;
        for l in 0..base {
            if unread[l]
                && let Some(m) = &mentions[l]
                && m.iter().any(|&v| v >= base || !unread[v])
            {
                unread[l] = false;
                changed = true;
            }
        }
        if !changed {
            return Ok(unread);
        }
    }
}

/// Adds to `found` variables below `base` that `value`'s normal form
/// certainly mentions, looking `depth` arguments deep.
fn rigid(
    cx: &Ctx,
    value: Value,
    base: usize,
    depth: usize,
    found: &mut HashSet<usize>,
) -> Result<()> {
    let g = cx.g();
    let value = force(&g, value)?;
    if let Value::Neutral(Head::Def(id), spine) = &value
        && depth > 0
        && stitchwort_core::value::is_call_field(spine)
        && stitchwort_core::value::is_folded(&g, &value)
    {
        // A stuck field of a call, `(f x).i`, reads back as the call
        // unfolded, then the field: so look at the call.
        let arity = g.def(*id).arity();
        let call: stitchwort_core::value::Spine = spine[..arity].iter().cloned().collect();
        return rigid(
            cx,
            Value::Call(*id, call, Default::default()),
            base,
            depth - 1,
            found,
        );
    }
    let Value::Neutral(head, spine) = value else {
        return Ok(());
    };
    match head {
        Head::Var(l, _, _) if l < base => {
            found.insert(l);
        }
        // A definition that doesn't unfold is read back as itself applied
        // to its arguments.
        Head::Def(id) if depth > 0 => {
            let def = g.env.defs().get(id.0);
            for (i, elim) in (&spine).into_iter().enumerate() {
                match elim {
                    // Comparison skips an argument at an inert position (a
                    // proof the body never computes with).
                    Elim::App(arg, _) if def.is_some_and(|d| !d.is_inert(i)) => {
                        rigid(cx, arg.clone(), base, depth - 1, found)?;
                    }
                    Elim::App(..) | Elim::Proj(..) => {}
                    // Inert marks count up to the first `J` only.
                    Elim::J { .. } => break,
                }
            }
        }
        _ => {}
    }
    Ok(())
}

/// Every variable `value` mentions, as it is (calls not unfolded), or
/// `None` past [`SCAN_NODES`] nodes or at a value the checker never holds.
fn mentioned(value: &Value) -> Option<HashSet<usize>> {
    let mut scan = Scan::new(SCAN_NODES);
    scan.value(value).then_some(scan.found)
}

/// Every variable `value` can mention read back unfolded, as [`mentioned`]
/// finds them, and whether it may hold an unknown (solved or not), or
/// `None` past [`SCAN_NODES`] nodes: for the goal's read-back that keeps
/// calls folded where a scrutinee can't be hidden (`super::mixed_goal`).
pub(super) fn mentions(value: &Value) -> Option<(HashSet<usize>, bool)> {
    let mut scan = Scan::new(SCAN_NODES);
    scan.value(value).then_some((scan.found, scan.unknown))
}

/// Nodes [`holds_unknown`] visits before saying "perhaps".
const UNKNOWN_SCAN_NODES: usize = 1 << 16;

/// Whether `value` may hold an unknown, solved or not: a head, or one in a
/// closure's body. `false` only where it certainly holds none, so that
/// reading it back and evaluating it again would give the same value; a
/// call's unfolding is its closed definition applied to its arguments, so
/// it is not looked at. `true` past [`UNKNOWN_SCAN_NODES`] nodes.
pub(crate) fn holds_unknown(value: &Value) -> bool {
    let mut scan = Scan::new(UNKNOWN_SCAN_NODES);
    !scan.value(value) || scan.unknown
}

struct Scan {
    found: HashSet<usize>,
    /// Whether an unknown was met.
    unknown: bool,
    /// Values already walked, by address: closures' environments share the
    /// context's values. Nothing is freed during a walk.
    seen: HashSet<*const Value>,
    /// Each closure body's free indices, outside its own binder.
    bodies: HashMap<*const Term, Vec<usize>>,
    nodes: usize,
}

impl Scan {
    fn new(nodes: usize) -> Scan {
        Scan {
            found: HashSet::default(),
            unknown: false,
            seen: HashSet::default(),
            bodies: HashMap::default(),
            nodes,
        }
    }

    fn value(&mut self, value: &Value) -> bool {
        if !self.seen.insert(value as *const Value) {
            return true;
        }
        let Some(nodes) = self.nodes.checked_sub(1) else {
            return false;
        };
        self.nodes = nodes;
        match value {
            Value::Sort(_) | Value::Nat(_) | Value::Chars(_) | Value::Refl => true,
            Value::Pi(_, _, domain, body, _) => self.value(domain) && self.closure(body),
            Value::Lam(_, _, body, _) => self.closure(body),
            Value::Data(_, args) => args.iter().all(|a| self.value(a)),
            Value::Ctor(_, _, fields) => fields.iter().all(|f| self.value(f)),
            Value::NatAdd(_, x) => self.value(x),
            Value::Eq(ty, a, b) => self.value(ty) && self.value(a) && self.value(b),
            Value::Neutral(head, spine) => {
                match head {
                    Head::Var(l, _, _) => {
                        self.found.insert(*l);
                    }
                    Head::Meta(_) => self.unknown = true,
                    Head::Def(_) | Head::Quot(_, _) => {}
                }
                self.spine(spine)
            }
            // The unfolding is the closed definition applied to the spine.
            Value::Call(_, spine, _) => self.spine(spine),
            Value::Resumption(_) => false,
        }
    }

    fn spine(&mut self, spine: &stitchwort_core::value::Spine) -> bool {
        spine.into_iter().all(|elim| match elim {
            Elim::App(arg, _) => self.value(arg),
            Elim::J { motive, base, .. } => self.value(motive) && self.value(base),
            Elim::Proj(..) => true,
        })
    }

    /// A closure's environment, as far as its body (under one binder) uses it.
    fn closure(&mut self, closure: &stitchwort_core::value::Closure) -> bool {
        let key = std::rc::Rc::as_ptr(&closure.body);
        if !self.bodies.contains_key(&key) {
            let mut free = Vec::new();
            for (t, under) in closure.body.subterms() {
                let Some(nodes) = self.nodes.checked_sub(1) else {
                    return false;
                };
                self.nodes = nodes;
                match t {
                    Term::Var(ix) if *ix > under => free.push(ix - under - 1),
                    Term::Meta(_) => self.unknown = true,
                    _ => {}
                }
            }
            free.sort_unstable();
            free.dedup();
            self.bodies.insert(key, free);
        }
        let env = &closure.env;
        let free = self.bodies[&key].clone();
        free.into_iter()
            .all(|ix| match env.len().checked_sub(1 + ix) {
                Some(at) => self.value(&env[at]),
                None => false,
            })
    }
}
