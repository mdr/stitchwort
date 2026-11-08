//! Reuse across calls (docs/proposals/reuse-across-calls.md): a cell taken
//! apart in one function, rebuilt in place by another.
//!
//! The bytecode compiler reuses a cell where the body that takes it apart
//! builds a constructor with as many fields ([`crate::code`], "Moves and
//! reuse"). Often the body instead calls a function that builds it, perhaps
//! a few calls down (`Map.Tree.insertWith` takes a node apart and calls
//! `balance`, which calls `rebuild`, which builds the node). For such a
//! function this pass makes a *copy* with one more parameter, last: a reuse
//! token, the emptied cell. Wherever the compiler holds a token of that size
//! at a call of the function, it calls the copy and passes the token; the
//! copy's code starts with the token in hand, as if it had taken the cell
//! apart itself, and passes it on or fills it.
//!
//! - **Which functions.** A function *wants* tokens of `n` fields if it
//!   builds a constructor of `n` fields, or calls a function that wants
//!   them, at most [`DEPTH`] calls down (lambdas apart: only direct calls).
//! - **Which copies.** Only those some call would be given a token for: the
//!   compiler itself is run over every body in a planning mode, which says
//!   at which calls it would pass a token to a function that wants one
//!   ([`crate::code::plan`]); each such function and size gets a copy, whose
//!   body is planned in turn, until no new one comes up. At most one copy is
//!   made per function and size, so a copy that calls itself calls the copy.
//!   The copies are capped: [`MAX_COPIES`], and [`MAX_GROWTH`] of the
//!   program's size in IR nodes (at least [`MIN_GROWTH`]).
//! - **Not copied:** constants, natives, TRMC's loops (a body that uses a
//!   hole operation: the twins, their helpers' copies and the wrappers,
//!   [`crate::trmc`]), and bodies nested too deeply for the passes.
//! - **A copy's body** is the original's with the slots from `params` on
//!   moved up by one ([`crate::trmc::shift`]), so the token's slot,
//!   `params`, is one the IR never reads or binds. Nothing in the IR names a
//!   copy: only the bytecode's calls do. [`Program::validate`] checks both,
//!   so a copy is never a function value and its token is never a value the
//!   program passed.
//!
//! **Soundness.** No new way for a cell in use to be overwritten:
//!
//! 1. A token is still made only by `Unpack` and `DropReuse`, and holds a
//!    cell only if its count was 1, with its fields moved out; otherwise it
//!    holds `Erased`.
//! 2. It lives in a register the IR never reads (a temporary, or a copy's
//!    last parameter, by the checks above), and is only moved: into one
//!    `CtorReuse`, or as the last operand of one call of a copy, marked as a
//!    move ([`crate::code::MOVE`]); or dropped with its frame. So nothing
//!    else ever refers to the cell, and it's never a closure's capture or a
//!    resumption's.
//! 3. `CtorReuse` checks again at run time that the token is a cell of the
//!    right size with a count of 1, and otherwise builds a new cell. A
//!    mistake in which calls are given tokens (a copy that never builds, a
//!    token of the wrong size) costs an allocation, not an answer.
//! 4. Steps and frames don't change: a call of a copy enters one frame where
//!    the call of the original did, and the pass runs after every inlining
//!    decision. A token not used is freed when its frame ends, so at most
//!    one is held per parameter and frame.

use stitchwort_core::collections::HashMap;

use crate::ir::{Body, Expr, Global, GlobalId, GlobalKind, PrimOp, Program, Reuse};
use crate::opt::{MAX_NESTING, nesting, size};
use crate::trmc::{each, shift};

/// How many calls down a token is passed before something builds in it.
/// `Map.Tree` needs 2 (`balance` is inlined): `insertWith`'s lifted match
/// calls `rebuild`, which calls the rotation that builds.
pub const DEPTH: usize = 4;
/// The most copies made for a program.
pub const MAX_COPIES: usize = 256;
/// The most the copies may add to the program's IR nodes, in percent, or
/// [`MIN_GROWTH`] nodes if that's more: a small program using `Map` is
/// mostly `Map`.
pub const MAX_GROWTH: usize = 25;
pub const MIN_GROWTH: usize = 2_000;

/// What [`apply`] made.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// The copies made.
    pub copies: usize,
    /// The program's IR nodes before, and those the copies added.
    pub nodes: usize,
    pub added: usize,
    /// Whether a copy wanted was left out by a cap.
    pub capped: bool,
}

/// Makes the copies of `program`'s functions that take a reuse token.
pub fn apply(program: &mut Program) -> Stats {
    let count = program.globals.len();
    let eligible: Vec<bool> = program.globals.iter().map(eligible).collect();
    let wants = wants(program, &eligible);
    let wanted = |g: GlobalId, n: usize| {
        let g = g.0 as usize;
        g < count && eligible[g] && wants[g].binary_search(&n).is_ok()
    };
    let nodes = program_size(program);
    let budget = (nodes * MAX_GROWTH / 100).max(MIN_GROWTH);
    let mut stats = Stats {
        nodes,
        ..Stats::default()
    };

    let mut queue: Vec<(GlobalId, usize)> = Vec::new();
    let mut seen: HashMap<(GlobalId, usize), ()> = HashMap::default();
    let mut push = |queue: &mut Vec<(GlobalId, usize)>, pairs: Vec<(GlobalId, usize)>| {
        for pair in pairs {
            if seen.insert(pair, ()).is_none() {
                queue.push(pair);
            }
        }
    };
    for global in &program.globals {
        let planned = match &global.kind {
            GlobalKind::Function { params, body } => {
                crate::code::plan(program, *params, body, None, &wanted)
            }
            GlobalKind::Constant { body } => crate::code::plan(program, 0, body, None, &wanted),
            GlobalKind::Native(_) => continue,
        };
        push(&mut queue, planned);
    }
    for lambda in &program.lambdas {
        let planned = crate::code::plan(program, lambda.params, &lambda.body, None, &wanted);
        push(&mut queue, planned);
    }
    let planned = crate::code::plan(program, 0, &program.entry, None, &wanted);
    push(&mut queue, planned);

    // Breadth first, so that a cap leaves out the copies furthest from
    // the calls that are given tokens to begin with.
    let mut made: Vec<(GlobalId, usize)> = Vec::new();
    let mut at = 0;
    while at < queue.len() {
        let (g, n) = queue[at];
        at += 1;
        let GlobalKind::Function { params, body } = &program.globals[g.0 as usize].kind else {
            continue;
        };
        let nodes = size(&body.expr);
        if made.len() >= MAX_COPIES || stats.added + nodes > budget {
            stats.capped = true;
            continue;
        }
        stats.added += nodes;
        made.push((g, n));
        let planned = crate::code::plan(program, *params, body, Some(n), &wanted);
        push(&mut queue, planned);
    }
    stats.copies = made.len();

    let mut copies: Vec<Vec<(u32, GlobalId)>> = vec![Vec::new(); count];
    for (i, &(g, n)) in made.iter().enumerate() {
        let id = GlobalId(u32::try_from(count + i).expect("globals fit"));
        copies[g.0 as usize].push((u32::try_from(n).expect("sizes fit"), id));
    }
    let mut added = Vec::with_capacity(made.len());
    for &(g, n) in &made {
        let global = &program.globals[g.0 as usize];
        let GlobalKind::Function { params, body } = &global.kind else {
            unreachable!("only functions are copied");
        };
        // A function with copies of several sizes names each by its size.
        let name = if copies[g.0 as usize].len() == 1 {
            format!("{}[reuse]", global.name)
        } else {
            format!("{}[reuse{n}]", global.name)
        };
        added.push(Global {
            name: name.into(),
            def: global.def,
            kind: GlobalKind::Function {
                params: params + 1,
                body: Body {
                    frame: body.frame + 1,
                    expr: shift(&body.expr, *params, 1),
                },
            },
            reuse: Reuse::Copy {
                of: g,
                size: u32::try_from(n).expect("sizes fit"),
            },
        });
    }
    for (global, mut list) in program.globals.iter_mut().zip(copies) {
        if !list.is_empty() {
            list.sort_unstable();
            global.reuse = Reuse::Copies(list);
        }
    }
    program.globals.append(&mut added);
    stats
}

/// Whether a copy of `global` may be made.
fn eligible(global: &Global) -> bool {
    let GlobalKind::Function { body, .. } = &global.kind else {
        return false;
    };
    if global.reuse != Reuse::None || nesting(&body.expr) > MAX_NESTING {
        return false;
    }
    let mut loop_ = false;
    each(&body.expr, &mut |e| {
        loop_ |= matches!(e, Expr::Prim(PrimOp::Hole(_), _));
    });
    !loop_
}

/// The sizes of the tokens each global wants, in increasing order: those of
/// the constructors it builds, and those its callees want, at most
/// [`DEPTH`] calls down.
fn wants(program: &Program, eligible: &[bool]) -> Vec<Vec<usize>> {
    let count = program.globals.len();
    // Each global's constructor sizes, and the globals it calls.
    let mut builds: Vec<Vec<usize>> = vec![Vec::new(); count];
    let mut calls: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (g, global) in program.globals.iter().enumerate() {
        if !eligible[g] {
            continue;
        }
        let GlobalKind::Function { body, .. } = &global.kind else {
            continue;
        };
        each(&body.expr, &mut |e| match e {
            Expr::Ctor(_, _, fields) if !fields.is_empty() => builds[g].push(fields.len()),
            Expr::Call(h, _) if eligible.get(h.0 as usize).copied().unwrap_or(false) => {
                calls[g].push(h.0 as usize);
            }
            _ => {}
        });
        builds[g].sort_unstable();
        builds[g].dedup();
        calls[g].sort_unstable();
        calls[g].dedup();
    }
    // Round `d` adds what is wanted `d` calls down.
    let mut wants = builds;
    for _ in 0..DEPTH {
        let before = wants.clone();
        for g in 0..count {
            for &h in &calls[g] {
                wants[g].extend_from_slice(&before[h]);
            }
            wants[g].sort_unstable();
            wants[g].dedup();
        }
        if wants == before {
            break;
        }
    }
    wants
}

/// The program's IR nodes: its globals', lambdas' and entry's.
fn program_size(program: &Program) -> usize {
    let globals: usize = program
        .globals
        .iter()
        .map(|global| match &global.kind {
            GlobalKind::Function { body, .. } | GlobalKind::Constant { body } => size(&body.expr),
            GlobalKind::Native(_) => 0,
        })
        .sum();
    let lambdas: usize = program.lambdas.iter().map(|l| size(&l.body.expr)).sum();
    globals + lambdas + size(&program.entry.expr)
}
