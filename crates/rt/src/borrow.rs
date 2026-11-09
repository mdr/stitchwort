//! Borrow inference as a dry run (SW-2530, stage B0 of
//! docs/proposals/borrow-inference.md): which parameters of each function
//! could be borrowed, and, with the cargo feature `borrow-counts`, how many
//! reference-count operations a run would save if they were. Nothing here
//! changes what code is generated or how a program runs.
//!
//! The inference reads the compiled bytecode ([`Code`]) rather than the
//! erased IR. The bytecode already holds the decisions the note's rule O5
//! asks the inference to predict (an [`Instr::Unpack`] with a token, or an
//! [`Instr::DropReuse`], is a cell that will be reused, so its owner must
//! keep it), and it shows each operand's last use ([`MOVE`]). It is
//! forward-only (loops are tail calls), so one pass in order, merging at
//! jump targets, is a complete dataflow.
//!
//! A *lent* register holds a value without owning a reference: a borrowed
//! parameter, or a field read from a lent register. The rules (the note's
//! O1-O8) say when a parameter must stay owned:
//!
//! - O1 stored: a lent parameter itself goes into a constructor, closure,
//!   partial application, function-value call, effect native or consuming
//!   native;
//! - O2 returned;
//! - O3 passed to an owned parameter of a direct call;
//! - O4 an owned value is tail-passed to a borrowed parameter of a function
//!   in the same strongly connected group (the caller would have to drop it
//!   after the call, ending the tail call): the callee's parameter is owned;
//! - O5 reused: the cell is unpacked with a token, or dropped as one;
//! - O6 a field of a lent value is passed to an owned parameter (the
//!   projection rule): the value is owned. A field merely stored or
//!   returned is incremented there and doesn't force it;
//! - O7 (stage B1 only) the function is used as a value anywhere;
//! - O8 (stage B1 only) an owned value is tail-passed to a borrowed
//!   parameter of a function in another group.
//!
//! [`Variant::B2`] drops O7 and O8, as owned copies of the function would.
//! Groups are solved callees first, each to a fixpoint; since flags only
//! move towards owned, an outer loop repeats until the O4 and O8 marks on
//! earlier groups settle.

use stitchwort_core::collections::HashMap;

use crate::code::{Code, Instr, MOVE, NO_REG, Ops, Reg};
use crate::ir::{HoleOp, PrimOp};

/// Which rules.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Variant {
    /// Stage B2: owned copies serve functions used as values and owned
    /// tail arguments from other groups, so O7 and O8 don't apply. (Stage
    /// B1 has them.)
    pub b2: bool,
    /// Without O6: a field of a lent value passed to an owned parameter is
    /// incremented there, like a field stored in a constructor, instead of
    /// making its parent owned.
    pub relax_o6: bool,
}

impl Variant {
    pub const B1: Variant = Variant {
        b2: false,
        relax_o6: false,
    };
    pub const B2: Variant = Variant {
        b2: true,
        relax_o6: false,
    };

    pub fn name(self) -> String {
        format!(
            "{}{}",
            if self.b2 { "b2" } else { "b1" },
            if self.relax_o6 { "-no-o6" } else { "" }
        )
    }

    /// Parses `b1`, `b2`, `b1-no-o6`, `b2-no-o6`.
    pub fn parse(text: &str) -> Option<Variant> {
        let (stage, rest) = match text.split_once('-') {
            Some((a, b)) => (a, Some(b)),
            None => (text, None),
        };
        let relax_o6 = match rest {
            None => false,
            Some("no-o6") => true,
            Some(_) => return None,
        };
        match stage {
            "b1" => Some(Variant {
                b2: false,
                relax_o6,
            }),
            "b2" => Some(Variant { b2: true, relax_o6 }),
            _ => None,
        }
    }
}

/// Why a parameter is owned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    Stored,
    Returned,
    PassedOwned,
    TailOwned,
    Reused,
    FieldEscapes,
    ValueUse,
    TailAcross,
    /// Never borrowed: a reuse copy's token, or a loop with hole operations.
    Fixed,
}

impl Reason {
    pub const ALL: [Reason; 9] = [
        Reason::Stored,
        Reason::Returned,
        Reason::PassedOwned,
        Reason::TailOwned,
        Reason::Reused,
        Reason::FieldEscapes,
        Reason::ValueUse,
        Reason::TailAcross,
        Reason::Fixed,
    ];

    /// The note's rule name.
    pub fn name(self) -> &'static str {
        match self {
            Reason::Stored => "O1 stored",
            Reason::Returned => "O2 returned",
            Reason::PassedOwned => "O3 passed to an owned parameter",
            Reason::TailOwned => "O4 owned tail argument, same group",
            Reason::Reused => "O5 reused",
            Reason::FieldEscapes => "O6 field passed to an owned parameter",
            Reason::ValueUse => "O7 used as a value",
            Reason::TailAcross => "O8 owned tail argument, other group",
            Reason::Fixed => "fixed owned (token, hole loop)",
        }
    }
}

/// Which parameters of a function are never borrowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fixed {
    No,
    /// A reuse copy: the last parameter is its token.
    Last,
}

/// A function the inference looks at.
pub struct Func<'a> {
    pub code: &'a Code,
    pub fixed: Fixed,
    /// Named by a `Global` or `Pap` instruction anywhere: used as a value.
    pub value_used: bool,
    /// Per constant-pool entry, whether it holds no reference (a number, a
    /// tag): a register loaded from it needs no drop, so tail-passing it
    /// is free to a borrowed parameter. (The IR knows the same from the
    /// literal or the nullary constructor.)
    pub plain_consts: &'a [bool],
}

/// What was inferred, by global index.
pub struct Inference {
    /// Per function, per parameter: borrowed. Empty for a non-function.
    pub borrowed: Vec<Vec<bool>>,
    /// Per function, per parameter: why it is owned, if it is.
    pub reason: Vec<Vec<Option<Reason>>>,
    /// The strongly connected group of each function.
    pub group: Vec<u32>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Org {
    Own,
    /// Owned, but holding no reference (loaded from a plain constant).
    Plain,
    Lent {
        root: u32,
        direct: bool,
    },
}

enum Mark {
    /// A parameter of the function scanned.
    Own(usize, Reason),
    /// Parameter `.1` of function `.0`.
    Callee(usize, usize, Reason),
}

fn has_holes(code: &Code) -> bool {
    code.instrs.iter().any(|i| {
        matches!(
            i,
            Instr::Prim {
                op: PrimOp::Hole(HoleOp::New | HoleOp::Fill | HoleOp::Take),
                ..
            }
        )
    })
}

/// The jump targets of an instruction, and whether control also falls
/// through to the next one.
fn successors(code: &Code, instr: &Instr, out: &mut Vec<u32>) -> bool {
    match instr {
        Instr::Return { .. }
        | Instr::TailCall { .. }
        | Instr::TailApply { .. }
        | Instr::TailPrim { .. }
        | Instr::Unreachable => false,
        Instr::Jump { target } => {
            out.push(*target);
            false
        }
        Instr::JumpIfFalse { target, .. } | Instr::Test { target, .. } => {
            out.push(*target);
            true
        }
        Instr::NatCase { zero, .. } => {
            out.push(*zero);
            true
        }
        Instr::IntCase { neg, .. } => {
            out.push(*neg);
            true
        }
        Instr::Switch { table, .. } => {
            out.extend(code.tables[*table as usize].iter().copied());
            false
        }
        Instr::NumSwitch { table, .. } => {
            let t = &code.num_tables[*table as usize];
            out.extend(t.small.iter().map(|(_, p)| *p));
            out.extend(t.big.iter().map(|(_, p)| *p));
            out.push(t.default);
            false
        }
        _ => true,
    }
}

/// Using `r` where a reference is kept or handed to an owner: a lent
/// parameter itself must then be owned (`direct`); a field of one only when
/// `field` says so. Reading it with [`MOVE`] takes it out of the register.
fn escape(marks: &mut Vec<Mark>, s: &mut [Org], r: Reg, direct: Reason, field: Option<Reason>) {
    match s[(r & !MOVE) as usize] {
        Org::Lent { root, direct: true } => marks.push(Mark::Own(root as usize, direct)),
        Org::Lent {
            root,
            direct: false,
        } => {
            if let Some(reason) = field {
                marks.push(Mark::Own(root as usize, reason));
            }
        }
        Org::Own | Org::Plain => {}
    }
    if r & MOVE != 0 {
        s[(r & !MOVE) as usize] = Org::Own;
    }
}

/// The operands of a call of `g`: each goes to a borrowed or an owned
/// parameter of the callee.
#[allow(clippy::too_many_arguments)]
fn call_args(
    me: usize,
    code: &Code,
    g: u32,
    args: Ops,
    tail: bool,
    s: &mut [Org],
    flags: &[Vec<bool>],
    group: &[u32],
    variant: Variant,
    marks: &mut Vec<Mark>,
) {
    let field_rule = (!variant.relax_o6).then_some(Reason::FieldEscapes);
    let callee = flags.get(g as usize).filter(|f| !f.is_empty());
    for (j, r) in code.ops[args.start as usize..(args.start + args.len) as usize]
        .iter()
        .enumerate()
    {
        if callee.is_some_and(|c| c.get(j) == Some(&true)) {
            if tail && s[(r & !MOVE) as usize] == Org::Own {
                if group[g as usize] == group[me] {
                    marks.push(Mark::Callee(g as usize, j, Reason::TailOwned));
                } else if !variant.b2 {
                    marks.push(Mark::Callee(g as usize, j, Reason::TailAcross));
                }
            }
            if r & MOVE != 0 {
                s[(r & !MOVE) as usize] = Org::Own;
            }
        } else {
            escape(marks, s, *r, Reason::PassedOwned, field_rule);
        }
    }
}

/// Scans one function's body under the current flags, appending what it
/// forces owned. `false` if the body isn't forward-only (it is then left
/// all owned).
fn scan(
    me: usize,
    func: &Func,
    flags: &[Vec<bool>],
    group: &[u32],
    variant: Variant,
    marks: &mut Vec<Mark>,
) -> bool {
    let code = func.code;
    let regs = code.regs as usize;
    let mut cur: Option<Vec<Org>> = Some({
        let mut s = vec![Org::Own; regs];
        for (p, b) in flags[me].iter().enumerate() {
            if *b {
                s[p] = Org::Lent {
                    root: p as u32,
                    direct: true,
                };
            }
        }
        s
    });
    let mut pending: HashMap<u32, Vec<Org>> = HashMap::default();
    let mut targets = Vec::new();
    for (pc, instr) in code.instrs.iter().enumerate() {
        if let Some(p) = pending.remove(&(pc as u32)) {
            cur = Some(match cur.take() {
                None => p,
                Some(mut c) => {
                    for (a, b) in c.iter_mut().zip(&p) {
                        if a != b {
                            *a = Org::Own;
                        }
                    }
                    c
                }
            });
        }
        let Some(s) = cur.as_mut() else { continue };
        match *instr {
            Instr::Move { dst, src } => s[dst as usize] = s[src as usize],
            Instr::Take { dst, src } => {
                s[dst as usize] = s[src as usize];
                s[src as usize] = Org::Own;
            }
            Instr::Drop { reg } => s[reg as usize] = Org::Own,
            Instr::Const { dst, k } => {
                s[dst as usize] = if func.plain_consts.get(k as usize) == Some(&true) {
                    Org::Plain
                } else {
                    Org::Own
                };
            }
            Instr::Captured { dst, .. }
            | Instr::Global { dst, .. }
            | Instr::StaticClosure { dst, .. }
            | Instr::NatPred { dst, .. }
            | Instr::IntOfNat { dst, .. }
            | Instr::IntNegSucc { dst, .. }
            | Instr::TextChars { dst, .. } => s[dst as usize] = Org::Own,
            Instr::Call { dst, g, args } => {
                call_args(me, code, g, args, false, s, flags, group, variant, marks);
                s[dst as usize] = Org::Own;
            }
            Instr::TailCall { g, args } => {
                call_args(me, code, g, args, true, s, flags, group, variant, marks);
            }
            Instr::Prim { dst, op, args } => {
                let effect = matches!(op, PrimOp::Effect(_));
                if effect || op.consumes() {
                    for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                        escape(marks, s, *r, Reason::Stored, None);
                    }
                }
                s[dst as usize] = Org::Own;
            }
            Instr::TailPrim { args, .. } => {
                for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                    escape(marks, s, *r, Reason::Stored, None);
                }
            }
            Instr::Pap { dst, args, .. }
            | Instr::Closure { dst, args, .. }
            | Instr::Ctor { dst, args, .. } => {
                for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                    escape(marks, s, *r, Reason::Stored, None);
                }
                s[dst as usize] = Org::Own;
            }
            Instr::CtorReuse {
                dst, args, token, ..
            } => {
                for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                    escape(marks, s, *r, Reason::Stored, None);
                }
                s[token as usize] = Org::Own;
                s[dst as usize] = Org::Own;
            }
            Instr::Apply { dst, f, args } => {
                escape(marks, s, f, Reason::Stored, None);
                for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                    escape(marks, s, *r, Reason::Stored, None);
                }
                s[dst as usize] = Org::Own;
            }
            Instr::TailApply { f, args } => {
                escape(marks, s, f, Reason::Stored, None);
                for r in &code.ops[args.start as usize..(args.start + args.len) as usize] {
                    escape(marks, s, *r, Reason::Stored, None);
                }
            }
            Instr::Field { dst, src, .. } => {
                s[dst as usize] = match s[src as usize] {
                    Org::Lent { root, .. } => Org::Lent {
                        root,
                        direct: false,
                    },
                    Org::Own | Org::Plain => Org::Own,
                };
            }
            Instr::Unpack { src, fields, token } => {
                let lent = s[src as usize];
                if let Org::Lent { root, .. } = lent
                    && token != NO_REG
                {
                    marks.push(Mark::Own(root as usize, Reason::Reused));
                }
                for p in code.ops[fields.start as usize..(fields.start + fields.len) as usize]
                    .as_chunks::<2>()
                    .0
                {
                    s[p[1] as usize] = match lent {
                        Org::Lent { root, .. } => Org::Lent {
                            root,
                            direct: false,
                        },
                        Org::Own | Org::Plain => Org::Own,
                    };
                }
                s[src as usize] = Org::Own;
                if token != NO_REG {
                    s[token as usize] = Org::Own;
                }
            }
            Instr::DropReuse { src, token } => {
                if let Org::Lent { root, .. } = s[src as usize] {
                    marks.push(Mark::Own(root as usize, Reason::Reused));
                }
                s[src as usize] = Org::Own;
                s[token as usize] = Org::Own;
            }
            Instr::Return { src } => escape(marks, s, src, Reason::Returned, None),
            Instr::Switch { .. }
            | Instr::NatCase { .. }
            | Instr::IntCase { .. }
            | Instr::NumSwitch { .. }
            | Instr::JumpIfFalse { .. }
            | Instr::Test { .. }
            | Instr::Jump { .. }
            | Instr::Unreachable => {}
        }
        targets.clear();
        let falls = successors(code, instr, &mut targets);
        for t in &targets {
            if *t as usize <= pc {
                return false;
            }
            let snapshot = cur.as_ref().expect("live").clone();
            match pending.get_mut(t) {
                None => {
                    pending.insert(*t, snapshot);
                }
                Some(old) => {
                    for (a, b) in old.iter_mut().zip(&snapshot) {
                        if a != b {
                            *a = Org::Own;
                        }
                    }
                }
            }
        }
        if !falls {
            cur = None;
        }
    }
    true
}

fn strong_groups(edges: &[Vec<u32>], live: &[bool]) -> Vec<u32> {
    // Tarjan's, iterative; groups are numbered callees first.
    let n = edges.len();
    let mut index = vec![u32::MAX; n];
    let mut low = vec![0u32; n];
    let mut on = vec![false; n];
    let mut group = vec![0u32; n];
    let mut stack = Vec::new();
    let (mut counter, mut groups) = (0u32, 0u32);
    for root in 0..n {
        if !live[root] || index[root] != u32::MAX {
            continue;
        }
        let mut work = vec![(root, 0usize)];
        index[root] = counter;
        low[root] = counter;
        counter += 1;
        stack.push(root);
        on[root] = true;
        while let Some(&(v, i)) = work.last() {
            if i < edges[v].len() {
                work.last_mut().expect("work").1 += 1;
                let w = edges[v][i] as usize;
                if !live[w] {
                    continue;
                }
                if index[w] == u32::MAX {
                    index[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    on[w] = true;
                    work.push((w, 0));
                } else if on[w] {
                    low[v] = low[v].min(index[w]);
                }
            } else {
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    low[parent] = low[parent].min(low[v]);
                }
                if low[v] == index[v] {
                    loop {
                        let w = stack.pop().expect("stack");
                        on[w] = false;
                        group[w] = groups;
                        if w == v {
                            break;
                        }
                    }
                    groups += 1;
                }
            }
        }
    }
    group
}

/// Infers which parameters of `funcs` (by global index) are borrowed.
pub fn infer(funcs: &[Option<Func>], variant: Variant) -> Inference {
    let n = funcs.len();
    let live: Vec<bool> = funcs.iter().map(Option::is_some).collect();
    let mut borrowed: Vec<Vec<bool>> = vec![Vec::new(); n];
    let mut reason: Vec<Vec<Option<Reason>>> = vec![Vec::new(); n];
    let mut edges: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (g, f) in funcs.iter().enumerate() {
        let Some(f) = f else { continue };
        let params = f.code.params as usize;
        borrowed[g] = vec![true; params];
        reason[g] = vec![None; params];
        let mut own = |p: usize, why: Reason| {
            borrowed[g][p] = false;
            reason[g][p].get_or_insert(why);
        };
        if f.fixed == Fixed::Last && params > 0 {
            own(params - 1, Reason::Fixed);
        }
        if has_holes(f.code) {
            (0..params).for_each(|p| own(p, Reason::Fixed));
        }
        if !variant.b2 && f.value_used {
            (0..params).for_each(|p| own(p, Reason::ValueUse));
        }
        for i in &f.code.instrs {
            if let Instr::Call { g: t, .. } | Instr::TailCall { g: t, .. } = i
                && funcs.get(*t as usize).is_some_and(Option::is_some)
            {
                edges[g].push(*t);
            }
        }
    }
    let group = strong_groups(&edges, &live);
    let mut order: Vec<usize> = (0..n).filter(|g| live[*g]).collect();
    order.sort_by_key(|g| group[*g]);
    let mut marks = Vec::new();
    loop {
        let mut outer = false;
        let mut i = 0;
        while i < order.len() {
            let mut j = i;
            while j < order.len() && group[order[j]] == group[order[i]] {
                j += 1;
            }
            loop {
                let mut changed = false;
                for &g in &order[i..j] {
                    marks.clear();
                    let ok = scan(
                        g,
                        funcs[g].as_ref().expect("live"),
                        &borrowed,
                        &group,
                        variant,
                        &mut marks,
                    );
                    if !ok {
                        marks.extend((0..borrowed[g].len()).map(|p| Mark::Own(p, Reason::Fixed)));
                    }
                    for m in marks.drain(..) {
                        let (t, p, why) = match m {
                            Mark::Own(p, why) => (g, p, why),
                            Mark::Callee(t, p, why) => (t, p, why),
                        };
                        if borrowed[t].get(p) == Some(&true) {
                            borrowed[t][p] = false;
                            reason[t][p] = Some(why);
                            changed = true;
                            if t != g && group[t] != group[g] {
                                outer = true;
                            }
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            i = j;
        }
        if !outer {
            break;
        }
    }
    Inference {
        borrowed,
        reason,
        group,
    }
}

/// Totals over an inference, for the report.
#[derive(Default, Debug)]
pub struct Summary {
    pub functions: usize,
    pub with_borrowed: usize,
    pub params: usize,
    pub borrowed: usize,
    pub by_reason: [usize; 9],
}

impl Inference {
    pub fn summary(&self) -> Summary {
        let mut s = Summary::default();
        for (g, flags) in self.borrowed.iter().enumerate() {
            if flags.is_empty() {
                continue;
            }
            s.functions += 1;
            s.params += flags.len();
            s.borrowed += flags.iter().filter(|b| **b).count();
            s.with_borrowed += usize::from(flags.iter().any(|b| *b));
            for r in self.reason[g].iter().flatten() {
                let i = Reason::ALL.iter().position(|a| a == r).expect("known");
                s.by_reason[i] += 1;
            }
        }
        s
    }
}

#[cfg(feature = "borrow-counts")]
pub use shadow::*;

#[cfg(feature = "borrow-counts")]
mod shadow;

#[cfg(test)]
mod tests;
