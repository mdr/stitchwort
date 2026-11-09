//! Borrowed parameters (docs/proposals/borrow-inference.md, "Stage B1 as
//! built"): the compiler works out which parameters a function only reads,
//! and the caller lends those instead of handing over a reference, so a
//! read-only walk over a structure the program keeps (a `Map` lookup)
//! counts nothing.
//!
//! **The inference** reads the compiled bytecode ([`Code`]), which already
//! holds the decisions the note's rule O5 has to respect (an
//! [`Instr::Unpack`] with a token, or an [`Instr::DropReuse`], is a cell
//! that will be reused, so its owner must keep it) and each operand's last
//! use ([`MOVE`]). Bodies are forward-only (loops are tail calls), so one
//! pass in order, joining at jump targets, is a complete dataflow. Every
//! runtime parameter of a global function starts borrowed, and is made
//! owned when:
//!
//! - fed: a direct call hands it an owned value at its last use, which
//!   the caller would otherwise drop after the call: the callee might have
//!   freed it, or reused it, as it went. A value known to have another
//!   reference (a copy, or a field read from a value that stays live:
//!   [`St::Shared`]) doesn't count. The note's O1 (stored in a constructor,
//!   closure, partial application, function-value call, effect native or
//!   consuming native), O2 (returned) and O3 (passed to an owned parameter)
//!   are not rules by themselves: they only name the reason when the
//!   parameter is fed. A parameter that escapes but that every caller lends
//!   (a value it keeps, or one itself lent) is incremented where it
//!   escapes, which costs what the increment at the call would have.
//!   (So `Map`'s `get` borrows the node's value through its lifted match,
//!   which stores it in `Some` on one arm, and a lookup increments the value
//!   once, not at every level.)
//! - O4 an owned value is tail-passed to a borrowed parameter of a function
//!   in the same strongly connected group (the caller would have to drop it
//!   after the call, ending the tail call): the callee's parameter is owned;
//! - O5 reused: the cell is unpacked with a token, or dropped as one;
//! - O7 the function is used as a value anywhere (function values are
//!   called with owned arguments);
//! - O8 an owned value is tail-passed to a borrowed parameter of a function
//!   in another group;
//! - merge: at a jump target, a register is lent on one path and owned on
//!   another (each register's state at each instruction must be known, for
//!   native code and the machine to agree on who drops it);
//! - fresh: a direct call passes a value the caller has just made (a
//!   call's, constructor's or native operation's result, at its last use):
//!   such a value is likely the only reference, so the callee, owning it,
//!   frees it as it goes (`Unpack`'s unique path, into native code's cell
//!   cache), where borrowed it would be dropped whole after the call, by
//!   the runtime. (SW-2565: binary-trees' `check (make depth)` ran 83%
//!   more instructions without this rule.)
//!
//! The note's O6 is not a rule (SW-2530's measurements): a field of a lent
//! value that goes where values are kept (a constructor, an owned
//! parameter, a result) is incremented there, once, and its parent stays
//! borrowed. Groups are solved callees first, each to a fixpoint; since
//! flags only move towards owned, an outer loop repeats until the O4 and O8
//! marks on earlier groups settle. Flipping a parameter to owned is always
//! sound, so every doubt resolves that way: a reuse copy's token, a loop
//! with hole operations, and a body bigger than [`MAX_REGS`] or
//! [`MAX_INSTRS`] are owned throughout.
//!
//! **The rewrite** ([`rewrite`]). A *lent* register holds a value without
//! owning a reference to it: a borrowed parameter, or a field read from a
//! lent register. Each body's bytecode is rewritten so that every lent
//! value's life is explicit:
//!
//! - a field of a lent value is read with [`Instr::Peek`] (no count), and a
//!   lent `Unpack` becomes `Peek`s;
//! - a lent value copied or moved to another register is [`Instr::Lend`];
//! - a lent value moved where values are kept is first [`Instr::Own`]ed (an
//!   increment), as is one returned;
//! - a lent register that dies, is overwritten or is still held when the
//!   frame ends is [`Instr::Forget`]ten first;
//! - a call passes any operand at a borrowed position without a count. An
//!   owned value the caller moves there is passed without its `MOVE` and
//!   dropped after the call ([`Instr::Drop`]), and so is one passed both
//!   to a borrowed and an owned position of the same call.
//!
//! Native code then executes exactly that (no increment or decrement for a
//! lent value anywhere), and the machine, which stays free of `unsafe`,
//! keeps a real copy of each lent value that it leaves out of the
//! allocation trace, and checks at each `Forget` that its copy is not the
//! last reference (D3442). Every tail call stays a tail call (D3443).
//!
//! **The check** ([`check`]) runs over every rewritten body and holds the
//! discipline above; it is what makes the rewrite's mistakes a panic at
//! compile time rather than a use after free in native code.

use stitchwort_core::collections::HashMap;

use crate::code::{Code, Image, Instr, MOVE, NO_REG, Ops, Reg};
use crate::ir::{GlobalKind, HoleOp, PrimOp, Program, Reuse};

/// The most registers a body that borrows may have. Native code keeps a
/// bigger body's registers in a register file on the heap, whose error
/// exits drop every register in it (n1.rs, "Large bodies"); a body with
/// borrowed parameters is compiled with variables whatever its size, so
/// this only keeps such bodies small for Cranelift.
pub const MAX_REGS: u32 = 128;
/// The most instructions a body that borrows may have (as [`MAX_REGS`]).
pub const MAX_INSTRS: usize = 512;

/// Why a parameter is owned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reason {
    Stored,
    Returned,
    PassedOwned,
    TailOwned,
    Reused,
    ValueUse,
    TailAcross,
    Merge,
    Fresh,
    Fed,
    /// Never borrowed: a reuse copy's token, a loop with hole operations,
    /// a body that isn't forward-only or is too big.
    Fixed,
}

impl Reason {
    pub const ALL: [Reason; 11] = [
        Reason::Stored,
        Reason::Returned,
        Reason::PassedOwned,
        Reason::TailOwned,
        Reason::Reused,
        Reason::ValueUse,
        Reason::TailAcross,
        Reason::Merge,
        Reason::Fresh,
        Reason::Fed,
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
            Reason::ValueUse => "O7 used as a value",
            Reason::TailAcross => "O8 owned tail argument, other group",
            Reason::Merge => "lent and owned meet at a jump target",
            Reason::Fresh => "given a value its caller just made",
            Reason::Fed => "given an owned value at its last use",
            Reason::Fixed => "fixed owned (token, hole loop, size)",
        }
    }
}

/// Which parameters of a function are never borrowed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fixed {
    No,
    /// A reuse copy: the last parameter is its token.
    Last,
    /// None is borrowed.
    All,
}

/// A function the inference looks at.
pub struct Func<'a> {
    pub code: &'a Code,
    pub fixed: Fixed,
    /// Named by a `Global` or `Pap` instruction anywhere: used as a value.
    pub value_used: bool,
    /// Per constant-pool entry, whether it holds no reference (a number, a
    /// tag): a register loaded from it needs no drop, so tail-passing it
    /// is free to a borrowed parameter.
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

/// What a register holds at a point in a body.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum St {
    /// Nothing (never written, or moved out or dropped).
    Empty,
    /// An owned value that holds no reference (loaded from a plain
    /// constant): dropping it, or not, makes no difference.
    Plain,
    Own,
    /// Owned and made here (the result of a call, a constructor, a native
    /// operation): likely the only reference.
    Fresh,
    /// Owned, with another reference known to be held: a field read from
    /// a value that stays live, or a copy.
    Shared,
    /// Lent: borrowed parameter `root` itself (`direct`), or a value read
    /// from it.
    Lent {
        root: u32,
        direct: bool,
    },
}

enum Mark {
    /// A parameter of the function scanned must be owned.
    Own(usize, Reason),
    /// Parameter `.1` of function `.0` must be owned.
    Callee(usize, usize, Reason),
    /// A parameter of the function scanned escapes (O1-O3): the reason
    /// given if it is fed.
    Escapes(usize, Reason),
    /// A direct call hands parameter `.1` of function `.0` an owned value
    /// at its last use, which the caller drops after the call if the
    /// parameter is borrowed.
    Fed(usize, usize),
}

/// The inference's state: per function, per parameter.
struct Params {
    borrowed: Vec<Vec<bool>>,
    reason: Vec<Vec<Option<Reason>>>,
    escapes: Vec<Vec<Option<Reason>>>,
}

impl Params {
    /// Applies a mark from scanning function `g` (`usize::MAX` for a body
    /// that takes no part): the function whose parameter became owned, if
    /// one did.
    fn mark(&mut self, g: usize, m: Mark) -> Option<usize> {
        let (t, p, why) = match m {
            Mark::Own(p, why) => (g, p, why),
            Mark::Callee(t, p, why) => (t, p, why),
            Mark::Escapes(p, why) => {
                self.escapes[g][p].get_or_insert(why);
                return None;
            }
            Mark::Fed(t, p) => {
                let why = self.escapes[t].get(p).copied().flatten();
                (t, p, why.unwrap_or(Reason::Fed))
            }
        };
        if self.borrowed[t].get(p) != Some(&true) {
            return None;
        }
        self.borrowed[t][p] = false;
        self.reason[t][p] = Some(why);
        Some(t)
    }
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

fn ops(code: &Code, o: Ops) -> &[Reg] {
    &code.ops[o.start as usize..(o.start + o.len) as usize]
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

/// Holding an owned value that holds a reference (or may).
fn owned(s: St) -> bool {
    matches!(s, St::Own | St::Fresh | St::Shared)
}

/// Two paths' states of a register meeting at a jump target. `Err` if one
/// is lent and the other holds an owned value: the roots it was lent from.
fn join(a: St, b: St) -> Result<St, [Option<u32>; 2]> {
    match (a, b) {
        _ if a == b => Ok(a),
        (St::Empty, x) | (x, St::Empty) => Ok(x),
        (St::Plain, x) | (x, St::Plain) if owned(x) => Ok(x),
        (x, y) if owned(x) && owned(y) => Ok(St::Own),
        (
            St::Lent {
                root: r1,
                direct: d1,
            },
            St::Lent {
                root: r2,
                direct: d2,
            },
        ) if r1 == r2 => Ok(St::Lent {
            root: r1,
            direct: d1 || d2,
        }),
        _ => {
            let root = |s: St| match s {
                St::Lent { root, .. } => Some(root),
                _ => None,
            };
            Err([root(a), root(b)])
        }
    }
}

/// What instruction `instr` does to the registers' states (the bytecode
/// before or after [`rewrite`]).
fn transfer(code: &Code, instr: &Instr, s: &mut [St], plain: &[bool]) {
    let moved = |s: &mut [St], o: Ops| {
        for r in ops(code, o) {
            if r & MOVE != 0 {
                s[(r & !MOVE) as usize] = St::Empty;
            }
        }
    };
    let lent_from = |s: St| match s {
        St::Lent { root, .. } => St::Lent {
            root,
            direct: false,
        },
        _ => St::Own,
    };
    match *instr {
        Instr::Move { dst, src } => {
            // Two references now.
            if owned(s[src as usize]) {
                s[src as usize] = St::Shared;
            }
            s[dst as usize] = s[src as usize];
        }
        Instr::Take { dst, src } => {
            let v = s[src as usize];
            s[src as usize] = St::Empty;
            s[dst as usize] = v;
        }
        Instr::Drop { reg } | Instr::Forget { reg } => s[reg as usize] = St::Empty,
        Instr::Own { reg } => s[reg as usize] = St::Own,
        Instr::Const { dst, k } => {
            s[dst as usize] = if plain.get(k as usize) == Some(&true) {
                St::Plain
            } else {
                St::Own
            };
        }
        Instr::Captured { dst, .. }
        | Instr::Global { dst, .. }
        | Instr::StaticClosure { dst, .. }
        | Instr::NatPred { dst, .. }
        | Instr::IntOfNat { dst, .. }
        | Instr::IntNegSucc { dst, .. }
        | Instr::TextChars { dst, .. } => s[dst as usize] = St::Own,
        Instr::Call { dst, args, .. }
        | Instr::Prim { dst, args, .. }
        | Instr::Pap { dst, args, .. }
        | Instr::Closure { dst, args, .. }
        | Instr::Ctor { dst, args, .. } => {
            moved(s, args);
            s[dst as usize] = St::Fresh;
        }
        Instr::CtorReuse {
            dst, args, token, ..
        } => {
            moved(s, args);
            s[token as usize] = St::Empty;
            s[dst as usize] = St::Fresh;
        }
        Instr::Apply { dst, f, args } => {
            if f & MOVE != 0 {
                s[(f & !MOVE) as usize] = St::Empty;
            }
            moved(s, args);
            s[dst as usize] = St::Fresh;
        }
        Instr::TailCall { .. } | Instr::TailApply { .. } | Instr::TailPrim { .. } => {}
        Instr::Field { dst, src, .. } | Instr::Peek { dst, src, .. } => {
            s[dst as usize] = match s[src as usize] {
                St::Lent { root, .. } => St::Lent {
                    root,
                    direct: false,
                },
                // The value it was read from still holds it.
                _ => St::Shared,
            };
        }
        Instr::Lend { dst, src } => s[dst as usize] = s[src as usize],
        Instr::Unpack { src, fields, token } => {
            let from = s[src as usize];
            s[src as usize] = St::Empty;
            // A shared cell is left whole and its fields copied: shared too.
            let field = match from {
                St::Shared => St::Shared,
                other => lent_from(other),
            };
            for p in ops(code, fields).as_chunks::<2>().0 {
                if p[1] != NO_REG {
                    s[p[1] as usize] = field;
                }
            }
            if token != NO_REG {
                s[token as usize] = St::Own;
            }
        }
        Instr::DropReuse { src, token } => {
            s[src as usize] = St::Empty;
            s[token as usize] = St::Own;
        }
        Instr::Return { .. }
        | Instr::Switch { .. }
        | Instr::NatCase { .. }
        | Instr::IntCase { .. }
        | Instr::NumSwitch { .. }
        | Instr::JumpIfFalse { .. }
        | Instr::Test { .. }
        | Instr::Jump { .. }
        | Instr::Unreachable => {}
    }
}

/// Runs over a forward-only body from `entry`, calling `each` with every
/// reachable instruction's index and the registers' states before it,
/// which it may look at; `meet` hears of every register lent on one path
/// and owned on another at a jump target (the join is then owned).
/// `false` if a jump goes back.
fn forward(
    code: &Code,
    entry: Vec<St>,
    plain: &[bool],
    mut each: impl FnMut(usize, &[St]),
    mut meet: impl FnMut(usize, Reg, [Option<u32>; 2]),
) -> bool {
    let mut cur: Option<Vec<St>> = Some(entry);
    let mut pending: HashMap<u32, Vec<St>> = HashMap::default();
    let mut targets = Vec::new();
    let mut merge = |pc: usize, into: &mut Vec<St>, from: &[St]| {
        for (r, (a, b)) in into.iter_mut().zip(from).enumerate() {
            *a = join(*a, *b).unwrap_or_else(|roots| {
                meet(pc, r as Reg, roots);
                St::Own
            });
        }
    };
    for (pc, instr) in code.instrs.iter().enumerate() {
        if let Some(p) = pending.remove(&(pc as u32)) {
            cur = Some(match cur.take() {
                None => p,
                Some(mut c) => {
                    merge(pc, &mut c, &p);
                    c
                }
            });
        }
        let Some(s) = cur.as_mut() else { continue };
        each(pc, s);
        transfer(code, instr, s, plain);
        targets.clear();
        let falls = successors(code, instr, &mut targets);
        for t in &targets {
            if *t as usize <= pc {
                return false;
            }
            let snapshot = cur.as_ref().expect("live");
            match pending.get_mut(t) {
                None => {
                    pending.insert(*t, snapshot.clone());
                }
                Some(old) => merge(*t as usize, old, snapshot),
            }
        }
        if !falls {
            cur = None;
        }
    }
    true
}

/// The registers' states on entry to a body with these flags.
fn entry_state(code: &Code, borrowed: &[bool]) -> Vec<St> {
    let mut s = vec![St::Empty; code.regs as usize];
    for (p, st) in s.iter_mut().take(code.params as usize).enumerate() {
        *st = if borrowed.get(p) == Some(&true) {
            St::Lent {
                root: p as u32,
                direct: true,
            }
        } else {
            St::Own
        };
    }
    s
}

/// Using `r` where a reference is kept or handed to an owner: a lent
/// parameter itself must then be owned. (A field of one is incremented
/// there.)
fn escape(marks: &mut Vec<Mark>, s: &[St], r: Reg, why: Reason) {
    if let St::Lent { root, direct: true } = s[(r & !MOVE) as usize] {
        marks.push(Mark::Escapes(root as usize, why));
    }
}

/// The rules an instruction applies, given the registers' states before
/// it.
fn rules(
    me: usize,
    code: &Code,
    instr: &Instr,
    s: &[St],
    flags: &[Vec<bool>],
    group: &[u32],
    marks: &mut Vec<Mark>,
) {
    let all = |marks: &mut Vec<Mark>, o: Ops| {
        for r in ops(code, o) {
            escape(marks, s, *r, Reason::Stored);
        }
    };
    match *instr {
        Instr::Call { g, args, .. } | Instr::TailCall { g, args } => {
            let tail = matches!(instr, Instr::TailCall { .. });
            let callee = flags.get(g as usize).map_or(&[][..], |f| &f[..]);
            for (j, r) in ops(code, args).iter().enumerate() {
                if callee.get(j) == Some(&true) {
                    let st = s[(r & !MOVE) as usize];
                    if !tail && r & MOVE != 0 && st == St::Fresh {
                        marks.push(Mark::Callee(g as usize, j, Reason::Fresh));
                    } else if !tail && r & MOVE != 0 && st == St::Own {
                        marks.push(Mark::Fed(g as usize, j));
                    }
                    if tail && owned(st) {
                        if group.get(me) == Some(&group[g as usize]) {
                            marks.push(Mark::Callee(g as usize, j, Reason::TailOwned));
                        } else {
                            marks.push(Mark::Callee(g as usize, j, Reason::TailAcross));
                        }
                    }
                } else {
                    escape(marks, s, *r, Reason::PassedOwned);
                }
            }
        }
        Instr::Prim { op, args, .. } => {
            if matches!(op, PrimOp::Effect(_)) || op.consumes() {
                all(marks, args);
            }
        }
        Instr::TailPrim { args, .. }
        | Instr::Pap { args, .. }
        | Instr::Closure { args, .. }
        | Instr::Ctor { args, .. }
        | Instr::CtorReuse { args, .. } => all(marks, args),
        Instr::Apply { f, args, .. } | Instr::TailApply { f, args } => {
            escape(marks, s, f, Reason::Stored);
            all(marks, args);
        }
        Instr::Unpack { src, token, .. } if token != NO_REG => {
            if let St::Lent { root, .. } = s[src as usize] {
                marks.push(Mark::Own(root as usize, Reason::Reused));
            }
        }
        Instr::DropReuse { src, .. } => {
            if let St::Lent { root, .. } = s[src as usize] {
                marks.push(Mark::Own(root as usize, Reason::Reused));
            }
        }
        Instr::Return { src } => escape(marks, s, src, Reason::Returned),
        _ => {}
    }
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
/// `others` are the bodies that call them but take no part (lambdas,
/// constants, the entry): only their tail calls matter (O8).
pub fn infer(funcs: &[Option<Func>], others: &[&Code], plain: &[bool]) -> Inference {
    let n = funcs.len();
    let live: Vec<bool> = funcs.iter().map(Option::is_some).collect();
    let mut at = Params {
        borrowed: vec![Vec::new(); n],
        reason: vec![Vec::new(); n],
        escapes: vec![Vec::new(); n],
    };
    let mut edges: Vec<Vec<u32>> = vec![Vec::new(); n];
    for (g, f) in funcs.iter().enumerate() {
        let Some(f) = f else { continue };
        let params = f.code.params as usize;
        at.borrowed[g] = vec![true; params];
        at.reason[g] = vec![None; params];
        at.escapes[g] = vec![None; params];
        let mut own = |p: usize, why: Reason| {
            at.borrowed[g][p] = false;
            at.reason[g][p].get_or_insert(why);
        };
        if f.fixed == Fixed::Last && params > 0 {
            own(params - 1, Reason::Fixed);
        }
        if f.fixed == Fixed::All || has_holes(f.code) {
            (0..params).for_each(|p| own(p, Reason::Fixed));
        }
        if f.value_used {
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
                    let f = funcs[g].as_ref().expect("live");
                    marks.clear();
                    let entry = entry_state(f.code, &at.borrowed[g]);
                    let mut met = Vec::new();
                    let ok = forward(
                        f.code,
                        entry,
                        f.plain_consts,
                        |pc, s| {
                            rules(
                                g,
                                f.code,
                                &f.code.instrs[pc],
                                s,
                                &at.borrowed,
                                &group,
                                &mut marks,
                            )
                        },
                        |_, _, roots| met.extend(roots.into_iter().flatten()),
                    );
                    marks.extend(
                        met.into_iter()
                            .map(|root| Mark::Own(root as usize, Reason::Merge)),
                    );
                    if !ok {
                        marks
                            .extend((0..at.borrowed[g].len()).map(|p| Mark::Own(p, Reason::Fixed)));
                    }
                    for m in marks.drain(..) {
                        if let Some(t) = at.mark(g, m) {
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
        for code in others {
            marks.clear();
            let entry = entry_state(code, &[]);
            forward(
                code,
                entry,
                plain,
                |pc, s| {
                    rules(
                        usize::MAX,
                        code,
                        &code.instrs[pc],
                        s,
                        &at.borrowed,
                        &group,
                        &mut marks,
                    )
                },
                |_, _, _| {},
            );
            for m in marks.drain(..) {
                if matches!(m, Mark::Callee(..) | Mark::Fed(..)) && at.mark(usize::MAX, m).is_some()
                {
                    outer = true;
                }
            }
        }
        if !outer {
            break;
        }
    }
    Inference {
        borrowed: at.borrowed,
        reason: at.reason,
        group,
    }
}

/// Totals over an inference, for the dump.
#[derive(Default, Debug)]
pub struct Summary {
    pub functions: usize,
    pub with_borrowed: usize,
    pub params: usize,
    pub borrowed: usize,
    pub by_reason: [usize; 11],
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

/// Infers the borrowed parameters of a compiled program's functions,
/// rewrites every body to lend them ([`rewrite`]) and checks the result
/// ([`check`]). With `STITCHWORT_BORROW_DUMP` set, lists the functions
/// with a borrowed parameter on standard error (those whose name contains
/// its value, if it is longer than one character).
pub fn apply(program: &Program, image: &mut Image) {
    let n = program.globals.len();
    let mut used = vec![false; n];
    for code in &image.codes {
        for i in &code.instrs {
            if let Instr::Global { g, .. } | Instr::Pap { g, .. } = i {
                used[*g as usize] = true;
            }
        }
    }
    for g in 0..n {
        if used[g]
            && let Reuse::Copies(copies) = &program.globals[g].reuse
        {
            for (_, copy) in copies.clone() {
                used[copy.0 as usize] = true;
            }
        }
    }
    let plain: Vec<bool> = image.pool.iter().map(|v| !v.owns()).collect();
    let inference = {
        let funcs: Vec<Option<Func>> = (0..n)
            .map(|g| {
                let global = &program.globals[g];
                if !matches!(global.kind, GlobalKind::Function { .. }) {
                    return None;
                }
                let code = &image.codes[image.global_code[g]? as usize];
                if code.params == 0 {
                    return None;
                }
                let fixed = if code.regs > MAX_REGS || code.instrs.len() > MAX_INSTRS {
                    Fixed::All
                } else if matches!(global.reuse, Reuse::Copy { .. }) {
                    Fixed::Last
                } else {
                    Fixed::No
                };
                Some(Func {
                    code,
                    fixed,
                    value_used: used[g],
                    plain_consts: &plain,
                })
            })
            .collect();
        let mut others: Vec<&Code> = image
            .lambda_code
            .iter()
            .chain([&image.entry_code])
            .map(|c| &image.codes[*c as usize])
            .collect();
        for (g, code) in image.global_code.iter().enumerate() {
            if let Some(code) = code
                && funcs[g].is_none()
            {
                others.push(&image.codes[*code as usize]);
            }
        }
        infer(&funcs, &others, &plain)
    };
    let by_global: Vec<Box<[bool]>> = inference
        .borrowed
        .iter()
        .map(|f| {
            if f.iter().any(|b| *b) {
                f.clone().into_boxed_slice()
            } else {
                Box::default()
            }
        })
        .collect();
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = code {
            image.codes[*code as usize].borrowed = by_global[g].clone();
        }
    }
    let callee = |g: u32| -> &[bool] { by_global.get(g as usize).map_or(&[], |f| &f[..]) };
    for (i, code) in image.codes.iter_mut().enumerate() {
        if rewrite(code, &callee, &plain)
            && let Err(e) = check(code, &callee, &plain)
        {
            panic!("internal error: borrowed code {i} breaks the discipline: {e}");
        }
    }
    if let Ok(want) = std::env::var("STITCHWORT_BORROW_DUMP") {
        dump(program, &inference, &want);
        if want.len() > 1 {
            for (g, code) in image.global_code.iter().enumerate() {
                let name = &program.globals[g].name;
                if let Some(code) = code
                    && name.contains(&want)
                {
                    let code = &image.codes[*code as usize];
                    eprintln!("borrow-code {name} {:?}", code.borrowed);
                    for (pc, i) in code.instrs.iter().enumerate() {
                        let o = |o: Ops| ops(code, o).to_vec();
                        let args = match i {
                            Instr::Call { args, .. }
                            | Instr::TailCall { args, .. }
                            | Instr::Ctor { args, .. }
                            | Instr::Prim { args, .. }
                            | Instr::Apply { args, .. }
                            | Instr::TailApply { args, .. }
                            | Instr::Unpack { fields: args, .. } => format!(" {:x?}", o(*args)),
                            _ => String::new(),
                        };
                        let callee = match i {
                            Instr::Call { g, .. } | Instr::TailCall { g, .. } => {
                                format!(" -> {}", program.globals[*g as usize].name)
                            }
                            _ => String::new(),
                        };
                        eprintln!("  {pc}: {i:?}{args}{callee}");
                    }
                }
            }
        }
    }
}

fn dump(program: &Program, inference: &Inference, want: &str) {
    let s = inference.summary();
    eprintln!(
        "borrow functions={} with_borrowed={} params={} borrowed={}",
        s.functions, s.with_borrowed, s.params, s.borrowed
    );
    for (i, r) in Reason::ALL.iter().enumerate() {
        eprintln!("borrow owned-by {}={}", r.name(), s.by_reason[i]);
    }
    for (g, flags) in inference.borrowed.iter().enumerate() {
        let name = &program.globals[g].name;
        // Named ones are listed even if they borrow nothing.
        let named = want.len() > 1 && name.contains(want);
        if named || (want.len() <= 1 && flags.iter().any(|b| *b)) {
            let bits: String = flags.iter().map(|b| if *b { 'B' } else { 'o' }).collect();
            eprintln!("borrow-fn {name} {bits} {:?}", inference.reason[g]);
        }
    }
}

/// The registers lent before each instruction of `code` (whose flags are
/// `code.borrowed`), by pc: what a frame stopped there holds without a
/// count. `plain` says which pool entries hold no reference. Empty for a
/// body that doesn't borrow.
pub fn lent_table(code: &Code, plain: &[bool]) -> Vec<Vec<Reg>> {
    if !code.borrowed.iter().any(|b| *b) {
        return Vec::new();
    }
    let mut table = vec![Vec::new(); code.instrs.len()];
    forward(
        code,
        entry_state(code, &code.borrowed),
        plain,
        |at, s| {
            table[at] = (0..s.len() as Reg)
                .filter(|r| matches!(s[*r as usize], St::Lent { .. }))
                .collect();
        },
        |_, _, _| {},
    );
    table
}

// ----------------------------------------------------------------- rewrite

/// Rewrites `code` (whose own flags are `code.borrowed`) to lend: see the
/// module docs. `callee` gives a global's flags. Whether anything was
/// changed.
pub fn rewrite<'f>(code: &mut Code, callee: &dyn Fn(u32) -> &'f [bool], plain: &[bool]) -> bool {
    let lends = code.borrowed.iter().any(|b| *b);
    let calls_lend = code.instrs.iter().any(|i| match i {
        Instr::Call { g, .. } | Instr::TailCall { g, .. } => callee(*g).iter().any(|b| *b),
        _ => false,
    });
    if !lends && !calls_lend {
        return false;
    }
    let n = code.instrs.len();
    // The states before each reachable instruction; without lent
    // parameters, every register is taken to be owned.
    let states: Option<Vec<Option<Vec<St>>>> = lends.then(|| {
        let mut states = vec![None; n];
        let ok = forward(
            code,
            entry_state(code, &code.borrowed),
            plain,
            |pc, s| states[pc] = Some(s.to_vec()),
            |pc, r, _| panic!("internal error: register {r} lent and owned at {pc}"),
        );
        assert!(ok, "internal error: a borrowing body jumps back");
        states
    });
    let mut out: Vec<Instr> = Vec::with_capacity(n + n / 4);
    let mut start = vec![0u32; n + 1];
    let mut scratch: Option<Reg> = None;
    let regs = std::cell::Cell::new(code.regs);
    let fresh = || {
        regs.set(regs.get() + 1);
        regs.get() - 1
    };
    let mut scratch_reg = || *scratch.get_or_insert_with(fresh);
    let old_ops = code.ops.clone();
    let mut new_ops = std::mem::take(&mut code.ops);
    let list = |o: Ops| old_ops[o.start as usize..(o.start + o.len) as usize].to_vec();
    let mut push_ops = |list: &[Reg]| {
        let start = u32::try_from(new_ops.len()).expect("ops fit");
        new_ops.extend_from_slice(list);
        Ops {
            start,
            len: u32::try_from(list.len()).expect("ops fit"),
        }
    };
    for pc in 0..n {
        start[pc] = u32::try_from(out.len()).expect("instructions fit");
        let instr = code.instrs[pc];
        let s: Option<&[St]> = match &states {
            Some(states) => match &states[pc] {
                Some(s) => Some(s),
                None => {
                    // Unreachable: left as it is.
                    out.push(instr);
                    continue;
                }
            },
            None => None,
        };
        // Registers added by the rewrite are past the end of `s`: owned.
        let at = |r: Reg| s.and_then(|s| s.get((r & !MOVE) as usize)).copied();
        let lent = |r: Reg| matches!(at(r), Some(St::Lent { .. }));
        let plainish = |r: Reg| at(r) == Some(St::Plain);
        let all_lent = || -> Vec<Reg> {
            s.map_or(Vec::new(), |s| {
                (0..s.len() as Reg)
                    .filter(|r| matches!(s[*r as usize], St::Lent { .. }))
                    .collect()
            })
        };
        // Before an instruction that writes `dst` and doesn't read it:
        // its lent value ends.
        let forget_dst = |out: &mut Vec<Instr>, dst: Reg| {
            if lent(dst) {
                out.push(Instr::Forget { reg: dst });
            }
        };
        match instr {
            Instr::Move { dst, src } if lent(src) => {
                if dst != src {
                    forget_dst(&mut out, dst);
                    out.push(Instr::Lend { dst, src });
                }
            }
            Instr::Take { dst, src } if lent(src) => {
                if dst != src {
                    forget_dst(&mut out, dst);
                    out.push(Instr::Lend { dst, src });
                    out.push(Instr::Forget { reg: src });
                }
            }
            Instr::Drop { reg } if lent(reg) => out.push(Instr::Forget { reg }),
            Instr::Field { dst, src, i } if lent(src) => {
                if dst != src {
                    forget_dst(&mut out, dst);
                }
                out.push(Instr::Peek { dst, src, i });
            }
            Instr::Unpack { src, fields, token } if lent(src) => {
                assert_eq!(token, NO_REG, "internal error: a lent cell kept for reuse");
                let pairs = list(fields);
                let mut into_src = None;
                for p in pairs.as_chunks::<2>().0 {
                    let (i, d) = (p[0], p[1]);
                    if d == NO_REG {
                        continue;
                    }
                    if d == src {
                        into_src = Some(i);
                        continue;
                    }
                    forget_dst(&mut out, d);
                    out.push(Instr::Peek { dst: d, src, i });
                }
                match into_src {
                    Some(i) => out.push(Instr::Peek { dst: src, src, i }),
                    None => out.push(Instr::Forget { reg: src }),
                }
            }
            Instr::Unpack { fields, token, .. } => {
                for p in list(fields).as_chunks::<2>().0 {
                    if p[1] != NO_REG {
                        forget_dst(&mut out, p[1]);
                    }
                }
                if token != NO_REG {
                    forget_dst(&mut out, token);
                }
                out.push(instr);
            }
            Instr::DropReuse { src, token } => {
                assert!(!lent(src), "internal error: a lent cell kept for reuse");
                forget_dst(&mut out, token);
                out.push(instr);
            }
            Instr::Return { src } => {
                for r in all_lent() {
                    if r != src {
                        out.push(Instr::Forget { reg: r });
                    }
                }
                if lent(src) {
                    out.push(Instr::Own { reg: src });
                }
                out.push(instr);
            }
            Instr::Call { dst, g, args } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    callee(g),
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Call { dst, g, args }
                });
                out.extend(post);
            }
            Instr::TailCall { g, args } => {
                let mut a = list(args);
                operands(
                    &mut out,
                    &mut a,
                    callee(g),
                    None,
                    true,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                out.push(Instr::TailCall { g, args });
            }
            Instr::Prim { dst, op, args } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Prim { dst, op, args }
                });
                out.extend(post);
            }
            Instr::TailPrim { op, args } => {
                let mut a = list(args);
                operands(
                    &mut out,
                    &mut a,
                    &[],
                    None,
                    true,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                out.push(Instr::TailPrim { op, args });
            }
            Instr::Pap { dst, g, args } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Pap { dst, g, args }
                });
                out.extend(post);
            }
            Instr::Closure { dst, lambda, args } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Closure { dst, lambda, args }
                });
                out.extend(post);
            }
            Instr::Ctor { dst, tag, args } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Ctor { dst, tag, args }
                });
                out.extend(post);
            }
            Instr::CtorReuse {
                dst,
                tag,
                args,
                token,
            } => {
                let mut a = list(args);
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let args = push_ops(&a);
                let mut read = a.clone();
                read.push(token | MOVE);
                write_dst(&mut out, dst, &read, &lent, &mut scratch_reg, |dst| {
                    Instr::CtorReuse {
                        dst,
                        tag,
                        args,
                        token,
                    }
                });
                out.extend(post);
            }
            Instr::Apply { dst, f, args } => {
                let mut a = vec![f];
                a.extend(list(args));
                let post = operands(
                    &mut out,
                    &mut a,
                    &[],
                    Some(dst),
                    false,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let f = a[0];
                let args = push_ops(&a[1..]);
                write_dst(&mut out, dst, &a, &lent, &mut scratch_reg, |dst| {
                    Instr::Apply { dst, f, args }
                });
                out.extend(post);
            }
            Instr::TailApply { f, args } => {
                let mut a = vec![f];
                a.extend(list(args));
                operands(
                    &mut out,
                    &mut a,
                    &[],
                    None,
                    true,
                    &lent,
                    &plainish,
                    &all_lent,
                    &fresh,
                );
                let f = a[0];
                let args = push_ops(&a[1..]);
                out.push(Instr::TailApply { f, args });
            }
            Instr::Move { dst, src }
            | Instr::Take { dst, src }
            | Instr::Field { dst, src, .. }
            | Instr::NatPred { dst, src }
            | Instr::IntOfNat { dst, src }
            | Instr::IntNegSucc { dst, src }
            | Instr::TextChars { dst, src } => {
                let read = [src];
                write_dst(&mut out, dst, &read, &lent, &mut scratch_reg, |d| {
                    with_dst(instr, d)
                });
            }
            Instr::Drop { .. } => out.push(instr),
            Instr::Const { dst, .. }
            | Instr::Captured { dst, .. }
            | Instr::Global { dst, .. }
            | Instr::StaticClosure { dst, .. } => {
                forget_dst(&mut out, dst);
                out.push(instr);
            }
            Instr::Switch { .. }
            | Instr::NatCase { .. }
            | Instr::IntCase { .. }
            | Instr::NumSwitch { .. }
            | Instr::JumpIfFalse { .. }
            | Instr::Test { .. }
            | Instr::Jump { .. }
            | Instr::Unreachable => out.push(instr),
            Instr::Peek { .. } | Instr::Lend { .. } | Instr::Forget { .. } | Instr::Own { .. } => {
                panic!("internal error: bytecode lent twice")
            }
        }
    }
    start[n] = u32::try_from(out.len()).expect("instructions fit");
    let at = |t: u32| start[t as usize];
    for i in &mut out {
        match i {
            Instr::Jump { target }
            | Instr::JumpIfFalse { target, .. }
            | Instr::Test { target, .. } => *target = at(*target),
            Instr::NatCase { zero, .. } => *zero = at(*zero),
            Instr::IntCase { neg, .. } => *neg = at(*neg),
            _ => {}
        }
    }
    for table in &mut code.tables {
        for t in table.iter_mut() {
            *t = at(*t);
        }
    }
    for table in &mut code.num_tables {
        for (_, t) in table.small.iter_mut() {
            *t = at(*t);
        }
        for (_, t) in table.big.iter_mut() {
            *t = at(*t);
        }
        table.default = at(table.default);
    }
    code.instrs = out;
    code.ops = new_ops;
    code.regs = regs.get();
    true
}

/// `instr` (one with a destination and one source) writing `dst` instead.
fn with_dst(instr: Instr, dst: Reg) -> Instr {
    match instr {
        Instr::Move { src, .. } => Instr::Move { dst, src },
        Instr::Take { src, .. } => Instr::Take { dst, src },
        Instr::Field { src, i, .. } => Instr::Field { dst, src, i },
        Instr::NatPred { src, .. } => Instr::NatPred { dst, src },
        Instr::IntOfNat { src, .. } => Instr::IntOfNat { dst, src },
        Instr::IntNegSucc { src, .. } => Instr::IntNegSucc { dst, src },
        Instr::TextChars { src, .. } => Instr::TextChars { dst, src },
        other => unreachable!("{other:?} has no single source"),
    }
}

/// Emits an instruction that writes `dst` and reads `read` (operands as
/// in [`Code::ops`]): if `dst` holds a lent value, it ends first, or, if
/// the instruction still reads it (without moving it), after, the result
/// going through a scratch register.
fn write_dst(
    out: &mut Vec<Instr>,
    dst: Reg,
    read: &[Reg],
    lent: &dyn Fn(Reg) -> bool,
    scratch: &mut dyn FnMut() -> Reg,
    make: impl Fn(Reg) -> Instr,
) {
    if !lent(dst) {
        out.push(make(dst));
        return;
    }
    let reads_kept = read.contains(&dst);
    let reads_moved = read.contains(&(dst | MOVE));
    if reads_kept {
        let t = scratch();
        out.push(make(t));
        out.push(Instr::Forget { reg: dst });
        out.push(Instr::Take { dst, src: t });
    } else {
        if !reads_moved {
            out.push(Instr::Forget { reg: dst });
        }
        out.push(make(dst));
    }
}

/// Rewrites the operands `a` of a call (`lend[j]`: position `j` is a
/// borrowed parameter) or of any other instruction that takes values
/// (`lend` empty), emitting what goes before it; returns what goes after.
/// `tail`: the instruction ends the frame, so every lent register still
/// held must be passed on (moved) or forgotten first.
#[allow(clippy::too_many_arguments)]
fn operands(
    out: &mut Vec<Instr>,
    a: &mut [Reg],
    lend: &[bool],
    dst: Option<Reg>,
    tail: bool,
    lent: &dyn Fn(Reg) -> bool,
    plainish: &dyn Fn(Reg) -> bool,
    all_lent: &dyn Fn() -> Vec<Reg>,
    fresh: &dyn Fn() -> Reg,
) -> Vec<Instr> {
    let lends_at = |j: usize| lend.get(j) == Some(&true);
    // A lent register lent at one position and moved to an owned one (`g x
    // x`, `g` borrowing its first parameter and owning its second): the
    // owned position gets a copy, and the loan stays backed by the owner
    // further down the stack. In a tail call the copy is a new register
    // (the frame ends, so the loan is passed on moved); otherwise the
    // owned position reads the register without moving it, and the
    // register is forgotten after the call.
    let mut forget_after: Vec<Reg> = Vec::new();
    let both: Vec<Reg> = (0..a.len())
        .filter(|&j| !lends_at(j) && a[j] & MOVE != 0 && lent(a[j] & !MOVE))
        .map(|j| a[j] & !MOVE)
        .filter(|r| (0..a.len()).any(|i| lends_at(i) && a[i] & !MOVE == *r))
        .collect();
    for r in both {
        for (j, x) in a.iter_mut().enumerate() {
            if !lends_at(j) && *x == r | MOVE {
                if tail {
                    let t = fresh();
                    out.push(Instr::Lend { dst: t, src: r });
                    out.push(Instr::Own { reg: t });
                    *x = t | MOVE;
                } else {
                    *x = r;
                    if dst != Some(r) && !forget_after.contains(&r) {
                        forget_after.push(r);
                    }
                }
            }
        }
    }
    if tail {
        for r in all_lent() {
            match a.iter().rposition(|x| *x & !MOVE == r) {
                Some(last) => a[last] |= MOVE,
                None => out.push(Instr::Forget { reg: r }),
            }
        }
    }
    // A lent value moved to an owned position becomes owned first.
    let mut owned: Vec<Reg> = Vec::new();
    for (j, r) in a.iter().enumerate() {
        let reg = r & !MOVE;
        if !lends_at(j) && r & MOVE != 0 && lent(reg) && !owned.contains(&reg) {
            owned.push(reg);
            out.push(Instr::Own { reg });
        }
    }
    // An owned value at a borrowed position stays in this frame for the
    // call: not moved anywhere in it, and dropped after.
    let mut post: Vec<Instr> = forget_after
        .into_iter()
        .map(|reg| Instr::Forget { reg })
        .collect();
    if tail {
        return post;
    }
    let kept: Vec<Reg> = a
        .iter()
        .enumerate()
        .filter(|(j, r)| lends_at(*j) && !lent(**r) && !plainish(**r))
        .map(|(_, r)| r & !MOVE)
        .collect();
    let mut dropped: Vec<Reg> = Vec::new();
    for r in a.iter_mut() {
        let reg = *r & !MOVE;
        if *r & MOVE != 0 && kept.contains(&reg) {
            *r = reg;
            if !dropped.contains(&reg) {
                dropped.push(reg);
                if dst != Some(reg) {
                    post.push(Instr::Drop { reg });
                }
            }
        }
    }
    post
}

// ------------------------------------------------------------------- check

/// Checks that a rewritten body keeps the discipline: a lent register is
/// never moved where values are kept, dropped, unpacked, reused, returned
/// or overwritten, and is passed on or forgotten before the frame ends;
/// `Peek`, `Lend` and `Own` read only lent registers; and a call lends an
/// owned register only if it keeps it (a tail call never does, except a
/// plain value). The first violation, if any.
pub fn check<'f>(
    code: &Code,
    callee: &dyn Fn(u32) -> &'f [bool],
    plain: &[bool],
) -> Result<(), String> {
    let mut err: Option<String> = None;
    let mut met: Option<String> = None;
    let ok = forward(
        code,
        entry_state(code, &code.borrowed),
        plain,
        |pc, s| {
            if err.is_none()
                && let Err(e) = check_one(code, &code.instrs[pc], s, callee)
            {
                err = Some(format!("at {pc} ({:?}): {e}", code.instrs[pc]));
            }
        },
        |pc, r, _| {
            met.get_or_insert_with(|| {
                format!("at {pc}: register {r} lent on one path, owned on another")
            });
        },
    );
    if !ok && code.borrowed.iter().any(|b| *b) {
        return Err("a borrowing body jumps back".into());
    }
    match met.or(err) {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

fn check_one<'f>(
    code: &Code,
    instr: &Instr,
    s: &[St],
    callee: &dyn Fn(u32) -> &'f [bool],
) -> Result<(), String> {
    let lent = |r: Reg| matches!(s[(r & !MOVE) as usize], St::Lent { .. });
    let not_lent = |r: Reg, what: &str| {
        if lent(r) {
            Err(format!("{what} of lent register {}", r & !MOVE))
        } else {
            Ok(())
        }
    };
    // A value-taking operand list: nothing lent moved.
    let kept = |o: &[Reg], lend: &[bool]| -> Result<(), String> {
        for (j, r) in o.iter().enumerate() {
            if lend.get(j) != Some(&true) && r & MOVE != 0 {
                not_lent(*r, "move to an owned position")?;
            }
        }
        Ok(())
    };
    let dst_free = |d: Reg| not_lent(d, "write over");
    let ends = |read: &[Reg]| -> Result<(), String> {
        for r in 0..s.len() as Reg {
            if lent(r) && !read.contains(&(r | MOVE)) {
                return Err(format!("frame ends holding lent register {r}"));
            }
        }
        Ok(())
    };
    match *instr {
        Instr::Move { dst, src } | Instr::Take { dst, src } => {
            not_lent(src, "copy or move")?;
            dst_free(dst)
        }
        Instr::Drop { reg } => not_lent(reg, "drop"),
        Instr::Field { dst, src, .. } => {
            not_lent(src, "counted field")?;
            dst_free(dst)
        }
        Instr::Unpack { src, fields, token } => {
            not_lent(src, "unpack")?;
            for p in ops(code, fields).as_chunks::<2>().0 {
                if p[1] != NO_REG {
                    dst_free(p[1])?;
                }
            }
            if token != NO_REG {
                dst_free(token)?;
            }
            Ok(())
        }
        Instr::DropReuse { src, token } => {
            not_lent(src, "reuse")?;
            dst_free(token)
        }
        Instr::Peek { dst, src, .. } => {
            if !lent(src) {
                return Err("peek of an owned register".into());
            }
            if dst != src { dst_free(dst) } else { Ok(()) }
        }
        Instr::Lend { dst, src } => {
            if !lent(src) {
                return Err("lend of an owned register".into());
            }
            dst_free(dst)
        }
        Instr::Own { reg } => {
            if lent(reg) {
                Ok(())
            } else {
                Err("own of a register not lent".into())
            }
        }
        Instr::Forget { reg } => match s[reg as usize] {
            St::Lent { .. } | St::Empty => Ok(()),
            _ => Err("forget of an owned register".into()),
        },
        Instr::Return { src } => {
            not_lent(src, "return")?;
            ends(&[src | MOVE])
        }
        Instr::Call { g, args, .. } | Instr::TailCall { g, args } => {
            let tail = matches!(instr, Instr::TailCall { .. });
            let o = ops(code, args);
            let lend = callee(g);
            kept(o, lend)?;
            for (j, r) in o.iter().enumerate() {
                let reg = r & !MOVE;
                if lend.get(j) == Some(&true) && owned(s[reg as usize]) {
                    if tail {
                        return Err(format!("tail call lends owned register {reg}"));
                    }
                    if o.contains(&(reg | MOVE)) {
                        return Err(format!("call lends owned register {reg} and moves it"));
                    }
                }
            }
            match *instr {
                Instr::Call { dst, .. } => dst_free(dst),
                _ => ends(o),
            }
        }
        Instr::Prim { dst, args, .. }
        | Instr::Pap { dst, args, .. }
        | Instr::Closure { dst, args, .. }
        | Instr::Ctor { dst, args, .. } => {
            kept(ops(code, args), &[])?;
            dst_free(dst)
        }
        Instr::CtorReuse {
            dst, args, token, ..
        } => {
            kept(ops(code, args), &[])?;
            not_lent(token, "reuse")?;
            dst_free(dst)
        }
        Instr::TailPrim { args, .. } => {
            let o = ops(code, args);
            kept(o, &[])?;
            ends(o)
        }
        Instr::Apply { dst, f, args } => {
            kept(&[f], &[])?;
            kept(ops(code, args), &[])?;
            dst_free(dst)
        }
        Instr::TailApply { f, args } => {
            let mut o = vec![f];
            o.extend_from_slice(ops(code, args));
            kept(&o, &[])?;
            ends(&o)
        }
        Instr::Const { dst, .. }
        | Instr::Captured { dst, .. }
        | Instr::Global { dst, .. }
        | Instr::StaticClosure { dst, .. }
        | Instr::NatPred { dst, .. }
        | Instr::IntOfNat { dst, .. }
        | Instr::IntNegSucc { dst, .. }
        | Instr::TextChars { dst, .. } => dst_free(dst),
        Instr::Switch { .. }
        | Instr::NatCase { .. }
        | Instr::IntCase { .. }
        | Instr::NumSwitch { .. }
        | Instr::JumpIfFalse { .. }
        | Instr::Test { .. }
        | Instr::Jump { .. }
        | Instr::Unreachable => Ok(()),
    }
}

#[cfg(test)]
mod tests;
