//! The counter of stage B0 (cargo feature `borrow-counts`): the machine
//! runs the program as it always does, and a shadow of every register says
//! whether the inferred borrowing would hold that value without a count.
//! The shadow counts the reference-count operations that borrowing would
//! take away, and those it would add.
//!
//! A register's shadow class:
//!
//! - `OWNED`: held as today.
//! - `LENT`: a borrowed parameter that its caller passed with a copy (today
//!   an increment at the call and a decrement when the callee lets go), or
//!   a field read from a lent value (today an increment at the read and a
//!   decrement at the drop). Borrowing removes both.
//! - `PAID`: lent, but the reference it stands for was handed over by the
//!   caller's last use, or came out of a cell that was uniquely held. The
//!   owner would drop it after the call instead of the callee, so letting
//!   go costs nothing less. Moving such a value on (into a constructor, say)
//!   would cost an increment now and a decrement when the owner frees the
//!   cell: borrowing adds a pair there.
//!
//! Operations are counted only for values that hold a reference
//! ([`Value::owns`]). The report is on standard error when the machine is
//! dropped and `STITCHWORT_BORROW_COUNTS` is set; the variant is chosen by
//! `STITCHWORT_BORROW_VARIANT` (`b1`, the default, `b2`, `b1-no-o6`, `b2-no-o6`); and
//! `STITCHWORT_BORROW_DUMP` lists every function with a borrowed parameter.

use std::rc::Rc;

use crate::code::{Code, Image, Instr, MOVE, NO_REG, Reg};
use crate::ir::{GlobalKind, Program, Reuse};
use crate::value::Value;

use super::{Fixed, Func, Inference, Reason, Variant};

const OWNED: u8 = 0;
const LENT: u8 = 1;
const PAID: u8 = 2;

/// What the inference decided, for the machine to consult, by code.
#[derive(Default)]
pub struct BorrowInfo {
    /// Per code, per parameter: borrowed. Empty if none.
    pub flags: Vec<Box<[bool]>>,
    pub names: Vec<String>,
    pub variant: Option<Variant>,
}

pub fn variant_from_env() -> Variant {
    std::env::var("STITCHWORT_BORROW_VARIANT")
        .ok()
        .and_then(|v| Variant::parse(&v))
        .unwrap_or(Variant::B1)
}

/// Runs the inference over a compiled program.
pub fn for_image(program: &Program, image: &Image) -> BorrowInfo {
    let variant = variant_from_env();
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
            Some(Func {
                code,
                fixed: if matches!(global.reuse, Reuse::Copy { .. }) {
                    Fixed::Last
                } else {
                    Fixed::No
                },
                value_used: used[g],
                plain_consts: &plain,
            })
        })
        .collect();
    let inference = super::infer(&funcs, variant);
    let mut info = BorrowInfo {
        flags: vec![Box::default(); image.codes.len()],
        names: vec![String::new(); image.codes.len()],
        variant: Some(variant),
    };
    for (g, code) in image.global_code.iter().enumerate() {
        if let Some(code) = *code {
            info.names[code as usize] = program.globals[g].name.to_string();
            if funcs[g].is_some() {
                info.flags[code as usize] = inference.borrowed[g].clone().into_boxed_slice();
            }
        }
    }
    if std::env::var_os("STITCHWORT_BORROW_COUNTS").is_some() {
        report_static(program, &funcs, &inference, variant);
    }
    info
}

fn report_static(program: &Program, funcs: &[Option<Func>], inf: &Inference, variant: Variant) {
    let s = inf.summary();
    eprintln!("borrow-static variant={}", variant.name());
    eprintln!(
        "borrow-static functions={} with_borrowed={} params={} borrowed={}",
        s.functions, s.with_borrowed, s.params, s.borrowed
    );
    for (i, r) in Reason::ALL.iter().enumerate() {
        eprintln!("borrow-static owned-by {}={}", r.name(), s.by_reason[i]);
    }
    if std::env::var_os("STITCHWORT_BORROW_DUMP").is_some() {
        for (g, f) in funcs.iter().enumerate() {
            if let (Some(f), Ok(want)) = (f, std::env::var("STITCHWORT_BORROW_DUMP"))
                && want.len() > 1
                && program.globals[g].name.contains(&want)
            {
                eprintln!(
                    "borrow-code {} reasons={:?}",
                    program.globals[g].name, inf.reason[g]
                );
                for (pc, i) in f.code.instrs.iter().enumerate() {
                    let callee = match i {
                        Instr::Call { g, .. } | Instr::TailCall { g, .. } => {
                            format!(
                                "   -> {} {:?}",
                                program.globals[*g as usize].name, inf.borrowed[*g as usize]
                            )
                        }
                        _ => String::new(),
                    };
                    eprintln!("  {pc}: {i:?}{callee}");
                }
                eprintln!(
                    "  ops={:?}",
                    f.code
                        .ops
                        .iter()
                        .map(|r| if r & MOVE != 0 {
                            format!("{}!", r & !MOVE)
                        } else {
                            r.to_string()
                        })
                        .collect::<Vec<_>>()
                );
            }
            if f.is_some() && inf.borrowed[g].iter().any(|b| *b) {
                let bits: String = inf.borrowed[g]
                    .iter()
                    .map(|b| if *b { 'B' } else { 'o' })
                    .collect();
                eprintln!("borrow-fn {} {bits}", program.globals[g].name);
            }
        }
    }
}

/// The shadow and its counts.
#[derive(Default)]
pub struct Shadow {
    class: Vec<u8>,
    c: Counts,
    by_code: Vec<[i64; 4]>,
    cur: usize,
    info: Rc<BorrowInfoHandle>,
}

#[derive(Default)]
struct BorrowInfoHandle {
    names: Vec<String>,
}

#[derive(Default, Debug)]
struct Counts {
    /// Copies and drops of registers that borrowing takes away or adds,
    /// of any value (index 0: each costs the check that the value holds a
    /// reference) and of those that hold one (index 1: which also take a
    /// count).
    inc_saved: [i64; 2],
    dec_saved: [i64; 2],
    inc_added: [i64; 2],
    dec_added: [i64; 2],
    /// Reference-count operations the machine makes on registers (operand
    /// copies, field reads, drops, frame exits), the baseline the savings
    /// are of.
    base_inc: u64,
    base_dec: u64,
    calls: u64,
    lent_entries: u64,
    paid_entries: u64,
    owned_copy_tail_calls: u64,
}

impl Shadow {
    fn cls(&self, i: usize) -> u8 {
        self.class.get(i).copied().unwrap_or(OWNED)
    }

    fn set(&mut self, i: usize, c: u8) {
        if i >= self.class.len() {
            if c == OWNED {
                return;
            }
            self.class.resize(i + 1, OWNED);
        }
        self.class[i] = c;
    }

    fn inc_saved(&mut self, n: i64, counted: bool) {
        self.c.inc_saved[0] += n;
        if counted {
            self.c.inc_saved[1] += n;
            self.by_code[self.cur][0] += n;
        }
    }

    fn dec_saved(&mut self, n: i64, counted: bool) {
        self.c.dec_saved[0] += n;
        if counted {
            self.c.dec_saved[1] += n;
            self.by_code[self.cur][1] += n;
        }
    }

    fn pair_added(&mut self, counted: bool) {
        self.c.inc_added[0] += 1;
        self.c.dec_added[0] += 1;
        if counted {
            self.c.inc_added[1] += 1;
            self.c.dec_added[1] += 1;
            self.by_code[self.cur][2] += 1;
            self.by_code[self.cur][3] += 1;
        }
    }

    /// `r` is read to keep it: moved out (`MOVE`) or copied.
    fn escape(&mut self, base: usize, regs: &[Value], rf: Reg) {
        let r = base + (rf & !MOVE) as usize;
        let counted = regs[r].owns();
        let moved = rf & MOVE != 0;
        let c = self.cls(r);
        if counted && !moved {
            self.c.base_inc += 1;
        }
        if moved && c == LENT {
            self.inc_saved(-1, counted);
        } else if moved && c == PAID {
            self.pair_added(counted);
        }
        if moved {
            self.set(r, OWNED);
        }
    }

    /// A register about to be written: what it held is dropped.
    fn overwrite(&mut self, i: usize, regs: &[Value]) {
        if self.cls(i) == LENT {
            self.dec_saved(1, regs[i].owns());
        }
        if regs[i].owns() {
            self.c.base_dec += 1;
        }
        self.set(i, OWNED);
    }

    /// The frame at `base` ends with `moved` registers taken out: whatever
    /// else it holds is dropped.
    fn leave(&mut self, base: usize, regs: &[Value], moved: &[usize]) {
        for (k, v) in regs.iter().enumerate().skip(base) {
            if !moved.contains(&k) {
                if v.owns() {
                    self.c.base_dec += 1;
                }
                if self.cls(k) == LENT {
                    self.dec_saved(1, v.owns());
                }
            }
        }
        self.class.truncate(base);
    }

    /// The classes of the arguments of a call of `callee`, by operand, and
    /// the credit for the copies it no longer needs. `tail`: the call
    /// replaces the frame.
    fn args(
        &mut self,
        info: &BorrowInfo,
        callee: usize,
        base: usize,
        regs: &[Value],
        ops: &[Reg],
        tail: bool,
    ) -> Vec<u8> {
        let flags = &info.flags[callee];
        // A tail call that passes an owned value to a borrowed parameter
        // goes to the callee's owned copy (stage B2): everything owned.
        let owned_copy = tail
            && ops.iter().enumerate().any(|(j, rf)| {
                let r = base + (rf & !MOVE) as usize;
                flags.get(j) == Some(&true) && self.cls(r) == OWNED && regs[r].owns()
            });
        if owned_copy {
            self.c.owned_copy_tail_calls += 1;
        }
        let mut out = Vec::with_capacity(ops.len());
        for (j, rf) in ops.iter().enumerate() {
            let r = base + (rf & !MOVE) as usize;
            if flags.get(j) == Some(&true) && !owned_copy {
                let (c, moved, counted) = (self.cls(r), rf & MOVE != 0, regs[r].owns());
                let class = match (c, moved) {
                    (OWNED | PAID, true) => PAID,
                    (LENT, true) => LENT,
                    _ => LENT,
                };
                if !moved {
                    self.inc_saved(1, counted);
                    if counted {
                        self.c.base_inc += 1;
                    }
                }
                if counted {
                    if class == LENT {
                        self.c.lent_entries += 1;
                    } else {
                        self.c.paid_entries += 1;
                    }
                }
                if moved {
                    self.set(r, OWNED);
                }
                out.push(class);
            } else {
                self.escape(base, regs, *rf);
                out.push(OWNED);
            }
        }
        out
    }

    /// Called before each instruction the machine executes.
    pub fn hook(
        &mut self,
        image: &Image,
        code_ix: u32,
        base: usize,
        regs: &[Value],
        instr: &Instr,
    ) {
        let info = &image.borrow;
        if self.by_code.len() != image.codes.len() {
            self.by_code = vec![[0; 4]; image.codes.len()];
            self.info = Rc::new(BorrowInfoHandle {
                names: info.names.clone(),
            });
        }
        self.class.truncate(regs.len());
        self.cur = code_ix as usize;
        let code: &Code = &image.codes[code_ix as usize];
        let ops = |o: crate::code::Ops| &code.ops[o.start as usize..(o.start + o.len) as usize];
        match *instr {
            Instr::Move { dst, src } => {
                let (s, d) = (base + src as usize, base + dst as usize);
                let c = self.cls(s);
                let counted = regs[s].owns();
                if counted {
                    self.c.base_inc += 1;
                }
                self.overwrite(d, regs);
                if c != OWNED {
                    self.inc_saved(1, counted);
                    self.set(d, LENT);
                }
            }
            Instr::Take { dst, src } => {
                let (s, d) = (base + src as usize, base + dst as usize);
                let c = self.cls(s);
                self.overwrite(d, regs);
                self.set(s, OWNED);
                self.set(d, c);
            }
            Instr::Drop { reg } => {
                let r = base + reg as usize;
                if regs[r].owns() {
                    self.c.base_dec += 1;
                }
                if self.cls(r) == LENT {
                    self.dec_saved(1, regs[r].owns());
                }
                self.set(r, OWNED);
            }
            Instr::Const { dst, .. }
            | Instr::Captured { dst, .. }
            | Instr::Global { dst, .. }
            | Instr::StaticClosure { dst, .. }
            | Instr::NatPred { dst, .. }
            | Instr::IntOfNat { dst, .. }
            | Instr::IntNegSucc { dst, .. }
            | Instr::TextChars { dst, .. } => self.overwrite(base + dst as usize, regs),
            Instr::Call { dst, g, args } => {
                self.c.calls += 1;
                let callee = image.global_code[g as usize].expect("code") as usize;
                let classes = self.args(info, callee, base, regs, ops(args), false);
                self.overwrite(base + dst as usize, regs);
                let new_base = regs.len();
                self.class.truncate(new_base);
                for (j, c) in classes.into_iter().enumerate() {
                    self.set(new_base + j, c);
                }
            }
            Instr::TailCall { g, args } => {
                self.c.calls += 1;
                let callee = image.global_code[g as usize].expect("code") as usize;
                let o = ops(args);
                let classes = self.args(info, callee, base, regs, o, true);
                let moved: Vec<usize> = o
                    .iter()
                    .filter(|r| *r & MOVE != 0)
                    .map(|r| base + (r & !MOVE) as usize)
                    .collect();
                self.leave(base, regs, &moved);
                for (j, c) in classes.into_iter().enumerate() {
                    self.set(base + j, c);
                }
            }
            Instr::Prim { dst, op, args } => {
                if matches!(op, crate::ir::PrimOp::Effect(_)) || op.consumes() {
                    for r in ops(args) {
                        self.escape(base, regs, *r);
                    }
                }
                self.overwrite(base + dst as usize, regs);
            }
            Instr::TailPrim { args, .. } => {
                let o = ops(args);
                for r in o {
                    self.escape(base, regs, *r);
                }
                let moved: Vec<usize> = o.iter().map(|r| base + (r & !MOVE) as usize).collect();
                self.leave(base, regs, &moved);
            }
            Instr::Pap { dst, args, .. }
            | Instr::Closure { dst, args, .. }
            | Instr::Ctor { dst, args, .. } => {
                for r in ops(args) {
                    self.escape(base, regs, *r);
                }
                self.overwrite(base + dst as usize, regs);
            }
            Instr::CtorReuse {
                dst, args, token, ..
            } => {
                for r in ops(args) {
                    self.escape(base, regs, *r);
                }
                self.set(base + token as usize, OWNED);
                self.overwrite(base + dst as usize, regs);
            }
            Instr::Apply { dst, f, args } => {
                self.escape(base, regs, f);
                for r in ops(args) {
                    self.escape(base, regs, *r);
                }
                self.overwrite(base + dst as usize, regs);
            }
            Instr::TailApply { f, args } => {
                self.escape(base, regs, f);
                let o = ops(args);
                for r in o {
                    self.escape(base, regs, *r);
                }
                let mut moved: Vec<usize> = o
                    .iter()
                    .filter(|r| *r & MOVE != 0)
                    .map(|r| base + (r & !MOVE) as usize)
                    .collect();
                if f & MOVE != 0 {
                    moved.push(base + (f & !MOVE) as usize);
                }
                self.leave(base, regs, &moved);
            }
            Instr::Field { dst, src, .. } => {
                let (s, d) = (base + src as usize, base + dst as usize);
                // The field read is a copy of whatever the cell holds; its
                // register isn't known until the machine runs it, so count
                // it as a copy when the cell has a counted field (the
                // fields of constructors are mostly counted or not by
                // type, and the count is exact for the one read).
                let lent = self.cls(s) != OWNED;
                let counted = field_counted(&regs[s], instr);
                if counted {
                    self.c.base_inc += 1;
                }
                self.overwrite(d, regs);
                if lent {
                    self.inc_saved(1, counted);
                    self.set(d, LENT);
                }
            }
            Instr::Unpack { src, fields, token } => {
                let s = base + src as usize;
                let c = self.cls(s);
                let shared = match &regs[s] {
                    Value::Data(_, cell) => Rc::strong_count(&cell.0) > 1,
                    _ => true,
                };
                let pairs = ops(fields);
                if shared {
                    if regs[s].owns() {
                        self.c.base_dec += 1;
                    }
                    if c == LENT {
                        self.dec_saved(1, regs[s].owns());
                    }
                }
                for p in pairs.as_chunks::<2>().0 {
                    let d = base + p[1] as usize;
                    let counted = match &regs[s] {
                        Value::Data(_, cell) => cell[p[0] as usize].owns(),
                        _ => false,
                    };
                    if shared && counted {
                        self.c.base_inc += 1;
                    }
                    self.overwrite(d, regs);
                    if c != OWNED {
                        if shared {
                            self.inc_saved(1, counted);
                            self.set(d, LENT);
                        } else {
                            self.set(d, PAID);
                        }
                    }
                }
                self.set(s, OWNED);
                if token != NO_REG {
                    self.set(base + token as usize, OWNED);
                }
            }
            Instr::DropReuse { src, token } => {
                let s = base + src as usize;
                if regs[s].owns() {
                    self.c.base_dec += 1;
                }
                if self.cls(s) == LENT {
                    self.dec_saved(1, regs[s].owns());
                }
                self.set(s, OWNED);
                self.set(base + token as usize, OWNED);
            }
            Instr::Return { src } => {
                self.escape(base, regs, src | MOVE);
                self.leave(base, regs, &[base + src as usize]);
            }
            Instr::Switch { .. }
            | Instr::NatCase { .. }
            | Instr::IntCase { .. }
            | Instr::NumSwitch { .. }
            | Instr::JumpIfFalse { .. }
            | Instr::Test { .. }
            | Instr::Jump { .. }
            | Instr::Unreachable => {}
        }
    }
}

fn field_counted(src: &Value, instr: &Instr) -> bool {
    let Instr::Field { i, .. } = instr else {
        return false;
    };
    match src {
        Value::Data(_, cell) => cell[*i as usize].owns(),
        _ => false,
    }
}

impl Drop for Shadow {
    fn drop(&mut self) {
        if std::env::var_os("STITCHWORT_BORROW_COUNTS").is_none() || self.by_code.is_empty() {
            return;
        }
        let c = &self.c;
        // "any": every copy and drop of a lent value (each saves at least the
        // check that it holds a reference); "counted": of those that hold one.
        eprintln!(
            "borrow-dynamic net_inc_any={} net_dec_any={} net_inc={} net_dec={} \
             inc_saved={} dec_saved={} inc_added={} dec_added={} base_inc={} base_dec={}",
            c.inc_saved[0] - c.inc_added[0],
            c.dec_saved[0] - c.dec_added[0],
            c.inc_saved[1] - c.inc_added[1],
            c.dec_saved[1] - c.dec_added[1],
            c.inc_saved[1],
            c.dec_saved[1],
            c.inc_added[1],
            c.dec_added[1],
            c.base_inc,
            c.base_dec
        );
        eprintln!(
            "borrow-dynamic calls={} lent_entries={} paid_entries={} owned_copy_tail_calls={}",
            c.calls, c.lent_entries, c.paid_entries, c.owned_copy_tail_calls
        );
        let mut rows: Vec<(i64, usize)> = self
            .by_code
            .iter()
            .enumerate()
            .map(|(i, r)| (r[0] + r[1] - r[2] - r[3], i))
            .filter(|(n, _)| *n != 0)
            .collect();
        rows.sort_by_key(|r| std::cmp::Reverse(r.0));
        for (net, i) in rows.iter().take(25) {
            let r = self.by_code[*i];
            let name = &self.info.names[*i];
            eprintln!(
                "borrow-code net={net} inc_saved={} dec_saved={} added={} {}",
                r[0],
                r[1],
                r[2],
                if name.is_empty() { "(anonymous)" } else { name }
            );
        }
    }
}
