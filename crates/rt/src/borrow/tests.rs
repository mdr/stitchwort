//! The inference on small bytecode examples, one rule at a time.

use super::*;
use crate::code::{Code, Instr, MOVE, NO_REG, Ops};

#[derive(Default)]
struct B {
    instrs: Vec<Instr>,
    ops: Vec<Reg>,
}

impl B {
    fn ops(&mut self, regs: &[Reg]) -> Ops {
        let start = self.ops.len() as u32;
        self.ops.extend_from_slice(regs);
        Ops {
            start,
            len: regs.len() as u32,
        }
    }

    fn push(mut self, i: Instr) -> Self {
        self.instrs.push(i);
        self
    }

    fn call(mut self, dst: Reg, g: u32, args: &[Reg]) -> Self {
        let args = self.ops(args);
        self.push(Instr::Call { dst, g, args })
    }

    fn tail(mut self, g: u32, args: &[Reg]) -> Self {
        let args = self.ops(args);
        self.push(Instr::TailCall { g, args })
    }

    fn ctor(mut self, dst: Reg, args: &[Reg]) -> Self {
        let args = self.ops(args);
        self.push(Instr::Ctor { dst, tag: 1, args })
    }

    fn unpack(mut self, src: Reg, fields: &[(u32, Reg)], token: Reg) -> Self {
        let flat: Vec<Reg> = fields.iter().flat_map(|(i, r)| [*i, *r]).collect();
        let fields = self.ops(&flat);
        self.push(Instr::Unpack { src, fields, token })
    }

    fn code(self, params: u32, regs: u32) -> Code {
        Code {
            instrs: self.instrs,
            ops: self.ops,
            tables: Vec::new(),
            num_tables: Vec::new(),
            regs,
            params,
            borrowed: Box::default(),
        }
    }
}

fn run(codes: &[Code], used: &[bool]) -> Inference {
    let funcs: Vec<Option<Func>> = codes
        .iter()
        .zip(used)
        .map(|(code, value_used)| {
            Some(Func {
                code,
                fixed: Fixed::No,
                value_used: *value_used,
                plain_consts: &[true],
            })
        })
        .collect();
    infer(&funcs, &[], &[true])
}

fn one(code: Code) -> Inference {
    run(&[code], &[false])
}

/// `get key tree`: a read-only walk, matching on the tree and tail-calling
/// itself on a field.
fn walk() -> Code {
    B::default()
        .push(Instr::NatCase { src: 0, zero: 3 })
        .unpack(1, &[(0, 2)], NO_REG)
        .tail(0, &[0, 2 | MOVE])
        .push(Instr::Const { dst: 3, k: 0 })
        .push(Instr::Return { src: 3 })
        .code(2, 4)
}

#[test]
fn a_read_only_walk_borrows_everything() {
    let inf = one(walk());
    assert_eq!(inf.borrowed[0], [true, true]);
}

/// A caller of global 0 with one argument that hands it an owned value
/// at its last use: its own parameter, which it owns (run it as a
/// function used as a value).
fn feeding() -> Code {
    B::default()
        .call(1, 0, &[MOVE])
        .push(Instr::Return { src: 1 })
        .code(1, 2)
}

/// The same, passing a value it keeps (and so would increment anyway).
fn keeping() -> Code {
    B::default()
        .call(1, 0, &[0])
        .ctor(2, &[MOVE, 1 | MOVE])
        .push(Instr::Return { src: 2 })
        .code(1, 3)
}

#[test]
fn a_parameter_stored_in_a_constructor_is_owned() {
    let stored = || {
        B::default()
            .ctor(1, &[0])
            .push(Instr::Return { src: 1 })
            .code(1, 2)
    };
    let inf = run(&[stored(), feeding()], &[false, true]);
    assert_eq!(inf.borrowed[0], [false]);
    assert_eq!(inf.reason[0][0], Some(Reason::Stored));
    // Every caller keeps what it passes: it is incremented where it is
    // stored instead of at the call.
    let inf = run(&[stored(), keeping()], &[false, false]);
    assert_eq!(inf.borrowed[0], [true]);
}

#[test]
fn a_returned_parameter_is_owned() {
    let returned = B::default().push(Instr::Return { src: 0 }).code(1, 1);
    let inf = run(&[returned, feeding()], &[false, true]);
    assert_eq!(inf.borrowed[0], [false]);
    assert_eq!(inf.reason[0][0], Some(Reason::Returned));
}

/// A caller handing over its last reference makes the parameter owned,
/// even if it never escapes (the callee may free it as it goes); one
/// handing over a copy, whose original stays live, does not.
#[test]
fn a_parameter_fed_its_only_reference_is_owned() {
    let fed = run(&[walk_param(), feeding()], &[false, true]);
    assert_eq!(fed.reason[0][0], Some(Reason::Fed));
    let copy = B::default()
        .push(Instr::Move { dst: 1, src: 0 })
        .call(2, 0, &[1 | MOVE])
        .ctor(3, &[MOVE, 2 | MOVE])
        .push(Instr::Return { src: 3 })
        .code(1, 4);
    let inf = run(&[walk_param(), copy], &[false, true]);
    assert_eq!(inf.borrowed[0], [true]);
}

/// A value its caller has just made is likely unique: the callee owns it,
/// to free it as it goes.
#[test]
fn a_parameter_given_a_fresh_value_is_owned() {
    let fresh = B::default()
        .ctor(1, &[])
        .call(2, 0, &[1 | MOVE])
        .push(Instr::Return { src: 2 })
        .code(1, 3);
    let inf = run(&[walk_param(), fresh], &[false, false]);
    assert_eq!(inf.reason[0][0], Some(Reason::Fresh));
}

#[test]
fn a_field_stored_or_returned_leaves_its_parent_borrowed() {
    let code = B::default()
        .push(Instr::Field {
            dst: 1,
            src: 0,
            i: 0,
        })
        .ctor(2, &[1])
        .push(Instr::Return { src: 2 })
        .code(1, 3);
    assert_eq!(one(code).borrowed[0], [true]);
    let code = B::default()
        .push(Instr::Field {
            dst: 1,
            src: 0,
            i: 0,
        })
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert_eq!(one(code).borrowed[0], [true]);
}

/// `keep x = Ctor x` (owned: used as a value), and a caller `f p = keep p`
/// or `f p = keep p.0`.
#[test]
fn a_value_passed_to_an_owned_parameter_is_owned() {
    let keep = B::default()
        .ctor(1, &[0])
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    let direct = B::default()
        .call(1, 0, &[0])
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    let feeds_direct = B::default()
        .call(1, 1, &[MOVE])
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    let inf = run(&[keep, direct, feeds_direct], &[true, false, true]);
    assert_eq!(inf.borrowed[1], [false]);
    assert_eq!(inf.reason[1][0], Some(Reason::PassedOwned));

    let keep = B::default()
        .ctor(1, &[0])
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    let via_field = B::default()
        .push(Instr::Field {
            dst: 1,
            src: 0,
            i: 0,
        })
        .call(2, 0, &[1 | MOVE])
        .push(Instr::Return { src: 2 })
        .code(1, 3);
    // Without the note's O6: the field is incremented where it goes, and
    // its parent stays borrowed.
    let inf = run(&[keep, via_field], &[true, false]);
    assert_eq!(inf.borrowed[1], [true]);
}

#[test]
fn a_value_passed_to_a_borrowed_parameter_stays_borrowed() {
    let inf = run(
        &[
            walk(),
            B::default()
                .call(1, 0, &[0, 0])
                .push(Instr::Return { src: 1 })
                .code(1, 2),
        ],
        &[false, false],
    );
    assert_eq!(inf.borrowed[1], [true]);
}

#[test]
fn a_cell_that_is_reused_is_owned() {
    let code = B::default()
        .unpack(0, &[(0, 1)], 2)
        .push(Instr::Return { src: 1 })
        .code(1, 3);
    let inf = one(code);
    assert_eq!(inf.borrowed[0], [false]);
    assert_eq!(inf.reason[0][0], Some(Reason::Reused));
}

/// Two functions that tail-call each other, one passing a fresh value:
/// the callee's parameter must be owned (O4), since the caller couldn't
/// drop it after the call.
#[test]
fn mutual_recursion_with_an_owned_tail_argument() {
    // even x = odd (Ctor x'): a fresh value; odd y = even y.
    let even = B::default()
        .push(Instr::NatCase { src: 0, zero: 3 })
        .ctor(1, &[])
        .tail(1, &[1 | MOVE])
        .push(Instr::Const { dst: 2, k: 0 })
        .push(Instr::Return { src: 2 })
        .code(1, 3);
    let odd = B::default().tail(0, &[MOVE]).code(1, 1);
    let inf = run(&[even, odd], &[false, false]);
    assert_eq!(inf.group[0], inf.group[1]);
    assert_eq!(inf.borrowed[1], [false]);
    assert_eq!(inf.reason[1][0], Some(Reason::TailOwned));
    // `even`'s own parameter is only tested, and `odd` passes its owned
    // parameter on to it: so it too is owned, through the cycle.
    assert_eq!(inf.borrowed[0], [false]);
}

#[test]
fn a_lent_tail_argument_keeps_the_loop_borrowed() {
    let a = B::default().tail(1, &[0]).code(1, 1);
    let b = B::default().tail(0, &[0]).code(1, 1);
    let inf = run(&[a, b], &[false, false]);
    assert_eq!(inf.borrowed, [vec![true], vec![true]]);
}

/// `f` tail-calls `g` (another group) with a fresh value: `g`'s parameter
/// is owned (O8).
#[test]
fn an_owned_tail_argument_from_another_group() {
    let f = B::default().ctor(1, &[]).tail(1, &[1 | MOVE]).code(1, 2);
    let inf = run(&[f, walk_param()], &[false, false]);
    assert_eq!(inf.reason[1][0], Some(Reason::TailAcross));
}

fn walk_param() -> Code {
    B::default()
        .push(Instr::Field {
            dst: 1,
            src: 0,
            i: 0,
        })
        .push(Instr::Return { src: 1 })
        .code(1, 2)
}

#[test]
fn a_function_used_as_a_value_is_owned() {
    let inf = run(&[walk_param()], &[true]);
    assert_eq!(inf.reason[0][0], Some(Reason::ValueUse));
}

#[test]
fn a_loop_with_holes_is_left_owned() {
    use crate::ir::HoleOp;
    let mut b = B::default();
    let args = b.ops(&[]);
    let code = b
        .push(Instr::Prim {
            dst: 1,
            op: PrimOp::Hole(HoleOp::New),
            args,
        })
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert_eq!(one(code).borrowed[0], [false]);
}

/// A tail call that passes a tag loaded from a constant needs no drop
/// afterwards, so it doesn't make the callee's parameter owned.
#[test]
fn a_plain_constant_tail_argument_leaves_the_callee_borrowed() {
    let f = B::default()
        .push(Instr::Const { dst: 1, k: 0 })
        .tail(1, &[1 | MOVE])
        .code(1, 2);
    let inf = run(&[f, walk_param()], &[false, false]);
    assert_eq!(inf.borrowed[1], [true]);
}

/// A register that holds a field of the parameter on one path and an owned
/// value on the other, where the paths meet: the parameter is owned, since
/// whoever reads the register after can't know whether to drop it.
#[test]
fn lent_and_owned_meeting_make_the_parameter_owned() {
    let code = B::default()
        .push(Instr::NatCase { src: 1, zero: 3 })
        .push(Instr::Field {
            dst: 2,
            src: 0,
            i: 0,
        })
        .push(Instr::Jump { target: 4 })
        .ctor(2, &[])
        .push(Instr::Return { src: 2 })
        .code(2, 3);
    let inf = one(code);
    assert_eq!(inf.borrowed[0], [false, true]);
    assert_eq!(inf.reason[0][0], Some(Reason::Merge));
}

/// The callers' flags, by global index, for [`rewrite`] and [`check`].
fn rewritten(mut code: Code, own: &[bool], callees: &[&[bool]]) -> Code {
    code.borrowed = own.into();
    let callee = |g: u32| -> &[bool] { callees.get(g as usize).copied().unwrap_or(&[]) };
    rewrite(&mut code, &callee, &[true]);
    if let Err(e) = check(&code, &callee, &[true]) {
        panic!("{e}: {:?}", code.instrs);
    }
    code
}

fn count(code: &Code, f: impl Fn(&Instr) -> bool) -> usize {
    code.instrs.iter().filter(|i| f(i)).count()
}

/// The walk lends: its match reads the node's fields without counting, its
/// tail call passes the key and the subtree on lent, and both ends of the
/// frame forget what is still lent.
#[test]
fn a_borrowed_walk_reads_without_counting() {
    let code = rewritten(walk(), &[true, true], &[&[true, true]]);
    assert_eq!(count(&code, |i| matches!(i, Instr::Unpack { .. })), 0);
    assert_eq!(count(&code, |i| matches!(i, Instr::Peek { .. })), 1);
    assert_eq!(count(&code, |i| matches!(i, Instr::Own { .. })), 0);
    let Instr::NatCase { zero, .. } = code.instrs[0] else {
        panic!("{:?}", code.instrs)
    };
    assert!(matches!(code.instrs[zero as usize], Instr::Const { .. }));
    let tail = code
        .instrs
        .iter()
        .find_map(|i| match i {
            Instr::TailCall { args, .. } => Some(ops(&code, *args).to_vec()),
            _ => None,
        })
        .expect("a tail call");
    assert_eq!(tail, [MOVE, 2 | MOVE]);
}

/// `f p = Some p.0`: the field is incremented once, where it is stored.
#[test]
fn an_escaping_field_is_owned_once() {
    let code = B::default()
        .push(Instr::Field {
            dst: 1,
            src: 0,
            i: 0,
        })
        .ctor(2, &[1 | MOVE])
        .push(Instr::Return { src: 2 })
        .code(1, 3);
    let code = rewritten(code, &[true], &[]);
    assert_eq!(count(&code, |i| matches!(i, Instr::Own { reg: 1 })), 1);
    assert_eq!(count(&code, |i| matches!(i, Instr::Forget { reg: 0 })), 1);
}

/// An owned value moved to a borrowed parameter stays with the caller,
/// which drops it after the call (unless the result goes in its register).
#[test]
fn an_owned_value_lent_is_dropped_after_the_call() {
    let caller = |dst| {
        B::default()
            .ctor(1, &[])
            .call(dst, 0, &[0, 1 | MOVE])
            .push(Instr::Return { src: dst })
            .code(1, 3)
    };
    let code = rewritten(caller(2), &[], &[&[true, true]]);
    let Instr::Call { args, .. } = code.instrs[1] else {
        panic!("{:?}", code.instrs)
    };
    assert_eq!(ops(&code, args), [0, 1]);
    assert!(matches!(code.instrs[2], Instr::Drop { reg: 1 }));
    let code = rewritten(caller(1), &[], &[&[true, true]]);
    assert_eq!(count(&code, |i| matches!(i, Instr::Drop { .. })), 0);
}

fn rejected(code: Code, own: &[bool], callees: &[&[bool]]) -> String {
    let mut code = code;
    code.borrowed = own.into();
    let callee = |g: u32| -> &[bool] { callees.get(g as usize).copied().unwrap_or(&[]) };
    check(&code, &callee, &[true]).expect_err("rejected")
}

#[test]
fn the_check_rejects_counting_a_lent_value() {
    let unpack = B::default()
        .unpack(0, &[(0, 1)], NO_REG)
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert!(rejected(unpack, &[true], &[]).contains("unpack"));
    let returned = B::default().push(Instr::Return { src: 0 }).code(1, 1);
    assert!(rejected(returned, &[true], &[]).contains("return"));
    let stored = B::default()
        .ctor(1, &[MOVE])
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert!(rejected(stored, &[true], &[]).contains("owned position"));
    let reused = B::default()
        .push(Instr::DropReuse { src: 0, token: 1 })
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert!(rejected(reused, &[true], &[]).contains("reuse"));
    let dropped = B::default()
        .push(Instr::Drop { reg: 0 })
        .push(Instr::Const { dst: 1, k: 0 })
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert!(rejected(dropped, &[true], &[]).contains("drop"));
}

#[test]
fn the_check_rejects_a_frame_ending_with_a_loan() {
    let kept = B::default()
        .push(Instr::Const { dst: 1, k: 0 })
        .push(Instr::Return { src: 1 })
        .code(1, 2);
    assert!(rejected(kept, &[true], &[]).contains("frame ends"));
    // A tail call can't lend what its own frame owns.
    let fresh = B::default().ctor(1, &[]).tail(0, &[1 | MOVE]).code(1, 2);
    assert!(rejected(fresh, &[], &[&[true]]).contains("tail call lends"));
}
