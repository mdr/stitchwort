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
        }
    }
}

fn run(codes: &[Code], used: &[bool], variant: Variant) -> Inference {
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
    infer(&funcs, variant)
}

fn one(code: Code) -> Inference {
    run(&[code], &[false], Variant::B1)
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

#[test]
fn a_parameter_stored_in_a_constructor_is_owned() {
    let code = B::default()
        .ctor(2, &[1])
        .push(Instr::Return { src: 2 })
        .code(2, 3);
    let inf = one(code);
    assert_eq!(inf.borrowed[0], [true, false]);
    assert_eq!(inf.reason[0][1], Some(Reason::Stored));
}

#[test]
fn a_returned_parameter_is_owned() {
    let code = B::default().push(Instr::Return { src: 0 }).code(1, 1);
    let inf = one(code);
    assert_eq!(inf.borrowed[0], [false]);
    assert_eq!(inf.reason[0][0], Some(Reason::Returned));
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

/// `keep x = Ctor x`, and a caller `f p = keep p` or `f p = keep p.0`.
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
    let inf = run(&[keep, direct], &[false, false], Variant::B1);
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
    let inf = run(&[keep, via_field], &[false, false], Variant::B1);
    assert_eq!(inf.reason[1][0], Some(Reason::FieldEscapes));
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
        Variant::B1,
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
    let inf = run(&[even, odd], &[false, false], Variant::B1);
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
    let inf = run(&[a, b], &[false, false], Variant::B1);
    assert_eq!(inf.borrowed, [vec![true], vec![true]]);
}

/// `f` tail-calls `g` (another group) with a fresh value: B1 makes `g`'s
/// parameter owned (O8), B2 leaves it to an owned copy.
#[test]
fn an_owned_tail_argument_from_another_group() {
    let f = B::default().ctor(1, &[]).tail(1, &[1 | MOVE]).code(1, 2);
    let g = walk_param();
    let b1 = run(&[f, g], &[false, false], Variant::B1);
    assert_eq!(b1.reason[1][0], Some(Reason::TailAcross));
    let f = B::default().ctor(1, &[]).tail(1, &[1 | MOVE]).code(1, 2);
    let b2 = run(&[f, walk_param()], &[false, false], Variant::B2);
    assert_eq!(b2.borrowed[1], [true]);
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
fn a_function_used_as_a_value_is_owned_in_b1_only() {
    let b1 = run(&[walk_param()], &[true], Variant::B1);
    assert_eq!(b1.reason[0][0], Some(Reason::ValueUse));
    let b2 = run(&[walk_param()], &[true], Variant::B2);
    assert_eq!(b2.borrowed[0], [true]);
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
    let inf = run(&[f, walk_param()], &[false, false], Variant::B1);
    assert_eq!(inf.borrowed[1], [true]);
}
