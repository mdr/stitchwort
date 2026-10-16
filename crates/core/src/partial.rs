//! The kernel's partial computations (docs/proposals/partial.md §7.2): one
//! opaque type former, `Delay op res a`, and five constants that build its
//! values.
//!
//! ```text
//! Delay  : (op : Type) -> (res : op -> Type) -> Type -> Type
//! now    : [op] [res] [a] -> a -> Delay op res a
//! lift   : [op] [res] [a] -> Comp op res a -> Delay op res a
//! bindD  : [op] [res] [a b : Type] -> Delay op res a -> (a -> Delay op res b) -> Delay op res b
//! mapSig : [op1] [res1] [op2] [res2] [a] -> SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a
//! pfix   : [op] [res] [A : Type] [B : A -> Type] ->
//!          ((x : A) -> Delay (Plus (Rec A) op) (PlusRes (RecRes B) res) (B x)) ->
//!          (x : A) -> Delay op res (B x)
//! ```
//!
//! They're definitions without bodies, declared in the prelude like any
//! other signature, and admitted here once their types are checked to be
//! exactly these. A final definition without a body never unfolds, so an
//! application of one is a neutral term: conversion compares them
//! structurally. There's no computation rule and no eliminator: `Delay`
//! isn't a data type, so nothing can match on it, and positivity treats it
//! like any other type a data type might be nested in (refused).
//!
//! Why that's consistent (§7.8): any model of the rest of the theory
//! extends by reading every `Delay op res a` as a one-element set, and the
//! constants as the only functions into it. None of their types extracts an
//! `a` from a `Delay … a`. Only the runtime gives `Delay` a meaning
//! (`step.rs`), and nothing it computes is ever given back to the checker.
//!
//! This file is trusted for consistency: it fixes the types.

use std::rc::Rc;

use stitchwort_syntax::Diagnostic;

use crate::globals::{Globals, State};
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Icit, Sort, Term};
use crate::value::{conv, eval};

/// The type former and its constants, in the order they must be declared.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Primitive {
    Delay,
    Now,
    Lift,
    BindD,
    MapSig,
    Pfix,
}

impl Primitive {
    pub const ALL: [Primitive; 6] = [
        Primitive::Delay,
        Primitive::Now,
        Primitive::Lift,
        Primitive::BindD,
        Primitive::MapSig,
        Primitive::Pfix,
    ];

    /// Its name in the prelude.
    pub fn name(self) -> &'static str {
        match self {
            Primitive::Delay => "Delay",
            Primitive::Now => "now",
            Primitive::Lift => "lift",
            Primitive::BindD => "bindD",
            Primitive::MapSig => "mapSig",
            Primitive::Pfix => "pfix",
        }
    }

    pub fn named(name: &str) -> Option<Primitive> {
        Primitive::ALL.into_iter().find(|p| p.name() == name)
    }

    /// How many arguments a value built by this constant has (implicit ones
    /// included): an application to exactly this many is a `Delay`.
    pub fn arity(self) -> usize {
        match self {
            Primitive::Delay => 3,
            Primitive::Now | Primitive::Lift => 4,
            Primitive::BindD | Primitive::Pfix => 6,
            Primitive::MapSig => 7,
        }
    }
}

type Result<T> = std::result::Result<T, Diagnostic>;

/// A type in the shape of a term, with variables as de Bruijn *levels*
/// (counting from the outermost binder), which reads more like the types
/// above than indices would.
enum Shape {
    Level(usize),
    Type0,
    Pi(&'static str, Icit, Box<Shape>, Box<Shape>),
    App(Box<Shape>, Box<Shape>, Icit),
    Def(DefId),
    Data(DataId, Vec<Shape>),
}

impl Shape {
    fn term(&self, depth: usize) -> Term {
        match self {
            Shape::Level(l) => Term::Var(depth - 1 - l),
            Shape::Type0 => Term::Sort(Sort::Type(0)),
            Shape::Pi(x, icit, a, b) => Term::Pi(
                (*x).into(),
                *icit,
                Rc::new(a.term(depth)),
                Rc::new(b.term(depth + 1)),
            ),
            Shape::App(f, a, icit) => Term::app_icit(f.term(depth), a.term(depth), *icit),
            Shape::Def(id) => Term::Def(*id),
            Shape::Data(d, args) => Term::data(*d, args.iter().map(|a| a.term(depth)).collect()),
        }
    }
}

fn l(level: usize) -> Shape {
    Shape::Level(level)
}

fn pi(icit: Icit, x: &'static str, a: Shape, b: Shape) -> Shape {
    Shape::Pi(x, icit, Box::new(a), Box::new(b))
}

fn arrow(a: Shape, b: Shape) -> Shape {
    pi(Icit::Explicit, "_", a, b)
}

fn implicit(x: &'static str, a: Shape, b: Shape) -> Shape {
    pi(Icit::Implicit, x, a, b)
}

fn app(f: Shape, args: Vec<(Shape, Icit)>) -> Shape {
    args.into_iter()
        .fold(f, |f, (a, icit)| Shape::App(Box::new(f), Box::new(a), icit))
}

/// `op -> Type`, for the operations `op` at `level`.
fn res_type(op: usize) -> Shape {
    arrow(l(op), Shape::Type0)
}

/// The prelude declarations the types refer to.
struct Prelude {
    comp: DataId,
    plus: DataId,
    sig_map: DataId,
    rec: DataId,
    plus_res: DefId,
    rec_res: DefId,
    delay: Option<DefId>,
}

fn prelude(g: &Globals) -> Option<Prelude> {
    let r = &g.registry;
    Some(Prelude {
        comp: r.data(Builtin::Comp)?,
        plus: r.data(Builtin::Plus)?,
        sig_map: r.data(Builtin::SigMap)?,
        rec: r.data(Builtin::Rec)?,
        plus_res: r.def(Builtin::PlusRes)?,
        rec_res: r.def(Builtin::RecRes)?,
        delay: g.builtins.primitive_id(Primitive::Delay),
    })
}

/// The type `prim` must have.
fn expected(p: &Prelude, prim: Primitive) -> Option<Shape> {
    let delay = |op: Shape, res: Shape, a: Shape| -> Option<Shape> {
        Some(app(
            Shape::Def(p.delay?),
            vec![
                (op, Icit::Explicit),
                (res, Icit::Explicit),
                (a, Icit::Explicit),
            ],
        ))
    };
    let ty = || Shape::Type0;
    Some(match prim {
        // (op : Type) -> (res : op -> Type) -> Type -> Type
        Primitive::Delay => pi(
            Icit::Explicit,
            "op",
            ty(),
            pi(Icit::Explicit, "res", res_type(0), arrow(ty(), ty())),
        ),
        // [op] [res] [a] -> a -> Delay op res a
        Primitive::Now => implicit(
            "op",
            ty(),
            implicit(
                "res",
                res_type(0),
                implicit("a", ty(), arrow(l(2), delay(l(0), l(1), l(2))?)),
            ),
        ),
        // [op] [res] [a] -> Comp op res a -> Delay op res a
        Primitive::Lift => implicit(
            "op",
            ty(),
            implicit(
                "res",
                res_type(0),
                implicit(
                    "a",
                    ty(),
                    arrow(
                        Shape::Data(p.comp, vec![l(0), l(1), l(2)]),
                        delay(l(0), l(1), l(2))?,
                    ),
                ),
            ),
        ),
        // [op] [res] [a b] -> Delay op res a -> (a -> Delay op res b) -> Delay op res b
        Primitive::BindD => implicit(
            "op",
            ty(),
            implicit(
                "res",
                res_type(0),
                implicit(
                    "a",
                    ty(),
                    implicit(
                        "b",
                        ty(),
                        arrow(
                            delay(l(0), l(1), l(2))?,
                            arrow(
                                arrow(l(2), delay(l(0), l(1), l(3))?),
                                delay(l(0), l(1), l(3))?,
                            ),
                        ),
                    ),
                ),
            ),
        ),
        // [op1] [res1] [op2] [res2] [a] ->
        //   SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a
        Primitive::MapSig => implicit(
            "op1",
            ty(),
            implicit(
                "res1",
                res_type(0),
                implicit(
                    "op2",
                    ty(),
                    implicit(
                        "res2",
                        res_type(2),
                        implicit(
                            "a",
                            ty(),
                            arrow(
                                Shape::Data(p.sig_map, vec![l(0), l(1), l(2), l(3)]),
                                arrow(delay(l(0), l(1), l(4))?, delay(l(2), l(3), l(4))?),
                            ),
                        ),
                    ),
                ),
            ),
        ),
        // [op] [res] [A] [B : A -> Type] ->
        //   ((x : A) -> Delay (Plus (Rec A) op) (PlusRes (RecRes B) res) (B x)) ->
        //   (x : A) -> Delay op res (B x)
        Primitive::Pfix => {
            let rec_a = Shape::Data(p.rec, vec![l(2)]);
            let ops = Shape::Data(p.plus, vec![Shape::Data(p.rec, vec![l(2)]), l(0)]);
            let rec_res = app(
                Shape::Def(p.rec_res),
                vec![(l(2), Icit::Implicit), (l(3), Icit::Explicit)],
            );
            let res = app(
                Shape::Def(p.plus_res),
                vec![
                    (rec_a, Icit::Implicit),
                    (l(0), Icit::Implicit),
                    (rec_res, Icit::Explicit),
                    (l(1), Icit::Explicit),
                ],
            );
            let b_of = |x: usize| app(l(3), vec![(l(x), Icit::Explicit)]);
            // The description is the parameter at level 4; its own `x` is at
            // level 4 inside its type. The final `x` is at level 5.
            let description = pi(Icit::Explicit, "x", l(2), delay(ops, res, b_of(4))?);
            implicit(
                "op",
                ty(),
                implicit(
                    "res",
                    res_type(0),
                    implicit(
                        "A",
                        ty(),
                        implicit(
                            "B",
                            res_type(2),
                            arrow(
                                description,
                                pi(Icit::Explicit, "x", l(2), delay(l(0), l(1), b_of(5))?),
                            ),
                        ),
                    ),
                ),
            )
        }
    })
}

fn shape_error(g: &Globals, id: DefId, prim: Primitive) -> Diagnostic {
    Diagnostic::error(
        "E-BUILTIN",
        format!(
            "the prelude's `{}` doesn't have the type the compiler expects",
            prim.name()
        ),
    )
    .with_label(g.def(id).span, "here")
}

/// Admits pending definition `id`, declared with only a signature, as
/// primitive `prim`: final, with no body. Its type must be exactly the one
/// above. Each primitive is admitted once, `Delay` first; the prelude's
/// `Comp`, `Plus`, `PlusRes`, `SigMap`, `Rec` and `RecRes` must be final.
pub fn define_primitive(g: &mut Globals, id: DefId, prim: Primitive) -> Result<()> {
    let Some(def) = g.defs.get(id.0) else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown definition",
        ));
    };
    if def.state != State::Pending {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            format!(
                "malformed core term: `{}` has already been defined",
                def.name
            ),
        ));
    }
    let fits = g.builtins.primitive_id(prim).is_none()
        && match prelude(g).and_then(|p| expected(&p, prim)) {
            Some(shape) => conv(g, 0, &eval(g, &[], &shape.term(0))?, &def.ty_value)?,
            None => false,
        };
    if !fits {
        let e = shape_error(g, id, prim);
        g.defs[id.0].state = State::Failed;
        return Err(e);
    }
    let def = &mut g.defs[id.0];
    def.state = State::Final;
    def.arity = 0;
    g.builtins.register_primitive(prim, id);
    Ok(())
}
