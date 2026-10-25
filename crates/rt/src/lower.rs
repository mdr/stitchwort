//! Lowering checked core terms to the erased IR ([`crate::ir`]).
//!
//! Erasure follows the JS backend exactly, through the decisions both share
//! ([`crate::erasure`], [`crate::natives`]): the same parameters, fields and
//! `let`s are erased, the same definitions are native, and a program uses
//! the same definitions. Like the JS generator, lowering recurses over a
//! definition's body, so each level checks there's stack left first.

use std::cell::OnceCell;
use std::rc::Rc;

use num_bigint::BigInt;
use stitchwort_core::collections::HashMap;
use stitchwort_core::native::Native;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Limits, QuotForm, Sort, Term};
use stitchwort_syntax::Diagnostic;

use crate::effect::{Carrier, EffectNatives, EffectOp};
use crate::erasure::{DefShape, def_shape, is_done_continuation, text_literal};
use crate::fusion::StateFusion;
use crate::hoist::SigMaps;
use crate::ir::{
    Arm, Body, CtorInfo, Expr, Global, GlobalId, GlobalKind, Lambda, LambdaId, Lit, MainRow,
    MatchKind, PrimOp, Program, Shapes, Slot, TypeId, TypeInfo,
};
use crate::natives::{FloatPrim, IntNative, Representation, TextNative};
use crate::opt::{Types, optimize};
use crate::specialise::{self, Specialiser};

type Result<T> = std::result::Result<T, Diagnostic>;

const PASS: &str = "runtime lowering";

fn internal(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-RUNTIME", format!("internal error: {}", message.into()))
}

/// A handler around partial code (`foldD`, docs/proposals/partial-handlers.md)
/// runs only on the reference runner so far: this runtime gets it in lane C
/// of that note. A `main` that uses it is refused when it's lowered; a test
/// that runs it stops with this error, and runs on the reference evaluator
/// instead.
pub fn fold_d_unsupported() -> Diagnostic {
    Diagnostic::error(
        "E-RUNTIME",
        "a handler around partial code isn't supported on this runner yet",
    )
    .with_note("run it with `stitchwort run --reference`")
}

/// Lowers the program that runs `main`: the closed term of type
/// `{IO, Partial} ()` (`row` [`MainRow::Io`]) or `{IO, Fail, Partial} ()`
/// ([`MainRow::FailIo`]) that `stitchwort run` runs (`Main`'s term and row
/// in the driver), with every definition it uses. Uses at most
/// `limits.stack` bytes of stack: a definition nested too deeply for that
/// is an `E-RESOURCE` error.
pub fn lower_main(g: &Globals, limits: Limits, main: &Term, row: MainRow) -> Result<Program> {
    if row == MainRow::FailIo && g.registry.loaded_data(Builtin::Fail).is_none() {
        return Err(internal("a `main` that may fail, with `Fail` not loaded"));
    }
    let mut program = lower_program(g, limits, main)?;
    if program.globals.iter().any(|global| {
        matches!(
            global.kind,
            GlobalKind::Native(PrimOp::Delay(Primitive::FoldD))
        )
    }) {
        return Err(fold_d_unsupported());
    }
    program.main_row = row;
    Ok(program)
}

/// Lowers global `id` and every definition it uses; the program's entry is
/// `id`'s value. For tests and debugging.
pub fn lower_global(g: &Globals, limits: Limits, id: DefId) -> Result<Program> {
    lower_program(g, limits, &Term::Def(id))
}

/// Lowers the definitions `ids` and every definition they use, with no
/// entry (it's `erased`). For tests that lower everything a program has.
pub fn lower_definitions(g: &Globals, limits: Limits, ids: &[DefId]) -> Result<Program> {
    lower_roots(g, limits, ids.to_vec(), &Term::Refl)
}

fn lower_program(g: &Globals, limits: Limits, entry: &Term) -> Result<Program> {
    // The definitions the entry uses are found by scanning it, which sees
    // which of its calls are at the empty row.
    lower_roots(g, limits, Vec::new(), entry)
}

fn lower_roots(g: &Globals, limits: Limits, roots: Vec<DefId>, entry: &Term) -> Result<Program> {
    let _op = g.budget.operation(Limits::stack_only(limits.stack));
    let mut cx = Lowerer::new(g)?;
    // What the entry uses, as the JS backend finds it: an erased definition
    // or a native one is opaque. A call at the empty row uses the callee's
    // variant (docs/proposals/effect-polymorphism.md, design E).
    let failure = std::cell::RefCell::new(None);
    let reach = specialise::reachable(&cx.spec, roots, &[entry], |id| match cx.shape(id) {
        Ok(shape) => shape.result_erased || cx.native_op(id).is_some(),
        Err(e) => {
            failure.borrow_mut().get_or_insert(e);
            true
        }
    })?;
    if let Some(e) = failure.into_inner() {
        return Err(e);
    }
    let used = &reach.used;
    // The globals, in declaration order (dependency order), each variant
    // just after its definition's place.
    let mut plans = Vec::new();
    for id in (0..g.defs.len())
        .map(DefId)
        .filter(|id| used[id.0] || reach.empty[id.0])
    {
        let shape = cx.shape(id)?;
        if shape.result_erased {
            continue;
        }
        let mask = shape.mask().to_vec();
        let params = u32::try_from(shape.runtime_arity()).expect("arity fits");
        let native = cx.native_op(id);
        if let Some(op) = native {
            if op.arity() != params {
                return Err(internal(format!(
                    "`{}` takes {params} runtime arguments, but its native operation {}",
                    g.def(id).name,
                    op.arity()
                )));
            }
        } else if g.def(id).body().is_none() {
            return Err(
                Diagnostic::error("E-RUNTIME", format!("can't run `{}`", g.def(id).name))
                    .with_label(
                        g.def(id).span,
                        "it hasn't been checked successfully, so it has no definition to run",
                    ),
            );
        }
        if used[id.0] {
            let gid = GlobalId(u32::try_from(plans.len()).expect("globals fit"));
            cx.global_of.insert(id, (gid, params, native));
            plans.push((id, params, native, false));
        }
        if reach.empty[id.0] {
            let mask = cx.spec.empty_mask(id, &mask)?;
            let params = u32::try_from(mask.iter().filter(|e| !**e).count()).expect("arity fits");
            let gid = GlobalId(u32::try_from(plans.len()).expect("globals fit"));
            cx.empty_of.insert(id, (gid, params, mask));
            plans.push((id, params, None, true));
        }
    }
    cx.hoisted_base = plans.len();
    let mut globals = Vec::with_capacity(plans.len());
    for (id, params, native, variant) in plans {
        let def = g.def(id);
        let kind = match native {
            Some(op) => GlobalKind::Native(op),
            None => {
                let body = if variant {
                    cx.empty_body(id)
                } else {
                    cx.def_body(id)
                }
                .map_err(|e| e.with_label(def.span, "while lowering this for the runtime"))?;
                if params == 0 {
                    GlobalKind::Constant { body }
                } else {
                    GlobalKind::Function { params, body }
                }
            }
        };
        globals.push(Global {
            name: if variant {
                format!("{}[empty]", def.path).into()
            } else {
                def.path.clone()
            },
            def: id,
            kind,
        });
    }
    let entry = cx.frame_body(&[], |cx| cx.expr(entry))?;
    globals.append(&mut cx.hoisted);
    // The simplifier needs to recognise, and build, `Bool` and `Decidable`.
    let types = Types {
        bool_: g.registry.data(Builtin::Bool).map(|d| cx.type_id(d)),
        decidable: g.registry.data(Builtin::Decidable).map(|d| cx.type_id(d)),
    };
    let mut program = Program {
        globals,
        lambdas: cx.lambdas,
        types: cx.types,
        entry,
        main_row: MainRow::Io,
        shapes: shapes(g)?,
    };
    optimize(&mut program, types);
    Ok(program)
}

/// The constructors the runtime builds and takes apart, from the prelude:
/// constructor `c` of data type `d`, checked to have `fields` runtime
/// fields.
fn shape(g: &Globals, d: DataId, c: usize, fields: usize) -> Result<u32> {
    let data = g.data(d);
    let ctor = data
        .ctors
        .get(c)
        .ok_or_else(|| internal(format!("`{}` has no constructor {c}", data.name)))?;
    // The runtime takes these apart as cells, so none may be a record stored
    // as its field (D866).
    if data.unboxed_field().is_some() {
        return Err(internal(format!(
            "`{}` is stored unboxed, not as a cell",
            data.name
        )));
    }
    let runtime = ctor.field_erased.iter().filter(|erased| !**erased).count();
    if runtime != fields {
        return Err(internal(format!(
            "`{}` has {runtime} runtime fields, not {fields}",
            ctor.name
        )));
    }
    Ok(u32::try_from(c).expect("ctors fit"))
}

fn shapes(g: &Globals) -> Result<Shapes> {
    let missing = |b: Builtin| internal(format!("the prelude doesn't declare `{}`", b.name()));
    let ctor = |b: Builtin, fields: usize| -> Result<u32> {
        let (d, c) = g.registry.ctor(b).ok_or_else(|| missing(b))?;
        shape(g, d, c, fields)
    };
    // For the constructors the registry doesn't name: by index.
    let nth = |b: Builtin, c: usize, fields: usize| -> Result<u32> {
        let d = g.registry.data(b).ok_or_else(|| missing(b))?;
        shape(g, d, c, fields)
    };
    Ok(Shapes {
        false_: ctor(Builtin::False, 0)?,
        true_: ctor(Builtin::True, 0)?,
        none: ctor(Builtin::None, 0)?,
        some: ctor(Builtin::Some, 1)?,
        yes: ctor(Builtin::Yes, 0)?,
        no: ctor(Builtin::No, 0)?,
        nil: ctor(Builtin::Nil, 0)?,
        cons: ctor(Builtin::Cons, 2)?,
        pair: ctor(Builtin::MkPair, 2)?,
        char_: ctor(Builtin::MkChar, 1)?,
        unit: ctor(Builtin::UnitValue, 0)?,
        done: ctor(Builtin::Done, 1)?,
        call: ctor(Builtin::Call, 2)?,
        bind_node: ctor(Builtin::Done, 1)?.max(ctor(Builtin::Call, 2)?) + 1,
        row_empty: match g.registry.ctor(Builtin::RowEmpty) {
            Some((d, c)) if g.registry.loaded_data(Builtin::Row) == Some(d) => shape(g, d, c, 0)?,
            _ => u32::MAX,
        },
        left: nth(Builtin::Plus, 0, 1)?,
        right: nth(Builtin::Plus, 1, 1)?,
        recur: nth(Builtin::Rec, 0, 1)?,
        sig_map: nth(Builtin::SigMap, 0, 2)?,
        print: ctor(Builtin::Print, 1)?,
        read_line: ctor(Builtin::ReadLine, 1)?,
        read_all: ctor(Builtin::ReadAll, 1)?,
        stop: match g.registry.loaded_data(Builtin::Fail) {
            Some(d) => shape(g, d, 0, 1)?,
            None => u32::MAX,
        },
    })
}

/// What a de Bruijn level stands for while lowering.
#[derive(Clone, Copy)]
enum Bind {
    /// An erased value: a proof, a type, or an erased parameter or field.
    Erased,
    /// Slot `slot` of frame `frame` (an index into [`Lowerer::frames`]).
    Slot { frame: usize, slot: Slot },
}

/// A function's or lambda's frame, while its body is lowered.
struct Frame {
    /// The next free slot. Slots are given out in scope order and reused by
    /// sibling scopes (the arms of a match).
    next: Slot,
    /// How many slots it needs.
    size: Slot,
    /// Whether each slot has been read since it was last bound: a match
    /// binds only the fields its arm uses.
    used: Vec<bool>,
    /// The levels of the outer variables it captures, in order.
    captures: Vec<usize>,
}

struct Lowerer<'g> {
    g: &'g Globals,
    repr: Representation,
    shapes: Vec<OnceCell<DefShape>>,
    if_then_else: Option<DefId>,
    to_bool: Option<DefId>,
    /// The effect runtime's natives, if the core's effect machinery has the
    /// shapes they were written for.
    effect: Option<EffectNatives>,
    /// Recognises state-passing handlers (stage 4d), when there are
    /// natives.
    fusion: Option<StateFusion>,
    /// Each global's id, runtime arity and native operation.
    global_of: HashMap<DefId, (GlobalId, u32, Option<PrimOp>)>,
    /// Decides which calls are at the empty row, and makes the variants.
    spec: Specialiser<'g>,
    /// Each empty-row variant's global, runtime arity and erasure mask.
    empty_of: HashMap<DefId, (GlobalId, u32, Vec<bool>)>,
    lambdas: Vec<Lambda>,
    types: Vec<TypeInfo>,
    type_of: HashMap<DataId, TypeId>,
    /// What each de Bruijn level stands for, outermost first.
    env: Vec<Bind>,
    frames: Vec<Frame>,
    /// Recognises closed signature maps, each made a constant
    /// ([`crate::hoist`], stage 4f).
    sig_maps: Option<SigMaps>,
    /// The constants made of closed maps, which go after the program's own
    /// globals (from `hoisted_base`), and each one's index by its code.
    hoisted: Vec<Global>,
    hoisted_of: HashMap<String, GlobalId>,
    hoisted_base: usize,
    /// Whether a map's own code is being lowered (a map inside it is part
    /// of the same constant).
    hoisting: bool,
}

impl<'g> Lowerer<'g> {
    fn new(g: &'g Globals) -> Result<Self> {
        let repr = Representation::new(g, true, true).map_err(Diagnostic::from)?;
        // As for `run --js`: the runtime is written for native numbers and
        // text.
        if repr.nat.is_none() {
            return Err(internal(
                "the prelude's `Nat` doesn't have the representation the runtime expects",
            ));
        }
        if repr.text.is_none() {
            return Err(internal(
                "the prelude's `Text` doesn't have the representation the runtime expects",
            ));
        }
        Ok(Lowerer {
            g,
            repr,
            shapes: g.defs.iter().map(|_| OnceCell::new()).collect(),
            if_then_else: g.registry.def(Builtin::IfThenElse),
            to_bool: g.registry.def(Builtin::ToBool),
            effect: EffectNatives::new(g),
            fusion: EffectNatives::new(g).and_then(|_| StateFusion::new(g)),
            global_of: HashMap::default(),
            spec: Specialiser::new(g),
            empty_of: HashMap::default(),
            lambdas: Vec::new(),
            types: Vec::new(),
            type_of: HashMap::default(),
            env: Vec::new(),
            frames: Vec::new(),
            sig_maps: SigMaps::new(g),
            hoisted: Vec::new(),
            hoisted_of: HashMap::default(),
            hoisted_base: 0,
            hoisting: false,
        })
    }

    /// What erasure decides about `id`, computed on first use. `Delay`'s
    /// constants take all their parameters: the runtime builds `Delay`
    /// values.
    fn shape(&self, id: DefId) -> Result<&DefShape> {
        let cell = &self.shapes[id.0];
        if let Some(shape) = cell.get() {
            return Ok(shape);
        }
        let shape = def_shape(self.g, id, true)?;
        Ok(cell.get_or_init(|| shape))
    }

    /// The native operation that replaces `id`, if any.
    fn native_op(&self, id: DefId) -> Option<PrimOp> {
        if let Some(prim) = self.g.builtins.primitive(id) {
            return Some(PrimOp::Delay(prim));
        }
        if let Some(op) = self.repr.kernel_native(self.g, id) {
            return Some(PrimOp::Nat(op));
        }
        if let Some(op) = self.repr.text_natives.get(&id) {
            return Some(PrimOp::Text(*op));
        }
        if let Some(op) = self.repr.float_natives.get(&id) {
            return Some(PrimOp::Float(*op));
        }
        if let Some(op) = self.effect.as_ref().and_then(|e| e.native(id)) {
            return Some(PrimOp::Effect(op));
        }
        self.repr.int_natives.get(&id).map(|op| PrimOp::Int(*op))
    }

    fn type_id(&mut self, d: DataId) -> TypeId {
        if let Some(t) = self.type_of.get(&d) {
            return *t;
        }
        let data = self.g.data(d);
        let ctors = data
            .ctors
            .iter()
            .map(|ctor| CtorInfo {
                name: ctor.name.clone(),
                fields: ctor
                    .fields
                    .iter()
                    .zip(&ctor.field_erased)
                    .filter(|(_, erased)| !**erased)
                    .map(|((name, _), _)| name.clone())
                    .collect(),
            })
            .collect();
        let t = TypeId(u32::try_from(self.types.len()).expect("types fit"));
        self.types.push(TypeInfo {
            data: d,
            name: data.name.clone(),
            record: data.record,
            ctors,
        });
        self.type_of.insert(d, t);
        t
    }

    // ------------------------------------------------------------ frames

    /// Lowers a body in a new frame whose parameters are `params` (whether
    /// each is erased), bound at the next levels, in slots `0..`.
    fn frame_body(
        &mut self,
        params: &[bool],
        lower: impl FnOnce(&mut Self) -> Result<Expr>,
    ) -> Result<Body> {
        let level = self.env.len();
        self.frames.push(Frame {
            next: 0,
            size: 0,
            used: Vec::new(),
            captures: Vec::new(),
        });
        for erased in params {
            if *erased {
                self.env.push(Bind::Erased);
            } else {
                self.bind_slot();
            }
        }
        let expr = lower(self);
        self.env.truncate(level);
        let frame = self.frames.pop().expect("pushed above");
        Ok(Body {
            frame: frame.size,
            expr: expr?,
        })
    }

    fn frame(&mut self) -> &mut Frame {
        self.frames.last_mut().expect("lowering happens in a frame")
    }

    /// Binds the next level to a fresh slot of the current frame.
    fn bind_slot(&mut self) -> Slot {
        let slot = self.reserve_slot();
        self.env.push(Bind::Slot {
            frame: self.frames.len() - 1,
            slot,
        });
        slot
    }

    /// A fresh slot of the current frame, not yet bound to a level.
    fn reserve_slot(&mut self) -> Slot {
        let frame = self.frame();
        let slot = frame.next;
        frame.next += 1;
        frame.size = frame.size.max(frame.next);
        let i = slot as usize;
        if frame.used.len() <= i {
            frame.used.resize(i + 1, false);
        }
        frame.used[i] = false;
        slot
    }

    /// The scope as it is, to return to with [`Lowerer::leave`].
    fn mark(&mut self) -> (usize, Slot) {
        let next = self.frame().next;
        (self.env.len(), next)
    }

    fn leave(&mut self, (level, next): (usize, Slot)) {
        self.env.truncate(level);
        self.frame().next = next;
    }

    fn slot_used(&mut self, slot: Slot) -> bool {
        self.frame()
            .used
            .get(slot as usize)
            .copied()
            .unwrap_or(false)
    }

    /// The variable at de Bruijn `level`, read in the current frame: a slot
    /// of its own, or a value it captures.
    fn level(&mut self, level: usize) -> Expr {
        let current = self.frames.len() - 1;
        match self.env[level] {
            Bind::Erased => Expr::Erased,
            Bind::Slot { frame, slot } if frame == current => {
                self.frames[current].used[slot as usize] = true;
                Expr::Local(slot)
            }
            Bind::Slot { .. } => {
                let captures = &mut self.frames[current].captures;
                let index = match captures.iter().position(|l| *l == level) {
                    Some(i) => i,
                    None => {
                        captures.push(level);
                        captures.len() - 1
                    }
                };
                Expr::Captured(u32::try_from(index).expect("captures fit"))
            }
        }
    }

    fn var(&mut self, ix: usize) -> Expr {
        self.level(self.env.len() - 1 - ix)
    }

    // -------------------------------------------------------- definitions

    /// A definition's body: its parameters (up to its arity) are the
    /// frame's first slots, the erased ones left out.
    fn def_body(&mut self, id: DefId) -> Result<Body> {
        let def = self.g.def(id);
        let body = def.run_body().expect("checked by lower_program").clone();
        let mask = self.shape(id)?.mask().to_vec();
        let params: Vec<bool> = (0..def.arity)
            .map(|i| mask.get(i).copied().unwrap_or(false))
            .collect();
        let arity = def.arity;
        // Its calls of row eliminators with `Empty` inlined, if it has any.
        let simplified = self.spec.generic_body(id)?;
        let tree = simplified
            .as_deref()
            .unwrap_or_else(|| body.peel_lams(arity));
        self.frame_body(&params, |cx| cx.expr(tree))
    }

    /// The body of `id`'s empty-row variant: its row parameters are erased.
    fn empty_body(&mut self, id: DefId) -> Result<Body> {
        let body = self
            .spec
            .empty_body(id)?
            .ok_or_else(|| internal("an empty-row variant that can't be made"))?;
        let mask = self.empty_of[&id].2.clone();
        let params: Vec<bool> = (0..self.g.def(id).arity)
            .map(|i| mask.get(i).copied().unwrap_or(false))
            .collect();
        self.frame_body(&params, |cx| cx.expr(&body))
    }

    // -------------------------------------------------------- expressions

    fn expr(&mut self, term: &Term) -> Result<Expr> {
        self.g.budget.nesting(PASS)?;
        Ok(match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t)?,
            Term::Var(ix) => self.var(*ix),
            Term::Def(id) => self.apply_def(*id, &[])?,
            Term::Nat(n) => Expr::Lit(Lit::Nat((**n).clone())),
            Term::Chars(chars) => Expr::Lit(Lit::Chars(
                chars.as_slice().iter().collect::<String>().into(),
            )),
            Term::App(..) => {
                let (head, args) = term.spine();
                self.application(head, &args)?
            }
            Term::Lam(..) => self.lambda(term)?,
            Term::Let(_, _, value, body, erased) => self.let_(value, body, *erased)?,
            Term::Ctor(d, c, args) => self.ctor(term, *d, *c, args)?,
            // Proofs are erased, and transport along an equality does nothing.
            Term::J(_, base, _) => self.expr(base)?,
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Quot(QuotForm::Type, ..) => Expr::Erased,
            // Quotients (docs/proposals/map-equality.md §7.4.1, D921): there
            // is no wrapper, so `Quot.mk a` is `a`, or the placeholder when
            // the carrier's elements are erased (the checker's flag); a lift
            // whose result isn't erased is the application `f q`, through
            // the usual path, so `f`'s own type decides which arguments it
            // takes (§7.4.2). Erased-result lifts, `Quot.ind` and
            // `Quot.sound` are proofs or types.
            Term::Quot(QuotForm::Mk, args, false) => self.expr(&args[2])?,
            Term::Quot(QuotForm::Lift, args, false) => {
                let f_q = Term::App(args[3].clone(), args[5].clone(), Icit::Explicit);
                self.expr(&f_q)?
            }
            Term::Quot(QuotForm::Mk | QuotForm::Lift | QuotForm::Ind | QuotForm::Sound, ..) => {
                Expr::Erased
            }
            Term::Case(ix, d, branches) => self.case(*ix, *d, branches)?,
            Term::NumCase(ix, arms, default) => self.num_case(*ix, arms, default)?,
            Term::Meta(_) => {
                return Err(internal("an unsolved metavariable in a checked definition"));
            }
        })
    }

    fn exprs(&mut self, terms: &[&Term]) -> Result<Vec<Expr>> {
        terms.iter().map(|t| self.expr(t)).collect()
    }

    fn application(&mut self, head: &Term, args: &[&Term]) -> Result<Expr> {
        match strip(head) {
            Term::Def(id) => self.apply_def(*id, args),
            Term::Lam(..) => {
                if let Some(reduced) = crate::erasure::beta_variable(self.g, head, args)? {
                    return self.expr(&reduced);
                }
                self.beta(head, args)
            }
            _ => {
                let f = self.expr(head)?;
                // An erased function (a proof of a `∀`, or a type-level
                // function) applied to anything is erased too: the
                // `[decreasing := shrinks x h]` of a definition whose
                // `shrinks` is a proof parameter.
                if matches!(f, Expr::Erased) {
                    return Ok(Expr::Erased);
                }
                let args = self.exprs(args)?;
                Ok(apply(f, args))
            }
        }
    }

    /// `(x y => body) a b` as `let x = a; let y = b; body`: no closure is
    /// made. The arguments are in the outer scope, so each is lowered before
    /// any parameter is bound; but `b` is computed after `x` has its slot,
    /// so the slots of the parameters before it are reserved while it's
    /// lowered, so that `b`'s own variables don't overwrite them.
    fn beta(&mut self, head: &Term, args: &[&Term]) -> Result<Expr> {
        let mark = self.mark();
        let mut body = strip(head);
        let mut lets = Vec::new();
        let mut params = Vec::new();
        let mut rest = Vec::new();
        for arg in args {
            // (An error ends lowering, so the scope needn't be restored.)
            let value = self.expr(arg)?;
            let Term::Lam(_, _, inner) = body else {
                rest.push(value);
                continue;
            };
            if matches!(value, Expr::Erased) {
                params.push(Bind::Erased);
            } else {
                let slot = self.reserve_slot();
                params.push(Bind::Slot {
                    frame: self.frames.len() - 1,
                    slot,
                });
                lets.push((slot, value));
            }
            body = strip(inner);
        }
        self.env.extend(params);
        let out = self.expr(body);
        // An argument the body doesn't use needn't be computed: it's pure,
        // and total (a partial computation is a value until it's run).
        lets.retain(|(slot, _)| self.slot_used(*slot));
        self.leave(mark);
        let mut out = apply(out?, rest);
        for (slot, value) in lets.into_iter().rev() {
            out = Expr::Let(slot, Box::new(value), Box::new(out));
        }
        Ok(out)
    }

    /// A definition applied to `args`: erased arguments are left out, and
    /// with all its runtime arguments it's a saturated call.
    fn apply_def(&mut self, id: DefId, args: &[&Term]) -> Result<Expr> {
        // A closed signature map (a `translate`'s, say): a constant,
        // computed when first used and kept, not built again on every call
        // (crate::hoist). It reads no variable, so it's lowered in a frame
        // of its own.
        if !self.hoisting
            && let Some(sig_maps) = &self.sig_maps
            && sig_maps.closed_map(self.g, id, args)
        {
            self.hoisting = true;
            let body = self.frame_body(&[], |cx| cx.apply_def(id, args));
            self.hoisting = false;
            let body = body?;
            let key = format!("{:?}", body.expr);
            if let Some(gid) = self.hoisted_of.get(&key) {
                return Ok(Expr::Global(*gid));
            }
            let index = self.hoisted_base + self.hoisted.len();
            let gid = GlobalId(u32::try_from(index).expect("globals fit"));
            self.hoisted.push(Global {
                name: format!("{}[map {}]", self.g.def(id).path, self.hoisted.len()).into(),
                def: id,
                kind: GlobalKind::Constant { body },
            });
            self.hoisted_of.insert(key, gid);
            return Ok(Expr::Global(gid));
        }
        if Some(id) == self.if_then_else && args.len() >= 4 {
            return self.if_(args);
        }
        if Some(id) == self.to_bool
            && let [_, decision] = args
        {
            // `a == b` on native values: `toBool (Nat.decEq a b)` is
            // `Nat.equal a b`, and likewise for `Int` and `Text`.
            let decision = self.expr(decision)?;
            let fused = match decision {
                Expr::Prim(PrimOp::Nat(Native::DecEqNat), operands) => {
                    Ok((PrimOp::Nat(Native::EqNat), operands))
                }
                Expr::Prim(PrimOp::Int(IntNative::DecEqInt), operands) => {
                    Ok((PrimOp::IntEqual, operands))
                }
                Expr::Prim(PrimOp::Text(TextNative::DecEqText), operands) => {
                    Ok((PrimOp::TextEqual, operands))
                }
                other => Err(other),
            };
            let decision = match fused {
                Ok((op, operands)) => return Ok(Expr::Prim(op, operands)),
                Err(decision) => decision,
            };
            let (gid, params, native) = self.global(id)?;
            debug_assert!(native.is_none() && params == 1);
            return Ok(Expr::Call(gid, vec![decision]));
        }
        let shape = self.shape(id)?;
        if shape.result_erased {
            return Ok(Expr::Erased);
        }
        // A state-passing handler at the empty row: its fold runs as a loop
        // with the state in a variable (docs/proposals/effect-runtime.md
        // §9.1.5, stage 4d).
        if self.effect.as_ref().is_some_and(|e| e.is_fold(id))
            && let Some(fusion) = &self.fusion
            && let Some(fused) = fusion.fuse(self.g, args)?
        {
            let op = if fused.comp {
                EffectOp::FoldStateComp
            } else {
                EffectOp::FoldState
            };
            let runtime = self.exprs(&[&fused.done, &fused.call, args[6]])?;
            let rest = self.exprs(&args[7..])?;
            return Ok(apply(Expr::Prim(PrimOp::Effect(op), runtime), rest));
        }
        // A call at the empty row calls the variant, which takes no row.
        let variant = self.empty_of.contains_key(&id) && self.spec.empty_call(id, args)?;
        let mask = if variant {
            self.empty_of[&id].2.clone()
        } else {
            shape.mask().to_vec()
        };
        // A definition used as a value while an erased parameter is still
        // unsupplied: whoever receives it knows only its type, so it passes
        // the type and proof arguments too. Eta-expand over all the
        // remaining parameters; the saturated call inside drops the erased
        // ones as usual (D922). The supplied run-time arguments are
        // computed once, in `let`s outside the closure, not on every call.
        if args.len() < mask.len() && mask[args.len()..].iter().any(|erased| *erased) {
            let missing = mask.len() - args.len();
            let bound: Vec<usize> = (0..args.len())
                .filter(|i| !mask[*i] && !matches!(strip(args[*i]), Term::Var(_) | Term::Nat(_)))
                .collect();
            let n = bound.len();
            let mut spine = Term::Def(id);
            for (i, a) in args.iter().enumerate() {
                let a = match bound.iter().position(|b| *b == i) {
                    Some(j) => Term::Var(missing + (n - 1 - j)),
                    None => a.shift(self.g, n + missing, 0)?,
                };
                spine = Term::App(Rc::new(spine), Rc::new(a), Icit::Explicit);
            }
            for k in (0..missing).rev() {
                spine = Term::App(Rc::new(spine), Rc::new(Term::Var(k)), Icit::Explicit);
            }
            for _ in 0..missing {
                spine = Term::Lam("x".into(), Icit::Explicit, Rc::new(spine));
            }
            for (j, i) in bound.iter().enumerate().rev() {
                let value = args[*i].shift(self.g, j, 0)?;
                spine = Term::Let(
                    "s".into(),
                    Rc::new(Term::Refl),
                    Rc::new(value),
                    Rc::new(spine),
                    false,
                );
            }
            return self.expr(&spine);
        }
        let runtime: Vec<&Term> = args
            .iter()
            .enumerate()
            .filter(|(i, _)| !mask.get(*i).copied().unwrap_or(false))
            .map(|(_, a)| *a)
            .collect();
        let mut runtime = self.exprs(&runtime)?;
        let (gid, params, native) = if variant {
            let (gid, params, _) = &self.empty_of[&id];
            (*gid, *params, None)
        } else {
            self.global(id)?
        };
        let params = params as usize;
        if runtime.len() < params {
            return Ok(if runtime.is_empty() {
                Expr::Global(gid)
            } else {
                Expr::PartialApp(gid, runtime)
            });
        }
        let rest = runtime.split_off(params);
        let call = match native {
            Some(PrimOp::Effect(EffectOp::Fold)) => self.fold(args, runtime)?,
            Some(op) => Expr::Prim(op, runtime),
            None if params == 0 => Expr::Global(gid),
            None => Expr::Call(gid, runtime),
        };
        Ok(apply(call, rest))
    }

    /// `foldComp done call c` with its runtime arguments `runtime`: a
    /// `handle`'s fold, which resumes lazily where its carrier (the fourth
    /// argument, erased) is a computation (docs/proposals/effect-runtime.md
    /// §9.2): `EffectFoldLazy` for a `Comp`, `EffectFoldIn` testing the row
    /// at run time for `CompIn e t`, and the eager fold otherwise (a fold
    /// used as a value, too, is eager).
    fn fold(&mut self, args: &[&Term], mut runtime: Vec<Expr>) -> Result<Expr> {
        let effect = self.effect.as_ref().expect("`foldComp` is native");
        let carrier = args.get(3).map(|c| effect.carrier(c));
        let op = match carrier {
            Some(Carrier::Tree) => EffectOp::FoldLazy,
            Some(Carrier::Row(row)) => match self.expr(row)? {
                Expr::Erased => EffectOp::Fold,
                row => {
                    runtime.insert(0, row);
                    EffectOp::FoldIn
                }
            },
            Some(Carrier::Value) | None => EffectOp::Fold,
        };
        Ok(Expr::Prim(PrimOp::Effect(op), runtime))
    }

    fn global(&self, id: DefId) -> Result<(GlobalId, u32, Option<PrimOp>)> {
        self.global_of.get(&id).copied().ok_or_else(|| {
            internal(format!(
                "`{}` is used but wasn't found to be reachable",
                self.g.def(id).name
            ))
        })
    }

    /// `Bool.ifThenElse [a] c (_ => t) (_ => e)` as a test with two
    /// branches, no closures. A branch's parameter is a proof of `Unit`, so
    /// it's erased.
    fn if_(&mut self, args: &[&Term]) -> Result<Expr> {
        let cond = self.expr(args[1])?;
        let then = self.branch(args[2])?;
        let otherwise = self.branch(args[3])?;
        let rest = self.exprs(&args[4..])?;
        Ok(apply(
            Expr::If(Box::new(cond), Box::new(then), Box::new(otherwise)),
            rest,
        ))
    }

    fn branch(&mut self, term: &Term) -> Result<Expr> {
        if let Term::Lam(_, _, body) = strip(term) {
            self.env.push(Bind::Erased);
            let out = self.expr(body);
            self.env.pop();
            return out;
        }
        let f = self.expr(term)?;
        Ok(apply(f, vec![Expr::Erased]))
    }

    /// Consecutive lambdas, as one closure capturing the outer variables
    /// its body reads.
    fn lambda(&mut self, term: &Term) -> Result<Expr> {
        if let Term::Lam(_, _, body) = strip(term)
            && is_done_continuation(self.g, body)
        {
            return Ok(Expr::DoneK);
        }
        let mut params = 0;
        let mut body = strip(term);
        while let Term::Lam(_, _, inner) = body {
            params += 1;
            body = strip(inner);
        }
        let mut captures = Vec::new();
        let code = self.frame_body(&vec![false; params], |cx| {
            let out = cx.expr(body);
            captures = cx.frame().captures.clone();
            out
        })?;
        // What it captures, read in the frame that makes it (which may
        // capture them in turn).
        let sources = captures.iter().map(|level| self.level(*level)).collect();
        let id = LambdaId(u32::try_from(self.lambdas.len()).expect("lambdas fit"));
        self.lambdas.push(Lambda {
            params: u32::try_from(params).expect("params fit"),
            captures: u32::try_from(captures.len()).expect("captures fit"),
            body: code,
        });
        Ok(Expr::Closure(id, sources))
    }

    /// A `let` the kernel marked skipped (a proof, a type, or unused) is
    /// nothing; otherwise its value is computed once, before the body.
    fn let_(&mut self, value: &Term, body: &Term, erased: bool) -> Result<Expr> {
        let value = if erased {
            Expr::Erased
        } else {
            self.expr(value)?
        };
        let mark = self.mark();
        if matches!(value, Expr::Erased) {
            self.env.push(Bind::Erased);
            let out = self.expr(body);
            self.leave(mark);
            return out;
        }
        let slot = self.bind_slot();
        let out = self.expr(body);
        self.leave(mark);
        Ok(Expr::Let(slot, Box::new(value), Box::new(out?)))
    }

    fn ctor(&mut self, term: &Term, d: DataId, c: usize, args: &[Rc<Term>]) -> Result<Expr> {
        let data = self.g.data(d);
        if data.sort == Sort::Prop {
            return Ok(Expr::Erased);
        }
        if Some(d) == self.repr.text {
            // A string: a literal if the characters are, otherwise made from
            // the list.
            return Ok(match text_literal(&args[0]) {
                Some(text) => Expr::Lit(Lit::Text(text.into())),
                None => Expr::Prim(
                    PrimOp::Text(TextNative::TextFromList),
                    vec![self.expr(&args[0])?],
                ),
            });
        }
        if Some(d) == self.repr.nat {
            // Count the `Succ`s: `Succ (Succ x)` is `x + 2`, and a literal is
            // just a number.
            let mut count = 0u64;
            let mut inner = term;
            while let Term::Ctor(_, 1, succ) = inner.strip_loc() {
                count += 1;
                inner = &succ[0];
            }
            return Ok(match (inner.strip_loc(), count) {
                (Term::Ctor(_, 0, _), n) => Expr::Lit(Lit::Nat(BigUint::from(n))),
                (Term::Nat(k), n) => Expr::Lit(Lit::Nat(&**k + n)),
                (_, n) => Expr::Prim(
                    PrimOp::Nat(Native::Add),
                    vec![self.expr(inner)?, Expr::Lit(Lit::Nat(BigUint::from(n)))],
                ),
            });
        }
        if Some(d) == self.repr.float {
            // `{ bits = b, valid = _ }`: a literal if `b` is a number,
            // otherwise the double made from the bits.
            return Ok(
                match self
                    .nat_literal(&args[0])
                    .and_then(|b| u64::try_from(b).ok())
                {
                    Some(bits) => Expr::Lit(Lit::Float(bits)),
                    None => Expr::Prim(
                        PrimOp::Float(FloatPrim::FromBits),
                        vec![self.expr(&args[0])?],
                    ),
                },
            );
        }
        if Some(d) == self.repr.int {
            // `OfNat n` is `n`, and `NegSucc n` is `-n - 1`.
            return Ok(match (c, self.nat_literal(&args[0])) {
                (0, Some(n)) => Expr::Lit(Lit::Int(BigInt::from(n))),
                (_, Some(n)) => Expr::Lit(Lit::Int(-BigInt::from(n + 1u32))),
                (0, None) => {
                    Expr::Prim(PrimOp::Int(IntNative::NatToInt), vec![self.expr(&args[0])?])
                }
                (_, None) => Expr::Prim(PrimOp::NegSucc, vec![self.expr(&args[0])?]),
            });
        }
        // A record with one run-time field is that field (D866).
        if let Some(i) = data.unboxed_field() {
            return self.expr(&args[i]);
        }
        let t = self.type_id(d);
        let mut fields = Vec::new();
        for (erased, arg) in data.ctors[c].field_erased.iter().zip(args) {
            if !erased {
                fields.push(self.expr(arg)?);
            }
        }
        Ok(Expr::Ctor(t, u32::try_from(c).expect("ctors fit"), fields))
    }

    /// The number a `Nat` term is, if it's written out: `Succ`s around
    /// `Zero` or a compact number.
    fn nat_literal(&self, term: &Term) -> Option<BigUint> {
        let mut count = 0u64;
        let mut term = term.strip_loc();
        loop {
            match term {
                Term::Nat(k) => return Some(&**k + count),
                Term::Ctor(d, 0, _) if Some(*d) == self.repr.nat => {
                    return Some(BigUint::from(count));
                }
                Term::Ctor(d, 1, succ) if Some(*d) == self.repr.nat => {
                    count += 1;
                    term = succ[0].strip_loc();
                }
                _ => return None,
            }
        }
    }

    fn case(&mut self, ix: usize, d: DataId, branches: &[Branch]) -> Result<Expr> {
        let data = self.g.data(d);
        if data.sort == Sort::Prop {
            // The proof doesn't exist at runtime. Matching on it into data is
            // only allowed for at most one constructor with only proof
            // fields, so that branch is taken.
            let Some(branch) = branches.first() else {
                return Ok(Expr::Unreachable);
            };
            let mark = self.mark();
            for _ in &data.ctors[0].fields {
                self.env.push(Bind::Erased);
            }
            let out = match &branch.body {
                Some(body) => self.expr(body),
                None => Ok(Expr::Unreachable),
            };
            self.leave(mark);
            return out;
        }
        if let Some(field) = data.unboxed_field()
            && Some(d) != self.repr.float
        {
            // A record stored as its one run-time field (D866): the field is
            // the value matched, so its level stands for the scrutinee's own
            // variable, and nothing is taken apart.
            let Some(branch) = branches.first() else {
                return Ok(Expr::Unreachable);
            };
            let bound = self.env[self.env.len() - 1 - ix];
            let mark = self.mark();
            for i in 0..data.ctors[0].fields.len() {
                self.env.push(if i == field { bound } else { Bind::Erased });
            }
            let out = match &branch.body {
                Some(body) => self.expr(body),
                None => Ok(Expr::Unreachable),
            };
            self.leave(mark);
            return out;
        }
        let scrutinee = self.var(ix);
        if Some(d) == self.repr.float {
            // A `Float` is a double: matching its record gives its bits
            // (the proof field is erased).
            let Some(branch) = branches.first() else {
                return Ok(Expr::Unreachable);
            };
            let mark = self.mark();
            let slot = self.bind_slot();
            self.env.push(Bind::Erased);
            let body = match &branch.body {
                Some(body) => self.expr(body),
                None => Ok(Expr::Unreachable),
            };
            let used = self.slot_used(slot);
            self.leave(mark);
            let body = body?;
            return Ok(if used {
                Expr::Let(
                    slot,
                    Box::new(Expr::Prim(PrimOp::Float(FloatPrim::Bits), vec![scrutinee])),
                    Box::new(body),
                )
            } else {
                body
            });
        }
        let kind = if Some(d) == self.repr.nat {
            MatchKind::Nat
        } else if Some(d) == self.repr.int {
            MatchKind::Int
        } else if Some(d) == self.repr.text {
            MatchKind::Text
        } else {
            MatchKind::Data(self.type_id(d))
        };
        let mut arms = Vec::new();
        for (c, branch) in branches.iter().enumerate() {
            let mark = self.mark();
            let mut fields = Vec::new();
            let mut runtime = 0u32;
            for erased in &data.ctors[c].field_erased {
                if *erased {
                    self.env.push(Bind::Erased);
                } else {
                    fields.push((runtime, self.bind_slot()));
                    runtime += 1;
                }
            }
            let body = match &branch.body {
                Some(body) => self.expr(body),
                // An impossible branch (docs/proposals/indexed-families.md
                // §6.8): never reached by a well-typed value.
                None => Ok(Expr::Unreachable),
            };
            fields.retain(|(_, slot)| self.slot_used(*slot));
            self.leave(mark);
            arms.push(Arm {
                ctor: u32::try_from(c).expect("ctors fit"),
                fields,
                body: body?,
            });
        }
        Ok(Expr::Match(Box::new(scrutinee), kind, arms))
    }

    fn num_case(&mut self, ix: usize, arms: &[NumArm], default: &Term) -> Result<Expr> {
        let scrutinee = self.var(ix);
        let arms = arms
            .iter()
            .map(|arm| Ok(((*arm.value).clone(), self.expr(&arm.body)?)))
            .collect::<Result<Vec<_>>>()?;
        let default = self.expr(default)?;
        Ok(Expr::NumSwitch(
            Box::new(scrutinee),
            arms,
            Box::new(default),
        ))
    }
}

/// A term without its locations and annotations.
fn strip(term: &Term) -> &Term {
    let mut term = term;
    while let Term::Loc(_, t) | Term::Ann(t, _) = term {
        term = t;
    }
    term
}

/// `f` applied to `args`, if there are any.
fn apply(f: Expr, args: Vec<Expr>) -> Expr {
    if args.is_empty() {
        f
    } else {
        Expr::Apply(Box::new(f), args)
    }
}
