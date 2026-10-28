//! Calls modulo a constructor, so that a function like `List.map` doesn't
//! keep a frame per element (docs/core.md, "Tail calls as loops"; the JS
//! backend's `cons` mode makes the same functions loops).
//!
//! A function whose result, in some branch, is a constructor with a call to
//! the function itself in one of its fields (`Cons (f x) (map xs f)`), or in
//! a field of a constructor in a field, is run in destination-passing style
//! (the OCaml manual's "The 'Tail Modulo Constructor' program
//! transformation"; Leijen and Lorenzen, "Tail Recursion Modulo Context",
//! POPL 2023, §2 and §5). The function `g` gets a twin `g'` with two more
//! parameters, a cell and the index of its field to be filled. `g'` builds
//! the constructor with a hole where the call was, fills the hole of the
//! cell it was given with the new constructor, and tail-calls itself with
//! the new cell and the hole's index. A branch that isn't a constructor
//! with a call (`Nil`, or a plain tail call) fills the hole with its value
//! and ends. `g` is the twin called with a new cell of one field, and
//! returns that field.
//!
//! - **Which calls.** A constructor with exactly one field that is a call to
//!   the function (or a variable bound to one), or a constructor with
//!   exactly one such field, recursively. A `let` of a call whose variable
//!   is only used that way in the branches of the body is the call there
//!   (`List.filter`'s helper, inlined: `let rest := filter xs p; if p x then
//!   Cons x rest else rest`).
//! - **Helpers.** A tail call of another function with the call as an
//!   argument (`List.concat`'s `append xs (concat xss)`) is a call of a copy
//!   of the helper that takes the argument's place by the call itself, where
//!   the helper passes that parameter on unchanged in its own recursion
//!   (`append`'s `rest`). The copy and the function call each other in tail
//!   position and are twinned together.
//! - **All or nothing.** A function is only twinned if every call in it to
//!   the functions twinned with it is a turn of the loop, and every branch
//!   ends in a value, a call of a function that can't come back to it, or a
//!   turn: a call of a closure or of an effect native might go on to call
//!   the function, which the twin would no longer do as a tail call.
//! - **Effects.** A cell is created before the call that fills it and is
//!   reachable only from the loop, which is the only code running until it
//!   ends, so nothing sees a cell with a hole and a continuation can't
//!   capture one. The effect runtime's continuations are heap data and
//!   its natives call functions on the machine's frames, which finish
//!   before they return ([`crate::effect`]); the runner's captured frames
//!   ([`crate::run`]) are its own and never include a function's. A handler
//!   that resumes more than once runs the function's code once for each
//!   resumption, each from the start with a new cell. A function with an
//!   effectful callback is generic over its row, and its recursive call is
//!   inside a continuation (`bindIn e (f x) (y => …)`) that the effect
//!   natives call, so it isn't twinned; the empty-row variant
//!   ([`crate::specialise`]) is, as in the JS backend.

use std::rc::Rc;
use stitchwort_core::collections::HashMap;

use num_bigint::BigUint;
use stitchwort_core::DefId;

use crate::ir::{
    Arm, Body, Expr, Global, GlobalId, GlobalKind, HoleOp, Lit, PrimOp, Program, Slot,
};
use crate::opt::{MAX_NESTING, nesting, reads, size};

/// The largest helper (in nodes) that is copied.
const MAX_HELPER: usize = 400;
/// The most functions twinned together.
const MAX_MEMBERS: usize = 4;

/// Turns the functions of `program` that build a constructor around a call
/// to themselves into loops.
pub fn apply(program: &mut Program) {
    let count = program.globals.len();
    let graph = Graph::new(program);
    let mut twins: Vec<Global> = Vec::new();
    // Put in once every function has been looked at: helpers are copied from
    // the functions as they were.
    let mut wrappers = Vec::new();
    for i in 0..count {
        let first = count + twins.len();
        let Some(members) = build(program, &graph, i, first) else {
            continue;
        };
        let params = members[0].params;
        for (n, member) in members.into_iter().enumerate() {
            // A copy of a helper is numbered by its global, so names are
            // unique.
            let name = if n == 0 {
                format!("{}[cells]", member.name)
            } else {
                format!("{}[cells#{}]", member.name, count + twins.len())
            };
            twins.push(Global {
                name: name.into(),
                def: member.def,
                kind: GlobalKind::Function {
                    params: member.params + 2,
                    body: Body {
                        frame: member.frame,
                        expr: member.expr,
                    },
                },
            });
        }
        // The function: its twin, called with a new cell.
        let twin = GlobalId(u32::try_from(first).expect("globals fit"));
        let mut args: Vec<Expr> = (0..params).map(Expr::Local).collect();
        args.push(Expr::Local(params));
        args.push(nat(0));
        let wrapper = Expr::Let(
            params,
            Box::new(Expr::Prim(PrimOp::Hole(HoleOp::New), Vec::new())),
            Box::new(Expr::Let(
                params + 1,
                Box::new(Expr::Call(twin, args)),
                Box::new(Expr::Prim(
                    PrimOp::Hole(HoleOp::Take),
                    vec![Expr::Local(params)],
                )),
            )),
        );
        wrappers.push((i, params, wrapper));
    }
    for (i, params, wrapper) in wrappers {
        program.globals[i].kind = GlobalKind::Function {
            params,
            body: Body {
                frame: params + 2,
                expr: wrapper,
            },
        };
    }
    program.globals.append(&mut twins);
}

fn nat(n: u32) -> Expr {
    Expr::Lit(Lit::Nat(BigUint::from(n)))
}

/// A function that is twinned.
struct Member {
    /// What calls to it are called: its global, or for a copy of a helper
    /// a number no global has.
    id: GlobalId,
    name: Rc<str>,
    def: DefId,
    params: u32,
    /// The body with room for the twin's two more parameters, `params` and
    /// `params + 1`; then the twin's body.
    expr: Expr,
    frame: u32,
}

/// The twins of global `i` and of the helpers it is twinned with, the first
/// of which is `i`'s, whose ids are `first` on; or `None` if it isn't to be
/// twinned.
fn build(program: &Program, graph: &Graph, i: usize, first: usize) -> Option<Vec<Member>> {
    let global = &program.globals[i];
    let GlobalKind::Function { params, body } = &global.kind else {
        return None;
    };
    // The passes here recurse over the body.
    if nesting(&body.expr) > MAX_NESTING {
        return None;
    }
    let mut cx = Cx {
        program,
        first,
        members: vec![Member {
            id: GlobalId(u32::try_from(i).expect("globals fit")),
            name: global.name.clone(),
            def: global.def,
            params: *params,
            expr: shift(&body.expr, *params, 2),
            frame: body.frame + 2,
        }],
        next: 0,
        built: false,
        bad: false,
        leaf_calls: Vec::new(),
        holes: HashMap::default(),
        specialised: HashMap::default(),
    };
    let mut at = 0;
    while at < cx.members.len() {
        cx.next = cx.members[at].frame;
        cx.holes.clear();
        let expr = std::mem::replace(&mut cx.members[at].expr, Expr::Unreachable);
        let dest = Expr::Local(cx.members[at].params);
        let index = Expr::Local(cx.members[at].params + 1);
        cx.members[at].expr = cx.tail_in(&expr, &dest, &index);
        cx.members[at].frame = cx.next;
        at += 1;
    }
    if !cx.built || cx.bad {
        return None;
    }
    // No call to a twinned function is left that isn't a turn.
    for member in &cx.members {
        let used = uses(program, &member.expr);
        if cx.members.iter().any(|m| used.contains(&m.id)) {
            return None;
        }
    }
    // A function a branch ends by calling doesn't come back to this one.
    let me = cx.members[0].id;
    if cx.leaf_calls.iter().any(|h| graph.reaches(*h, me)) {
        return None;
    }
    Some(cx.members)
}

struct Cx<'p> {
    program: &'p Program,
    /// The id of the first member's twin; the next member's is the next.
    first: usize,
    members: Vec<Member>,
    /// The next unused slot of the member being turned into a twin.
    next: Slot,
    /// Whether any branch builds a constructor around a call.
    built: bool,
    /// Whether a branch ends in something that may go on to call a twinned
    /// function (a call of a closure, or an effect native).
    bad: bool,
    /// The functions that branches end by calling.
    leaf_calls: Vec<GlobalId>,
    /// The variables that stand for a call of a member, with its arguments.
    holes: HashMap<Slot, (usize, Vec<Expr>)>,
    /// The copies of helpers made, by what they were made from.
    specialised: HashMap<String, usize>,
}

impl Cx<'_> {
    fn fresh(&mut self) -> Slot {
        self.next += 1;
        self.next - 1
    }

    fn member(&self, id: GlobalId) -> Option<usize> {
        self.members.iter().position(|m| m.id == id)
    }

    fn twin(&self, member: usize) -> GlobalId {
        GlobalId(u32::try_from(self.first + member).expect("globals fit"))
    }

    /// The member and arguments of the call `e` is, or stands for.
    fn call(&self, e: &Expr) -> Option<(usize, Vec<Expr>)> {
        match e {
            Expr::Call(g, args) => {
                let m = self.member(*g)?;
                (args.len() == self.members[m].params as usize).then(|| (m, args.clone()))
            }
            Expr::Local(s) => self.holes.get(s).cloned(),
            _ => None,
        }
    }

    /// Which field of the constructor with these `fields` is a call, or has
    /// a call in a constructor, if exactly one is.
    fn hole(&self, fields: &[Expr]) -> Option<usize> {
        let mut found = None;
        for (i, field) in fields.iter().enumerate() {
            let is_hole = match field {
                Expr::Ctor(_, _, inner) => self.hole(inner).is_some(),
                other => self.call(other).is_some(),
            };
            if is_hole {
                if found.is_some() {
                    return None;
                }
                found = Some(i);
            }
        }
        found
    }

    /// `e`, in tail position in member `at`, for its twin: each branch
    /// fills the hole `index` of the cell `dest`, or is a turn.
    fn tail_in(&mut self, e: &Expr, dest: &Expr, index: &Expr) -> Expr {
        match e {
            Expr::Let(s, value, body) => {
                if let Some(hole) = self.call(value)
                    && !matches!(**value, Expr::Local(_))
                {
                    // The variable is the call where the body uses it as
                    // one, in tail position or in a constructor there. If
                    // it is read some other way, the `let` stays.
                    self.holes.insert(*s, hole);
                    let rest = self.tail_in(body, dest, index);
                    self.holes.remove(s);
                    if reads(&rest, *s) == 0 {
                        return rest;
                    }
                }
                Expr::Let(*s, value.clone(), Box::new(self.tail_in(body, dest, index)))
            }
            Expr::Match(x, kind, arms) => Expr::Match(
                x.clone(),
                *kind,
                arms.iter()
                    .map(|arm| Arm {
                        ctor: arm.ctor,
                        fields: arm.fields.clone(),
                        body: self.tail_in(&arm.body, dest, index),
                    })
                    .collect(),
            ),
            Expr::NumSwitch(x, arms, default) => Expr::NumSwitch(
                x.clone(),
                arms.iter()
                    .map(|(n, b)| (n.clone(), self.tail_in(b, dest, index)))
                    .collect(),
                Box::new(self.tail_in(default, dest, index)),
            ),
            Expr::If(c, a, b) => Expr::If(
                c.clone(),
                Box::new(self.tail_in(a, dest, index)),
                Box::new(self.tail_in(b, dest, index)),
            ),
            Expr::Unreachable => Expr::Unreachable,
            Expr::Ctor(t, c, fields) if self.hole(fields).is_some() => {
                self.built = true;
                let i = self.hole(fields).expect("a hole");
                let cell = self.fresh();
                let filled = self.fresh();
                let mut made = fields.clone();
                made[i] = Expr::Erased;
                let next_index = nat(u32::try_from(i).expect("fields fit"));
                let rest = match &fields[i] {
                    inner @ Expr::Ctor(..) => self.tail_in(inner, &Expr::Local(cell), &next_index),
                    call => self.turn(call, Expr::Local(cell), next_index),
                };
                Expr::Let(
                    cell,
                    Box::new(Expr::Ctor(*t, *c, made)),
                    Box::new(Expr::Let(
                        filled,
                        Box::new(Expr::Prim(
                            PrimOp::Hole(HoleOp::Fill),
                            vec![dest.clone(), index.clone(), Expr::Local(cell)],
                        )),
                        Box::new(rest),
                    )),
                )
            }
            other => {
                if self.call(other).is_some() {
                    return self.turn(other, dest.clone(), index.clone());
                }
                if let Expr::Call(h, args) = other
                    && let Some((m, args)) = self.specialise(*h, args)
                {
                    return self.twin_call(m, args, dest.clone(), index.clone());
                }
                match other {
                    Expr::Call(g, _) => self.leaf_calls.push(*g),
                    Expr::Apply(..) | Expr::Prim(PrimOp::Effect(_), _) => self.bad = true,
                    _ => {}
                }
                Expr::Prim(
                    PrimOp::Hole(HoleOp::Fill),
                    vec![dest.clone(), index.clone(), other.clone()],
                )
            }
        }
    }

    /// The call `call` is, in the twin of its function, filling hole
    /// `index` of `dest`.
    fn turn(&self, call: &Expr, dest: Expr, index: Expr) -> Expr {
        let (m, args) = self.call(call).expect("a call");
        self.twin_call(m, args, dest, index)
    }

    fn twin_call(&self, member: usize, mut args: Vec<Expr>, dest: Expr, index: Expr) -> Expr {
        args.push(dest);
        args.push(index);
        Expr::Call(self.twin(member), args)
    }

    /// For a call of `helper` with `args`, one of which is a call to a
    /// member: the member that is a copy of `helper` with that parameter
    /// replaced by the call, and the arguments to call it with. The helper
    /// has to pass the parameter on unchanged in its recursion, and the copy
    /// takes the call's variables (slots of the caller) as parameters.
    fn specialise(&mut self, helper: GlobalId, args: &[Expr]) -> Option<(usize, Vec<Expr>)> {
        if self.member(helper).is_some() || self.members.len() >= MAX_MEMBERS {
            return None;
        }
        let global = self.program.globals.get(helper.0 as usize)?;
        let GlobalKind::Function { params, body } = &global.kind else {
            return None;
        };
        let params = *params;
        if args.len() != params as usize
            || size(&body.expr) > MAX_HELPER
            || nesting(&body.expr) > MAX_NESTING
        {
            return None;
        }
        let k = args.iter().position(|a| self.call(a).is_some())?;
        let k_slot = Slot::try_from(k).expect("params fit");
        if !passes_on(&body.expr, helper, k_slot, params) {
            return None;
        }
        let (target, call_args) = self.call(&args[k])?;
        // The call's variables become the copy's parameters after the
        // helper's others.
        let mut vars = Vec::new();
        let mut bound = Vec::new();
        for a in &call_args {
            slots(a, &mut vars, &mut bound);
        }
        let extra = u32::try_from(vars.len()).expect("slots fit");
        // Variables the call's arguments bind themselves get new locals after
        // the helper's.
        let local_base = body.frame + extra;
        let to_param = |s: Slot| {
            if let Some(j) = vars.iter().position(|v| *v == s) {
                params - 1 + u32::try_from(j).expect("fits")
            } else {
                let j = bound.iter().position(|v| *v == s).expect("a variable");
                local_base + u32::try_from(j).expect("fits")
            }
        };
        let call_there: Vec<Expr> = call_args
            .iter()
            .map(|a| rewrite(a, &|s| to_param(s), &|g, a| Expr::Call(g, a)))
            .collect();
        let key = format!("{helper:?}/{k}/{target}/{call_there:?}");
        let passed = |args: &[Expr]| -> Vec<Expr> {
            let mut passed: Vec<Expr> = args
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != k)
                .map(|(_, a)| a.clone())
                .collect();
            passed.extend(vars.iter().map(|v| Expr::Local(*v)));
            passed
        };
        if let Some(&m) = self.specialised.get(&key) {
            return Some((m, passed(args)));
        }
        // The helper's parameters but `k`, then the call's variables; the
        // parameter `k` becomes a local bound to the call, after them, and
        // the helper's locals follow it.
        let at = self.members.len();
        let id = GlobalId(u32::MAX - u32::try_from(at).expect("members fit"));
        let new_params = params - 1 + extra;
        let slot = |s: Slot| -> Slot {
            if s < k_slot {
                s
            } else if s == k_slot {
                new_params
            } else if s < params {
                s - 1
            } else {
                s + extra
            }
        };
        let recur = |g: GlobalId, a: Vec<Expr>| -> Expr {
            if g == helper {
                let mut rest: Vec<Expr> = a
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| *i != k)
                    .map(|(_, a)| a)
                    .collect();
                rest.extend((0..extra).map(|j| Expr::Local(params - 1 + j)));
                Expr::Call(id, rest)
            } else {
                Expr::Call(g, a)
            }
        };
        let inner = rewrite(&body.expr, &slot, &recur);
        let copy = Expr::Let(
            new_params,
            Box::new(Expr::Call(self.members[target].id, call_there)),
            Box::new(inner),
        );
        self.members.push(Member {
            id,
            name: global.name.clone(),
            def: global.def,
            params: new_params,
            expr: shift(&copy, new_params, 2),
            frame: body.frame + extra + 2 + u32::try_from(bound.len()).expect("slots fit"),
        });
        self.specialised.insert(key, at);
        Some((at, passed(args)))
    }
}

/// Whether `body`, of `helper` with `params` parameters, calls `helper`
/// only with parameter `k` passed on as it is. A reference to `k` that is
/// not a call's argument isn't checked here; the specialised copy binds `k`
/// to the call, so such a reference would read the call's result, and the
/// final check on the result rejects what that leaves unsound.
fn passes_on(body: &Expr, helper: GlobalId, k: Slot, params: u32) -> bool {
    let mut ok = true;
    each(body, &mut |e| match e {
        Expr::Call(g, args) if *g == helper => {
            ok &= args.len() == params as usize
                && matches!(args[k as usize], Expr::Local(s) if s == k);
        }
        Expr::PartialApp(g, _) | Expr::Global(g) if *g == helper => ok = false,
        _ => {}
    });
    ok
}

/// Calls `f` on `e` and every expression in it.
fn each(e: &Expr, f: &mut impl FnMut(&Expr)) {
    f(e);
    match e {
        Expr::Local(_)
        | Expr::Captured(_)
        | Expr::Global(_)
        | Expr::Erased
        | Expr::Lit(_)
        | Expr::DoneK
        | Expr::Unreachable => {}
        Expr::Call(_, a)
        | Expr::Prim(_, a)
        | Expr::PartialApp(_, a)
        | Expr::Closure(_, a)
        | Expr::Ctor(_, _, a) => a.iter().for_each(|x| each(x, f)),
        Expr::Apply(g, a) => {
            each(g, f);
            a.iter().for_each(|x| each(x, f));
        }
        Expr::Let(_, v, b) => {
            each(v, f);
            each(b, f);
        }
        Expr::Match(x, _, arms) => {
            each(x, f);
            arms.iter().for_each(|a| each(&a.body, f));
        }
        Expr::NumSwitch(x, arms, d) => {
            each(x, f);
            arms.iter().for_each(|(_, b)| each(b, f));
            each(d, f);
        }
        Expr::If(c, a, b) => {
            each(c, f);
            each(a, f);
            each(b, f);
        }
    }
}

/// Adds to `free` the slots `e` reads that it doesn't bind itself, and to
/// `bound` those it binds, that they don't have yet.
fn slots(e: &Expr, free: &mut Vec<Slot>, bound: &mut Vec<Slot>) {
    let mut read = Vec::new();
    each(e, &mut |e| match e {
        Expr::Local(s) if !read.contains(s) => read.push(*s),
        Expr::Let(s, _, _) if !bound.contains(s) => bound.push(*s),
        Expr::Match(_, _, arms) => {
            for arm in arms {
                for (_, s) in &arm.fields {
                    if !bound.contains(s) {
                        bound.push(*s);
                    }
                }
            }
        }
        _ => {}
    });
    for s in read {
        if !bound.contains(&s) && !free.contains(&s) {
            free.push(s);
        }
    }
}

/// `e` with each slot renamed by `slot` and each call rebuilt by `call`
/// (which is given its arguments, rewritten).
fn rewrite(
    e: &Expr,
    slot: &dyn Fn(Slot) -> Slot,
    call: &dyn Fn(GlobalId, Vec<Expr>) -> Expr,
) -> Expr {
    let all = |es: &[Expr]| {
        es.iter()
            .map(|x| rewrite(x, slot, call))
            .collect::<Vec<_>>()
    };
    let one = |x: &Expr| Box::new(rewrite(x, slot, call));
    match e {
        Expr::Local(s) => Expr::Local(slot(*s)),
        Expr::Captured(_) | Expr::Global(_) | Expr::Erased | Expr::Lit(_) | Expr::DoneK => {
            e.clone()
        }
        Expr::Unreachable => Expr::Unreachable,
        Expr::Call(g, a) => call(*g, all(a)),
        Expr::Prim(op, a) => Expr::Prim(*op, all(a)),
        Expr::PartialApp(g, a) => Expr::PartialApp(*g, all(a)),
        Expr::Apply(f, a) => Expr::Apply(one(f), all(a)),
        Expr::Closure(l, a) => Expr::Closure(*l, all(a)),
        Expr::Ctor(t, c, a) => Expr::Ctor(*t, *c, all(a)),
        Expr::Let(s, v, b) => Expr::Let(slot(*s), one(v), one(b)),
        Expr::Match(x, kind, arms) => Expr::Match(
            one(x),
            *kind,
            arms.iter()
                .map(|arm| Arm {
                    ctor: arm.ctor,
                    fields: arm.fields.iter().map(|(i, s)| (*i, slot(*s))).collect(),
                    body: rewrite(&arm.body, slot, call),
                })
                .collect(),
        ),
        Expr::NumSwitch(x, arms, d) => Expr::NumSwitch(
            one(x),
            arms.iter()
                .map(|(n, b)| (n.clone(), rewrite(b, slot, call)))
                .collect(),
            one(d),
        ),
        Expr::If(c, a, b) => Expr::If(one(c), one(a), one(b)),
    }
}

/// `e` with the slots from `from` on moved up by `by`.
fn shift(e: &Expr, from: Slot, by: u32) -> Expr {
    rewrite(e, &|s| if s >= from { s + by } else { s }, &|g, a| {
        Expr::Call(g, a)
    })
}

/// What each global uses, to tell whether a call can come back to a
/// function.
struct Graph {
    /// The globals each global's body uses (calls, partial applications and
    /// references), through the lambdas it makes.
    uses: Vec<Vec<GlobalId>>,
}

impl Graph {
    fn new(program: &Program) -> Graph {
        let uses = program
            .globals
            .iter()
            .map(|global| match &global.kind {
                GlobalKind::Function { body, .. } | GlobalKind::Constant { body } => {
                    uses(program, &body.expr)
                }
                GlobalKind::Native(_) => Vec::new(),
            })
            .collect();
        Graph { uses }
    }

    /// Whether global `from` can, by calls or references, reach `to`.
    fn reaches(&self, from: GlobalId, to: GlobalId) -> bool {
        let mut seen = vec![false; self.uses.len()];
        let mut work = vec![from];
        while let Some(g) = work.pop() {
            if g == to {
                return true;
            }
            if std::mem::replace(&mut seen[g.0 as usize], true) {
                continue;
            }
            work.extend(self.uses[g.0 as usize].iter().copied());
        }
        false
    }
}

/// The globals `e` uses, and those of the lambdas it makes, found without
/// recursing.
fn uses(program: &Program, root: &Expr) -> Vec<GlobalId> {
    let mut out = Vec::new();
    let mut seen = vec![false; program.lambdas.len()];
    let mut work = vec![root];
    while let Some(e) = work.pop() {
        match e {
            Expr::Global(g) => out.push(*g),
            Expr::Call(g, args) | Expr::PartialApp(g, args) => {
                out.push(*g);
                work.extend(args);
            }
            Expr::Closure(l, args) => {
                work.extend(args);
                if !std::mem::replace(&mut seen[l.0 as usize], true) {
                    work.push(&program.lambdas[l.0 as usize].body.expr);
                }
            }
            Expr::Local(_)
            | Expr::Captured(_)
            | Expr::Erased
            | Expr::Lit(_)
            | Expr::DoneK
            | Expr::Unreachable => {}
            Expr::Prim(_, args) | Expr::Ctor(_, _, args) => work.extend(args),
            Expr::Apply(f, args) => {
                work.push(f);
                work.extend(args);
            }
            Expr::Let(_, v, b) => {
                work.push(v);
                work.push(b);
            }
            Expr::Match(x, _, arms) => {
                work.push(x);
                work.extend(arms.iter().map(|a| &a.body));
            }
            Expr::NumSwitch(x, arms, d) => {
                work.push(x);
                work.extend(arms.iter().map(|(_, b)| b));
                work.push(d);
            }
            Expr::If(c, a, b) => {
                work.push(c);
                work.push(a);
                work.push(b);
            }
        }
    }
    out
}
