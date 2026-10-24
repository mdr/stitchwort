//! `ring` (docs/syntax.md, "ring"; docs/proposals/proof-automation.md
//! §6.2): a proof of an equation between `Nat`s or `Int`s whose two sides are
//! equal as polynomials in their atoms.
//!
//! ```text
//! ring               -- a = b
//! ring [h1, h2]      -- a = b, given h1: l1 = r1 and h2: l2 = r2
//! ```
//!
//! The proof is an application of a theorem from `Std.Ring`
//! (std/Ring/Sound.sw):
//!
//! ```text
//! Std.Ring.proveNat (MkEnv [nat atoms] [int atoms]) a b rfl
//! Std.Ring.proveNatWith env a b [MkPair l1 r1, …] rfl (Both h1 (… Trivial))
//! ```
//!
//! (and `proveInt`, `proveIntWith` at `Int`), where `a` and `b` are the goal's
//! sides as syntax over numbered atoms, and `rfl` is the kernel running the
//! library's normaliser on both and finding the same normal form. With
//! hypotheses, the sides checked are `a + (r1 + …)` and `b + (l1 + …)`, and
//! the theorem cancels the two sums. Nothing here is trusted: a mistake is a
//! type error.
//!
//! **Reading** follows the value, as `omega`'s does, so the syntax's meaning
//! computes to exactly the side it reads: a number is `NNum`, `k + x` (what
//! `Succ` makes) is `NSucc` or `NAdd (NNum k)`, a stuck `a + b` or `a * b` is
//! `NAdd` or `NMul`; at `Int`, `Int.add`, `Int.mul`, `Int.neg` and `Int.sub`
//! are `ZAdd`, `ZMul`, `ZNeg` and `ZSub`, and `OfNat e` and `NegSucc e` read
//! `e` as a `Nat` side. A call that is kept folded (docs/proposals/folded-calls.md)
//! is read as what it unfolds to when that is arithmetic (`Nat.pow x 2`,
//! `Nat.toInt n`, `writeTimes k b (Succ n)`), and is otherwise an atom
//! written as the call (`multiplier k n`, `Nat.pow 10 k`). Anything else is an
//! atom: two subterms are one atom if they're the same term, or if a bounded
//! conversion check says so.
//!
//! **Checking** happens here first, with the same normal form computed in
//! Rust, so a failure can show both normal forms and their difference over
//! the atoms by name (`E-RING`). On success the term is checked here the way
//! the kernel will (the library's normal forms convert, and the theorem's
//! statement is the goal), so a bug is reported as an internal error naming
//! `ring`.

use std::collections::BTreeMap;
use std::rc::Rc;
use std::sync::LazyLock;

use num_bigint::{BigInt, BigUint, Sign};
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, conv, force};
use stitchwort_core::{DataId, DefId, Limits, Term, Value};
use stitchwort_syntax::ast::{self, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::Global;
use crate::check::{Ctx, Result, builtin_ctor, builtin_data, builtin_def, infer, insert};

/// The library names the emitted proofs use: the pre-pass loads their files
/// wherever `ring` is written (`module.rs`, `free_names`).
const LIBRARY: &[&str] = &[
    "Std.Ring.proveNat",
    "Std.Ring.proveInt",
    "Std.Ring.proveNatWith",
    "Std.Ring.proveIntWith",
    "Std.Ring.NExpr.poly",
    "Std.Ring.ZExpr.poly",
];

pub(crate) static LIBRARY_NAMES: LazyLock<Vec<ast::Name>> = LazyLock::new(|| {
    LIBRARY
        .iter()
        .map(|text| ast::Name {
            text: (*text).to_string(),
            span: Span::NOWHERE,
        })
        .collect()
});

/// `ring` where nothing says what it should prove.
pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-RING", "`ring` needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(ring: a * (b + c) = a * b + a * c)`")
}

/// `ring` against the goal `expected`.
pub(crate) fn check_ring(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Ring { facts, span } = expr else {
        unreachable!("only called on `ring`")
    };
    let span = *span;
    let lib = Lib::new(cx, span)?;
    let goal = force(cx.g(), expected.clone())?;
    let Some((sort, l, r)) = equation(cx, &lib, &goal)? else {
        return Err(Diagnostic::error(
            "E-RING",
            format!("`ring` can't prove `{}`", cx.show(expected)),
        )
        .with_label(span, "this goal isn't an equation between `Nat`s or `Int`s")
        .with_note(
            "`ring` proves `a = b` where `a` and `b` are `Nat`s or `Int`s built from `+`, `*`, numbers and atoms (and `-` at `Int`) that are equal as polynomials",
        ));
    };
    let mut hyps = Vec::new();
    for fact in facts {
        let (term, ty) = infer(cx, fact)?;
        let (term, ty) = insert(cx, term, ty)?;
        let forced = force(cx.g(), ty.clone())?;
        match equation(cx, &lib, &forced)? {
            Some((s, hl, hr)) if s == sort => hyps.push(Hyp {
                proof: term,
                ty,
                l: hl,
                r: hr,
                span: fact.span(),
            }),
            _ => {
                return Err(Diagnostic::error(
                    "E-RING",
                    format!(
                        "`ring` takes equations between `{}`s, and this is `{}`",
                        sort.name(),
                        cx.show(&ty)
                    ),
                )
                .with_label(fact.span(), "not an equation of the goal's type")
                .with_note(format!(
                    "each hypothesis of `ring [h1, h2]` proves `l = r` between `{}`s, like the goal",
                    sort.name()
                )));
            }
        }
    }

    let mut reader = Reader::default();
    let unknown = |cx: &Ctx| {
        Diagnostic::error(
            "E-RING",
            format!("`ring` needs to know the goal `{}`", cx.show(expected)),
        )
        .with_label(span, "part of the goal's arithmetic isn't known yet")
        .with_note("give the missing parts, for example with a type on a `let` or an argument")
    };
    let Ok(a) = reader.read(cx, &lib, sort, &l)? else {
        return Err(unknown(cx));
    };
    let Ok(b) = reader.read(cx, &lib, sort, &r)? else {
        return Err(unknown(cx));
    };
    let mut sides = Vec::new();
    for h in &hyps {
        let (Ok(hl), Ok(hr)) = (
            reader.read(cx, &lib, sort, &h.l)?,
            reader.read(cx, &lib, sort, &h.r)?,
        ) else {
            return Err(Diagnostic::error(
                "E-RING",
                format!("`ring` needs to know the hypothesis `{}`", cx.show(&h.ty)),
            )
            .with_label(h.span, "part of this equation isn't known yet"));
        };
        sides.push((hl, hr));
    }

    // The sides checked: with hypotheses, `a + (r1 + …)` and `b + (l1 + …)`.
    let sum = |terms: Vec<&Side>| -> Side {
        terms
            .into_iter()
            .rev()
            .fold(Side::zero(sort), |acc, t| Side::add(t.clone(), acc))
    };
    let (checked_a, checked_b) = if sides.is_empty() {
        (a.clone(), b.clone())
    } else {
        (
            Side::add(a.clone(), sum(sides.iter().map(|(_, r)| r).collect())),
            Side::add(b.clone(), sum(sides.iter().map(|(l, _)| l).collect())),
        )
    };
    let pa = checked_a.poly();
    let pb = checked_b.poly();
    if pa != pb {
        return Err(different(
            cx,
            &reader,
            sort,
            expected,
            &pa,
            &pb,
            !hyps.is_empty(),
            span,
        ));
    }
    emit(
        cx, &lib, sort, expected, &reader, &a, &b, &sides, &hyps, span,
    )
}

/// What a hypothesis `ring [h]` was given.
struct Hyp {
    proof: Term,
    ty: Value,
    l: Value,
    r: Value,
    span: Span,
}

/// The type an equation is between.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sort {
    Nat,
    Int,
}

impl Sort {
    fn name(self) -> &'static str {
        match self {
            Sort::Nat => "Nat",
            Sort::Int => "Int",
        }
    }
}

/// `l = r` at `Nat` or `Int`.
fn equation(cx: &Ctx, lib: &Lib, value: &Value) -> Result<Option<(Sort, Value, Value)>> {
    let Value::Eq(ty, l, r) = value else {
        return Ok(None);
    };
    let ty = force(cx.g(), (**ty).clone())?;
    let sort = match ty {
        Value::Data(d, _) if d == lib.nat => Sort::Nat,
        Value::Data(d, _) if d == lib.int => Sort::Int,
        _ => return Ok(None),
    };
    Ok(Some((sort, (**l).clone(), (**r).clone())))
}

/// The definitions and constructors the proof is made of.
struct Lib {
    prove_nat: DefId,
    prove_int: DefId,
    prove_nat_with: DefId,
    prove_int_with: DefId,
    npoly: DefId,
    zpoly: DefId,
    mk_env: (DataId, usize),
    natom: (DataId, usize),
    nnum: (DataId, usize),
    nadd: (DataId, usize),
    nmul: (DataId, usize),
    nsucc: (DataId, usize),
    zatom: (DataId, usize),
    zadd: (DataId, usize),
    zmul: (DataId, usize),
    zneg: (DataId, usize),
    zsub: (DataId, usize),
    zofnat: (DataId, usize),
    znegsucc: (DataId, usize),
    // The core's.
    add: DefId,
    mul: DefId,
    sub: DefId,
    div: DefId,
    modulo: DefId,
    int_add: DefId,
    int_mul: DefId,
    int_neg: DefId,
    int_sub: DefId,
    int_div: DefId,
    int_mod: DefId,
    nat: DataId,
    int: DataId,
    and: DataId,
    unit: DataId,
    nil: (DataId, usize),
    cons: (DataId, usize),
    mk_pair: (DataId, usize),
    of_nat: (DataId, usize),
    neg_succ: (DataId, usize),
}

impl Lib {
    fn new(cx: &Ctx, span: Span) -> Result<Lib> {
        let missing = |key: &str| {
            internal(
                span,
                format!("`{key}` isn't available (the library file that declares it isn't loaded)"),
            )
        };
        let def = |key: &str| match cx.e.named(key) {
            Some((Global::Def(id), _)) => Ok(*id),
            _ => Err(missing(key)),
        };
        let ctor = |key: &str| match cx.e.named(key) {
            Some((Global::Ctor(d, i), _)) => Ok((*d, *i)),
            _ => Err(missing(key)),
        };
        Ok(Lib {
            prove_nat: def("Std.Ring.proveNat")?,
            prove_int: def("Std.Ring.proveInt")?,
            prove_nat_with: def("Std.Ring.proveNatWith")?,
            prove_int_with: def("Std.Ring.proveIntWith")?,
            npoly: def("Std.Ring.NExpr.poly")?,
            zpoly: def("Std.Ring.ZExpr.poly")?,
            mk_env: ctor("Std.Ring.Env.MkEnv")?,
            natom: ctor("Std.Ring.NExpr.NAtom")?,
            nnum: ctor("Std.Ring.NExpr.NNum")?,
            nadd: ctor("Std.Ring.NExpr.NAdd")?,
            nmul: ctor("Std.Ring.NExpr.NMul")?,
            nsucc: ctor("Std.Ring.NExpr.NSucc")?,
            zatom: ctor("Std.Ring.ZExpr.ZAtom")?,
            zadd: ctor("Std.Ring.ZExpr.ZAdd")?,
            zmul: ctor("Std.Ring.ZExpr.ZMul")?,
            zneg: ctor("Std.Ring.ZExpr.ZNeg")?,
            zsub: ctor("Std.Ring.ZExpr.ZSub")?,
            zofnat: ctor("Std.Ring.ZExpr.ZOfNat")?,
            znegsucc: ctor("Std.Ring.ZExpr.ZNegSucc")?,
            add: builtin_def(cx, Builtin::Add)?,
            mul: builtin_def(cx, Builtin::Mul)?,
            sub: builtin_def(cx, Builtin::Sub)?,
            div: builtin_def(cx, Builtin::Div)?,
            modulo: builtin_def(cx, Builtin::Mod)?,
            int_add: builtin_def(cx, Builtin::IntAdd)?,
            int_mul: builtin_def(cx, Builtin::IntMul)?,
            int_neg: builtin_def(cx, Builtin::IntNeg)?,
            int_sub: builtin_def(cx, Builtin::IntSub)?,
            int_div: builtin_def(cx, Builtin::IntDiv)?,
            int_mod: builtin_def(cx, Builtin::IntMod)?,
            nat: builtin_data(cx, Builtin::Nat)?,
            int: builtin_data(cx, Builtin::Int)?,
            and: builtin_data(cx, Builtin::And)?,
            unit: builtin_data(cx, Builtin::Unit)?,
            nil: builtin_ctor(cx, Builtin::Nil)?,
            cons: builtin_ctor(cx, Builtin::Cons)?,
            mk_pair: builtin_ctor(cx, Builtin::MkPair)?,
            of_nat: builtin_ctor(cx, Builtin::OfNat)?,
            neg_succ: builtin_ctor(cx, Builtin::NegSucc)?,
        })
    }

    fn ctor(&self, which: (DataId, usize), fields: Vec<Term>) -> Term {
        Term::ctor(which.0, which.1, fields)
    }

    fn list(&self, items: Vec<Term>) -> Term {
        let mut list = self.ctor(self.nil, Vec::new());
        for item in items.into_iter().rev() {
            list = self.ctor(self.cons, vec![item, list]);
        }
        list
    }
}

fn nat_term(n: impl Into<BigUint>) -> Term {
    Term::Nat(Rc::new(n.into()))
}

fn internal(span: Span, message: String) -> Diagnostic {
    Diagnostic::error("E-RING-INTERNAL", "`ring` made a proof that doesn't check")
        .with_label(span, message)
        .with_note("this is a bug in the compiler's `ring`, not in the program")
}

/// A side read as syntax: `Nat`-valued or `Int`-valued.
#[derive(Clone, Debug)]
enum N {
    Atom(usize),
    Num(BigUint),
    Add(Box<N>, Box<N>),
    Mul(Box<N>, Box<N>),
    Succ(Box<N>),
}

#[derive(Clone, Debug)]
enum Z {
    Atom(usize),
    Add(Box<Z>, Box<Z>),
    Mul(Box<Z>, Box<Z>),
    Neg(Box<Z>),
    Sub(Box<Z>, Box<Z>),
    OfNat(N),
    NegSucc(N),
}

#[derive(Clone, Debug)]
enum Side {
    N(N),
    Z(Z),
}

impl Side {
    fn zero(sort: Sort) -> Side {
        match sort {
            Sort::Nat => Side::N(N::Num(BigUint::default())),
            Sort::Int => Side::Z(Z::OfNat(N::Num(BigUint::default()))),
        }
    }

    fn add(a: Side, b: Side) -> Side {
        match (a, b) {
            (Side::N(a), Side::N(b)) => Side::N(N::Add(Box::new(a), Box::new(b))),
            (Side::Z(a), Side::Z(b)) => Side::Z(Z::Add(Box::new(a), Box::new(b))),
            _ => unreachable!("both sides of one `ring` have the goal's type"),
        }
    }

    fn poly(&self) -> Poly {
        match self {
            Side::N(n) => n.poly(),
            Side::Z(z) => z.poly(),
        }
    }

    fn term(&self, lib: &Lib) -> Term {
        match self {
            Side::N(n) => n.term(lib),
            Side::Z(z) => z.term(lib),
        }
    }
}

impl N {
    fn poly(&self) -> Poly {
        match self {
            N::Atom(i) => Poly::var(2 * i),
            N::Num(k) => Poly::constant(BigInt::from(k.clone())),
            N::Add(a, b) => a.poly().add(&b.poly()),
            N::Mul(a, b) => a.poly().mul(&b.poly()),
            N::Succ(a) => a.poly().add(&Poly::constant(BigInt::from(1))),
        }
    }

    fn term(&self, lib: &Lib) -> Term {
        match self {
            N::Atom(i) => lib.ctor(lib.natom, vec![nat_term(*i as u64)]),
            N::Num(k) => lib.ctor(lib.nnum, vec![nat_term(k.clone())]),
            N::Add(a, b) => lib.ctor(lib.nadd, vec![a.term(lib), b.term(lib)]),
            N::Mul(a, b) => lib.ctor(lib.nmul, vec![a.term(lib), b.term(lib)]),
            N::Succ(a) => lib.ctor(lib.nsucc, vec![a.term(lib)]),
        }
    }
}

impl Z {
    fn poly(&self) -> Poly {
        match self {
            Z::Atom(i) => Poly::var(2 * i + 1),
            Z::Add(a, b) => a.poly().add(&b.poly()),
            Z::Mul(a, b) => a.poly().mul(&b.poly()),
            Z::Neg(a) => a.poly().neg(),
            Z::Sub(a, b) => a.poly().add(&b.poly().neg()),
            Z::OfNat(n) => n.poly(),
            Z::NegSucc(n) => n.poly().add(&Poly::constant(BigInt::from(1))).neg(),
        }
    }

    fn term(&self, lib: &Lib) -> Term {
        match self {
            Z::Atom(i) => lib.ctor(lib.zatom, vec![nat_term(*i as u64)]),
            Z::Add(a, b) => lib.ctor(lib.zadd, vec![a.term(lib), b.term(lib)]),
            Z::Mul(a, b) => lib.ctor(lib.zmul, vec![a.term(lib), b.term(lib)]),
            Z::Neg(a) => lib.ctor(lib.zneg, vec![a.term(lib)]),
            Z::Sub(a, b) => lib.ctor(lib.zsub, vec![a.term(lib), b.term(lib)]),
            Z::OfNat(n) => lib.ctor(lib.zofnat, vec![n.term(lib)]),
            Z::NegSucc(n) => lib.ctor(lib.znegsucc, vec![n.term(lib)]),
        }
    }
}

/// A polynomial: monomials (sorted variable lists, `Nat` atom `i` as `2i`,
/// `Int` atom `j` as `2j + 1`, as in the library) with nonzero coefficients.
/// The same normal form as `Std.Ring`'s, up to the order of the monomials.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct Poly(BTreeMap<Vec<usize>, BigInt>);

impl Poly {
    fn constant(c: BigInt) -> Poly {
        let mut p = Poly::default();
        p.insert(Vec::new(), c);
        p
    }

    fn var(v: usize) -> Poly {
        Poly(BTreeMap::from([(vec![v], BigInt::from(1))]))
    }

    fn insert(&mut self, vars: Vec<usize>, c: BigInt) {
        let entry = self.0.entry(vars).or_default();
        *entry += c;
        if *entry == BigInt::default() {
            self.0.retain(|_, c| *c != BigInt::default());
        }
    }

    fn add(&self, other: &Poly) -> Poly {
        let mut p = self.clone();
        for (vars, c) in &other.0 {
            p.insert(vars.clone(), c.clone());
        }
        p
    }

    fn mul(&self, other: &Poly) -> Poly {
        let mut p = Poly::default();
        for (va, ca) in &self.0 {
            for (vb, cb) in &other.0 {
                let mut vars = va.clone();
                vars.extend(vb);
                vars.sort_unstable();
                p.insert(vars, ca * cb);
            }
        }
        p
    }

    fn neg(&self) -> Poly {
        Poly(self.0.iter().map(|(v, c)| (v.clone(), -c)).collect())
    }
}

/// Why `a - b` on `Nat` is an atom.
const SUBTRACTION: &str = "truncated subtraction isn't a ring operation";

/// Reading stopped at an unsolved metavariable.
struct Unknown;

/// An atom: a `Nat` or `Int` subterm `ring` doesn't look inside.
struct Atom {
    value: Value,
    term: Term,
    sort: Sort,
    /// Why it's an atom, when it looks like arithmetic `ring` doesn't do.
    unsupported: Option<&'static str>,
}

#[derive(Default)]
struct Reader {
    atoms: Vec<Atom>,
    /// Each atom's number in its sort's list.
    index: Vec<usize>,
    nats: usize,
    ints: usize,
}

/// A definition applied to all its explicit and implicit arguments, kept as
/// the call (`Value::Call`) or stuck (`Value::Neutral`).
fn def_args(value: &Value) -> Option<(DefId, Vec<Value>)> {
    match value {
        Value::Neutral(Head::Def(id), spine) => {
            let args: Option<Vec<Value>> = spine
                .iter()
                .map(|e| match e {
                    Elim::App(v, _) => Some(v.clone()),
                    Elim::J { .. } => None,
                })
                .collect();
            Some((*id, args?))
        }
        Value::Call(id, spine, _) => Some((
            *id,
            stitchwort_core::value::call_args(spine)
                .into_iter()
                .map(|(v, _)| v)
                .collect(),
        )),
        _ => None,
    }
}

impl Reader {
    fn read(
        &mut self,
        cx: &Ctx,
        lib: &Lib,
        sort: Sort,
        value: &Value,
    ) -> Result<std::result::Result<Side, Unknown>> {
        Ok(match sort {
            Sort::Nat => self.read_nat(cx, lib, value)?.map(Side::N),
            Sort::Int => self.read_int(cx, lib, value)?.map(Side::Z),
        })
    }

    /// A folded call is read as its unfolding when that is arithmetic, and
    /// is otherwise an atom written as the call: `Some(atom value)`.
    fn unfold(
        &self,
        cx: &Ctx,
        lib: &Lib,
        sort: Sort,
        value: &Value,
    ) -> Result<(Value, Option<Value>)> {
        if !matches!(value, Value::Call(..)) {
            return Ok((force(cx.g(), value.clone())?, None));
        }
        let forced = force(cx.g(), value.clone())?;
        let arithmetic = match sort {
            Sort::Nat => {
                matches!(forced, Value::Nat(_) | Value::NatAdd(..))
                    || matches!(&forced, Value::Ctor(d, _, _) if *d == lib.nat)
                    || matches!(def_args(&forced), Some((id, _)) if id == lib.add || id == lib.mul)
            }
            Sort::Int => {
                matches!(&forced, Value::Ctor(d, _, _) if *d == lib.int)
                    || matches!(def_args(&forced), Some((id, _))
                        if [lib.int_add, lib.int_mul, lib.int_neg, lib.int_sub].contains(&id))
            }
        };
        Ok(if arithmetic {
            (forced, None)
        } else {
            (forced, Some(value.clone()))
        })
    }

    fn read_nat(
        &mut self,
        cx: &Ctx,
        lib: &Lib,
        value: &Value,
    ) -> Result<std::result::Result<N, Unknown>> {
        let (value, folded) = self.unfold(cx, lib, Sort::Nat, value)?;
        if let Some(call) = folded {
            return Ok(Ok(N::Atom(self.atom(cx, lib, Sort::Nat, call)?)));
        }
        let (k, base) = stitchwort_core::native::view(cx.g(), &value)?;
        let Some(base) = base else {
            return Ok(Ok(N::Num(k)));
        };
        if k != BigUint::default() {
            let inner = match self.read_nat(cx, lib, &base)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            return Ok(Ok(if k == BigUint::from(1u32) {
                N::Succ(Box::new(inner))
            } else {
                N::Add(Box::new(N::Num(k)), Box::new(inner))
            }));
        }
        let base = force(cx.g(), base)?;
        if let Value::Neutral(Head::Meta(_), _) = base {
            return Ok(Err(Unknown));
        }
        if let Some((id, args)) = def_args(&base)
            && (id == lib.add || id == lib.mul)
            && let [a, b] = args.as_slice()
        {
            let a = match self.read_nat(cx, lib, a)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            let b = match self.read_nat(cx, lib, b)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            let (a, b) = (Box::new(a), Box::new(b));
            return Ok(Ok(if id == lib.add {
                N::Add(a, b)
            } else {
                N::Mul(a, b)
            }));
        }
        Ok(Ok(N::Atom(self.atom(cx, lib, Sort::Nat, base)?)))
    }

    fn read_int(
        &mut self,
        cx: &Ctx,
        lib: &Lib,
        value: &Value,
    ) -> Result<std::result::Result<Z, Unknown>> {
        // `Int.add a b` and friends kept as calls are read without unfolding.
        if let Value::Call(..) = value
            && let Some((id, args)) = def_args(value)
            && let Some(z) = self.int_op(cx, lib, id, &args)?
        {
            return Ok(z);
        }
        let (value, folded) = self.unfold(cx, lib, Sort::Int, value)?;
        if let Some(call) = folded {
            return Ok(Ok(Z::Atom(self.atom(cx, lib, Sort::Int, call)?)));
        }
        if let Value::Neutral(Head::Meta(_), _) = value {
            return Ok(Err(Unknown));
        }
        if let Value::Ctor(d, c, fields) = &value
            && *d == lib.int
            && let [n] = fields.as_ref()
        {
            let n = match self.read_nat(cx, lib, n)? {
                Ok(t) => t,
                Err(u) => return Ok(Err(u)),
            };
            return Ok(Ok(if (*d, *c) == lib.of_nat {
                Z::OfNat(n)
            } else {
                debug_assert_eq!((*d, *c), lib.neg_succ);
                Z::NegSucc(n)
            }));
        }
        if let Some((id, args)) = def_args(&value)
            && let Some(z) = self.int_op(cx, lib, id, &args)?
        {
            return Ok(z);
        }
        Ok(Ok(Z::Atom(self.atom(cx, lib, Sort::Int, value)?)))
    }

    /// `Int.add`, `Int.mul`, `Int.neg` or `Int.sub` applied to `args`.
    fn int_op(
        &mut self,
        cx: &Ctx,
        lib: &Lib,
        id: DefId,
        args: &[Value],
    ) -> Result<Option<std::result::Result<Z, Unknown>>> {
        let binary = [lib.int_add, lib.int_mul, lib.int_sub];
        if binary.contains(&id)
            && let [a, b] = args
        {
            let a = match self.read_int(cx, lib, a)? {
                Ok(t) => Box::new(t),
                Err(u) => return Ok(Some(Err(u))),
            };
            let b = match self.read_int(cx, lib, b)? {
                Ok(t) => Box::new(t),
                Err(u) => return Ok(Some(Err(u))),
            };
            return Ok(Some(Ok(if id == lib.int_add {
                Z::Add(a, b)
            } else if id == lib.int_mul {
                Z::Mul(a, b)
            } else {
                Z::Sub(a, b)
            })));
        }
        if id == lib.int_neg
            && let [a] = args
        {
            return Ok(Some(match self.read_int(cx, lib, a)? {
                Ok(t) => Ok(Z::Neg(Box::new(t))),
                Err(u) => Err(u),
            }));
        }
        Ok(None)
    }

    /// The atom `value` is, adding it if it's new; its number in its sort's
    /// list.
    fn atom(&mut self, cx: &Ctx, lib: &Lib, sort: Sort, value: Value) -> Result<usize> {
        let term = cx.quote(&value)?;
        for (i, a) in self.atoms.iter().enumerate() {
            if a.sort == sort && crate::matching::same(&a.term, &term) {
                return Ok(self.index[i]);
            }
        }
        let g = cx.g();
        for (i, a) in self.atoms.iter().enumerate() {
            if a.sort != sort {
                continue;
            }
            let _op = g.budget.operation(Limits {
                work: 20_000,
                stack: 128 * 1024,
                size: 10_000,
                frames: 10_000,
            });
            if conv(g, cx.level(), &a.value, &value) == Ok(true) {
                return Ok(self.index[i]);
            }
        }
        let forced = force(g, value.clone())?;
        let unsupported = match def_args(&forced) {
            Some((id, _)) if id == lib.sub => Some(SUBTRACTION),
            Some((id, _)) if id == lib.div || id == lib.int_div => {
                Some("division isn't a ring operation")
            }
            Some((id, _)) if id == lib.modulo || id == lib.int_mod => {
                Some("a remainder isn't a ring operation")
            }
            _ if cx.show(&value).starts_with("Nat.pow ") => {
                Some("a power is multiplied out only when its exponent is a number")
            }
            _ => None,
        };
        let n = match sort {
            Sort::Nat => &mut self.nats,
            Sort::Int => &mut self.ints,
        };
        let i = *n;
        *n += 1;
        self.atoms.push(Atom {
            value,
            term,
            sort,
            unsupported,
        });
        self.index.push(i);
        Ok(i)
    }

    /// The atom at variable `v` (`2i` for `Nat` atom `i`, `2j + 1` for `Int`
    /// atom `j`).
    fn at_var(&self, v: usize) -> &Atom {
        let (sort, i) = if v % 2 == 0 {
            (Sort::Nat, v / 2)
        } else {
            (Sort::Int, v / 2)
        };
        let k = (0..self.atoms.len())
            .find(|&k| self.atoms[k].sort == sort && self.index[k] == i)
            .expect("every variable is an atom");
        &self.atoms[k]
    }

    /// The atoms of `sort`, in order, as terms for the environment.
    fn env_list(&self, cx: &Ctx, lib: &Lib, sort: Sort) -> Result<Term> {
        let mut items = Vec::new();
        for (a, _) in self
            .atoms
            .iter()
            .zip(&self.index)
            .filter(|(a, _)| a.sort == sort)
        {
            items.push(cx.quote_folded(&a.value)?);
        }
        Ok(lib.list(items))
    }
}

/// An atom as a message shows it, in brackets when it has an operator.
fn atom_text(cx: &Ctx, atom: &Atom) -> String {
    let s = cx.show(&atom.value);
    // An operator outside brackets: `a - b`, but not `Nat.pow 10 (k + 1)`.
    let mut depth = 0i32;
    let mut top = String::new();
    for ch in s.chars() {
        match ch {
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ if depth == 0 => top.push(ch),
            _ => {}
        }
    }
    let operator = [
        " + ", " - ", " * ", " / ", " % ", " |> ", " && ", " || ", "=>", "if ",
    ]
    .iter()
    .any(|op| top.contains(op));
    if operator || s.starts_with('-') {
        format!("({s})")
    } else {
        s
    }
}

/// A monomial as source syntax, without its sign: `2 * b * m`, `x * x`, `3`.
fn mono_text(cx: &Ctx, reader: &Reader, vars: &[usize], c: &BigInt) -> String {
    let magnitude = c.magnitude();
    let mut parts: Vec<String> = Vec::new();
    if vars.is_empty() || *magnitude != BigUint::from(1u32) {
        parts.push(magnitude.to_string());
    }
    for &v in vars {
        parts.push(atom_text(cx, reader.at_var(v)));
    }
    parts.join(" * ")
}

/// A polynomial as source syntax, highest degree first: `b * m * p + 2 * b`.
fn poly_text(cx: &Ctx, reader: &Reader, p: &Poly) -> String {
    let mut monos: Vec<(&Vec<usize>, &BigInt)> = p.0.iter().collect();
    if monos.is_empty() {
        return "0".into();
    }
    monos.sort_by(|(a, _), (b, _)| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));
    let mut out = String::new();
    for (k, (vars, c)) in monos.into_iter().enumerate() {
        let negative = c.sign() == Sign::Minus;
        let text = mono_text(cx, reader, vars, c);
        match (k, negative) {
            (0, false) => out.push_str(&text),
            (0, true) => {
                out.push('-');
                out.push_str(&text);
            }
            (_, false) => {
                out.push_str(" + ");
                out.push_str(&text);
            }
            (_, true) => {
                out.push_str(" - ");
                out.push_str(&text);
            }
        }
    }
    out
}

/// `E-RING`: the two sides' normal forms differ.
#[allow(clippy::too_many_arguments)]
fn different(
    cx: &Ctx,
    reader: &Reader,
    sort: Sort,
    expected: &Value,
    left: &Poly,
    right: &Poly,
    with_hyps: bool,
    span: Span,
) -> Diagnostic {
    let diff = left.add(&right.neg());
    let pick = |positive: bool| -> Poly {
        Poly(
            diff.0
                .iter()
                .filter(|(_, c)| (c.sign() == Sign::Plus) == positive)
                .map(|(v, c)| (v.clone(), if positive { c.clone() } else { -c }))
                .collect(),
        )
    };
    let (more, less) = (pick(true), pick(false));
    let mut parts = Vec::new();
    if !more.0.is_empty() {
        parts.push(format!("`{}` more", poly_text(cx, reader, &more)));
    }
    if !less.0.is_empty() {
        parts.push(format!("`{}` less", poly_text(cx, reader, &less)));
    }
    let mut d = Diagnostic::error(
        "E-RING",
        format!("`ring` can't prove `{}`", cx.show(expected)),
    )
    .with_label(span, "the two sides are different polynomials");
    if with_hyps {
        d = d.with_note(
            "with the hypotheses `l = r` added, the left side plus every `r` against the right side plus every `l`:",
        );
    }
    d = d
        .with_note(format!("left:  {}", poly_text(cx, reader, left)))
        .with_note(format!("right: {}", poly_text(cx, reader, right)))
        .with_note(format!("the left side has {}", parts.join(" and ")));
    for atom in reader.atoms.iter().filter(|a| a.unsupported.is_some()) {
        d = d.with_note(format!(
            "`{}` is an unknown to `ring`: {}",
            cx.show(&atom.value),
            atom.unsupported.unwrap_or_default()
        ));
    }
    let subtraction = |a: &&Atom| a.unsupported == Some(SUBTRACTION);
    if sort == Sort::Nat && reader.atoms.iter().any(|a| subtraction(&a)) {
        d = d.with_note("`omega` knows about `-` between `Nat`s, given the facts that bound it");
    }
    d
}

/// `f a1 … an`.
fn apps(f: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(f, Term::app)
}

/// Writes the proof and checks it the way the kernel will.
#[allow(clippy::too_many_arguments)]
fn emit(
    cx: &mut Ctx,
    lib: &Lib,
    sort: Sort,
    expected: &Value,
    reader: &Reader,
    a: &Side,
    b: &Side,
    sides: &[(Side, Side)],
    hyps: &[Hyp],
    span: Span,
) -> Result<Term> {
    let env = lib.ctor(
        lib.mk_env,
        vec![
            reader.env_list(cx, lib, Sort::Nat)?,
            reader.env_list(cx, lib, Sort::Int)?,
        ],
    );
    let (ta, tb) = (a.term(lib), b.term(lib));
    let poly = match sort {
        Sort::Nat => lib.npoly,
        Sort::Int => lib.zpoly,
    };
    // The sides the normal forms are of.
    let (checked_a, checked_b) = if sides.is_empty() {
        (ta.clone(), tb.clone())
    } else {
        let sum = |pick: &dyn Fn(&(Side, Side)) -> Term| -> Term {
            let zero = Side::zero(sort).term(lib);
            sides.iter().rev().fold(zero, |acc, s| {
                let add = match sort {
                    Sort::Nat => lib.nadd,
                    Sort::Int => lib.zadd,
                };
                lib.ctor(add, vec![pick(s), acc])
            })
        };
        let add = match sort {
            Sort::Nat => lib.nadd,
            Sort::Int => lib.zadd,
        };
        (
            lib.ctor(add, vec![ta.clone(), sum(&|(_, r)| r.term(lib))]),
            lib.ctor(add, vec![tb.clone(), sum(&|(l, _)| l.term(lib))]),
        )
    };
    let na = cx.eval(&Term::app(Term::Def(poly), checked_a))?;
    let nb = cx.eval(&Term::app(Term::Def(poly), checked_b))?;
    if !cx.unify(&na, &nb)? {
        return Err(internal(
            span,
            "the library's normal forms of the two sides differ, but the compiler's agree".into(),
        ));
    }
    let (prove, prove_with) = match sort {
        Sort::Nat => (lib.prove_nat, lib.prove_nat_with),
        Sort::Int => (lib.prove_int, lib.prove_int_with),
    };
    let mut args = vec![env, ta, tb];
    let (term, which) = if sides.is_empty() {
        let term = apps(Term::Def(prove), [args.clone(), vec![Term::Refl]].concat());
        (term, prove)
    } else {
        let pairs = lib.list(
            sides
                .iter()
                .map(|(l, r)| lib.ctor(lib.mk_pair, vec![l.term(lib), r.term(lib)]))
                .collect(),
        );
        let mut proofs = Term::ctor(lib.unit, 0, Vec::new());
        for h in hyps.iter().rev() {
            proofs = Term::ctor(lib.and, 0, vec![h.proof.clone(), proofs]);
        }
        args.push(pairs);
        let term = apps(
            Term::Def(prove_with),
            [args.clone(), vec![Term::Refl, proofs]].concat(),
        );
        (term, prove_with)
    };
    // The statement the theorem proves, and (with hypotheses) what their
    // proofs must prove; neither depends on `ok`.
    let g = cx.g();
    let shape = || {
        internal(
            span,
            "`Std.Ring.prove…` has fewer parameters than expected".into(),
        )
    };
    let mut ty = g.def(which).ty_value.clone();
    for arg in &args {
        let Value::Pi(_, _, _, cod) = force(g, ty)? else {
            return Err(shape());
        };
        ty = cod.apply(g, cx.eval(arg)?)?;
    }
    let Value::Pi(_, _, _, cod) = force(g, ty)? else {
        return Err(shape());
    };
    ty = cod.apply(g, Value::var(cx.level()))?;
    if !sides.is_empty() {
        let Value::Pi(_, _, dom, cod) = force(g, ty)? else {
            return Err(shape());
        };
        let mut meaning = force(g, (*dom).clone())?;
        for h in hyps {
            let Value::Data(d, params) = &meaning else {
                return Err(shape());
            };
            if *d != lib.and || params.len() != 2 {
                return Err(shape());
            }
            if !cx.unify(&params[0], &h.ty)? {
                return Err(internal(
                    span,
                    format!(
                        "the hypothesis `{}` is quoted as `{}`",
                        cx.show(&h.ty),
                        cx.show(&params[0])
                    ),
                ));
            }
            meaning = force(g, params[1].clone())?;
        }
        ty = cod.apply(g, Value::var(cx.level()))?;
    }
    if !cx.unify(&ty, expected)? {
        return Err(internal(
            span,
            format!(
                "the quoted goal means `{}`, not the goal `{}`",
                cx.show(&ty),
                cx.show(expected)
            ),
        ));
    }
    Ok(term)
}
