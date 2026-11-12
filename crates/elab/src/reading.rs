//! Readings (docs/proposals/bool-as-proposition.md §5, §6, §6.8): what
//! proposition a test (a `Bool` expression) decides, so a fact about it,
//! `e = True` or `e = False`, can be taken apart, built and used as that
//! proposition.
//!
//! A reading is an ordinary theorem `e = True ↔ P` or `e = False ↔ P`,
//! marked `@[reading]`, where `e` is a function applied to the theorem's
//! parameters, each once. It is filed under its polarity and the test's
//! head (the function; `&&` and `||`, which are two shapes of
//! `Bool.ifThenElse`, count as heads of their own), at most one per key,
//! and only in the module that declares the head: the library loads files
//! by the names a program mentions and a pattern mentions no reading, so a
//! reading anywhere else could be missing from a run that needs it, and the
//! check cache, which keys a unit on the units it uses, could miss a change
//! to it.
//!
//! The reader works one layer at a time: a constructor pattern, a
//! constructor or `.read` asks for the reading of the one test under it,
//! and the reading's parts are test facts again, read when something asks.
//! A test whose head has no reading is unfolded a step at a time (never
//! through `opaque`, which doesn't unfold), up to [`UNFOLD_LIMIT`] steps.
//!
//! A test is read by its function as written, so the reader evaluates with
//! calls kept folded ([`folded`]) and, with gluing off, where a fact's type
//! value has its calls unfolded already, starts from the type as written
//! ([`as_written`]): a variable's declared type, an annotation, a
//! parameter's type, the definition's own type. The same reading is found
//! either way.
//!
//! Nothing here is trusted: what the elaborator writes is
//! `Iff.forward (r args) h` or `Iff.backward (r args) p`, which the kernel
//! checks.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, Spine, apply, force, unfold_once};
use stitchwort_core::{DataId, DefId, Ev, Icit, Sort, Term, Value};
use stitchwort_syntax::ast::{self, BinOp, Decl, Expr};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Result};
use crate::{Elaborator, error};

/// How many times the reader unfolds a test whose head has no reading
/// before calling it a leaf.
const UNFOLD_LIMIT: usize = 8;

/// The head of a reading's test.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TestHead {
    Def(DefId),
    /// `a && b`: `Bool.ifThenElse a (_ => b) (_ => False)`.
    And,
    /// `a || b`: `Bool.ifThenElse a (_ => True) (_ => b)`.
    Or,
}

/// A `@[reading]` theorem, filed by the theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReadingInfo {
    /// `true` for `e = True ↔ P`, `false` for `e = False ↔ P`.
    pub polarity: bool,
    pub head: TestHead,
    /// For each of the theorem's parameters, in order, which of the test's
    /// arguments it is (for `&&` and `||`: 0 the left side, 1 the right).
    pub slots: Rc<[usize]>,
    /// The test's arguments, in order, that are a bare row `{e}` fixed to
    /// pure rather than a parameter: the empty row and its divergence,
    /// `Total`. A test fact's test is a `Bool`, so a function whose result
    /// is `{e} Bool` is only ever read there. A test with a row that isn't
    /// pure doesn't fit.
    pub pure_rows: Rc<[usize]>,
}

impl ReadingInfo {
    /// How many arguments the reading's test passes its function.
    fn arity(&self) -> usize {
        self.slots.len() + self.pure_rows.len()
    }

    /// Whether a test of this reading's head with `args` fits it.
    fn fits(&self, g: &Ev, args: &[Value]) -> Result<bool> {
        if args.len() != self.arity() {
            return Ok(false);
        }
        for &k in self.pure_rows.iter() {
            let arg = force(g, args[k].clone())?;
            if !matches!(arg, Value::Ctor(d, c, ref fields) if fields.is_empty() && is_pure_row(g, d, c))
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

/// A reading found for a test, in the caller's context: one reading, or
/// for a pattern or a constructor, the readings of what each reads as in
/// turn while that is a test fact again (§6.4).
pub(crate) struct Found {
    /// Each reading applied, outermost first.
    steps: Vec<Step>,
    /// What the last one reads as.
    pub prop: Value,
}

/// One reading applied to a test.
struct Step {
    via: Via,
    /// What it reads as.
    prop: Value,
}

/// What a step reads a test fact through.
enum Via {
    /// A `@[reading]` theorem.
    Reading {
        theorem: DefId,
        /// `r args`.
        proof: Term,
        /// The test fact, as the reading states it.
        fact: Value,
    },
    /// A decision `d: Decidable p` that doesn't compute, whose test fact
    /// `d.holds = True` reads as `p` and `d.holds = False` as `¬p` (§5.4,
    /// step 2).
    Decision {
        polarity: bool,
        /// `p`.
        prop: Term,
        /// `d`.
        decision: Term,
    },
}

/// What the reader found for a test.
pub(crate) enum Read {
    Found(Found),
    /// The test's function has a reading in this module that failed to
    /// check, with no stand-in to file.
    Pending(Pending),
    /// No reading, after unfolding what could be: the test's head when it
    /// is a function (for the note on `@[reading]`).
    Leaf(Option<DefId>),
}

/// `f` with calls kept folded (glued evaluation,
/// docs/proposals/folded-calls.md), whatever the session's switch says: a
/// test's reading is picked by its function as written, which a call
/// unfolded at once has lost (`inRange lo x hi` would be `lo <= x && x <=
/// hi`, read as `∧`). Values made here may hold calls; an unglued reader
/// unfolds them as it meets them.
fn folded<T>(g: &Ev, f: impl FnOnce() -> Result<T>) -> Result<T> {
    let was = g.machine.glue.replace(true);
    let out = f();
    g.machine.glue.set(was);
    out
}

/// The type of a fact to read, from its type `ty` and its type as written,
/// where known (a term with the values of its free variables): with gluing
/// on, `ty` keeps its calls folded already; with it off, the written type
/// evaluated with calls folded, where that is a test fact and the same type
/// as `ty` (a written type picked from the wrong place reads nothing).
pub(crate) fn as_written(
    cx: &Ctx,
    ty: &Value,
    written: Option<(Rc<Term>, Vec<Value>)>,
) -> Result<Value> {
    let g = cx.g();
    if g.machine.glue.get() {
        return Ok(ty.clone());
    }
    let Some((term, env)) = written else {
        return Ok(ty.clone());
    };
    // A variable among the written type's values may have been refined
    // since (a case branch's constructor), as `ty` is: read it from the
    // context.
    let env: Vec<Value> = env
        .into_iter()
        .map(|v| match &v {
            Value::Neutral(Head::Var(l, _), spine) if spine.is_empty() && *l < cx.level() => {
                cx.env[*l].clone()
            }
            _ => v,
        })
        .collect();
    let value = folded(&g, || Ok(stitchwort_core::value::eval(&g, &env, &term)?))?;
    if test_fact_in(&g, &value)?.is_none() {
        return Ok(ty.clone());
    }
    // Running out of resources here stops the declaration, as anywhere.
    let same = stitchwort_core::value::conv(&g, cx.level(), &value, ty)?;
    Ok(if same { value } else { ty.clone() })
}

/// [`as_written`] for the variable at `level`.
pub(crate) fn variable_as_written(cx: &Ctx, level: usize, ty: &Value) -> Result<Value> {
    as_written(cx, ty, crate::dot::written_at(cx, level))
}

/// [`as_written`] for a fact `term` of type `ty`: an annotation, a
/// variable's declared type or a function's declared result.
pub(crate) fn term_as_written(cx: &Ctx, term: &Term, ty: &Value) -> Result<Value> {
    if cx.g().machine.glue.get() {
        return Ok(ty.clone());
    }
    as_written(cx, ty, crate::dot::written_type_term(cx, term)?)
}

/// [`as_written`] for a type written here, `term`, whose value is `ty`.
pub(crate) fn here_as_written(cx: &Ctx, term: &Term, ty: &Value) -> Result<Value> {
    if cx.g().machine.glue.get() {
        return Ok(ty.clone());
    }
    as_written(cx, ty, Some((Rc::new(term.clone()), cx.env.clone())))
}

/// [`as_written`] for the type `dom` of the next explicit argument of
/// `head`: the parameter's type as `head`'s type writes it.
pub(crate) fn domain_as_written(cx: &Ctx, head: &Term, dom: &Value) -> Result<Value> {
    if cx.g().machine.glue.get() || !matches!(dom, Value::Eq(..)) {
        return Ok(dom.clone());
    }
    let written =
        crate::dot::written_type_term(cx, head)?.and_then(|(ty, env)| match ty.strip_loc() {
            Term::Pi(_, Icit::Explicit, d, _) => Some((d.clone(), env)),
            _ => None,
        });
    as_written(cx, dom, written)
}

/// [`as_written`] for an expected type: the definition's type as written,
/// where `expected` is that ([`Ctx::goal`]).
fn expected_as_written(cx: &Ctx, expected: &Value) -> Result<Value> {
    let g = cx.g();
    if g.machine.glue.get() {
        return Ok(expected.clone());
    }
    let Some((n, goal)) = &cx.goal else {
        return Ok(expected.clone());
    };
    if *n > cx.level() {
        return Ok(expected.clone());
    }
    as_written(cx, expected, Some((goal.clone(), cx.env[..*n].to_vec())))
}

/// The test and polarity of a test fact type `e = True` or `e = False`.
pub(crate) fn test_fact(cx: &Ctx, ty: &Value) -> Result<Option<(Value, bool)>> {
    test_fact_in(&cx.g(), ty)
}

fn test_fact_in(g: &Ev, ty: &Value) -> Result<Option<(Value, bool)>> {
    let Value::Eq(a, lhs, rhs) = force(g, ty.clone())? else {
        return Ok(None);
    };
    let reg = g.env.registry();
    let Some(bool_data) = reg.data(Builtin::Bool) else {
        return Ok(None);
    };
    if !matches!(force(g, (**a.rc()).clone())?, Value::Data(d, _) if d == bool_data) {
        return Ok(None);
    }
    let polarity = match force(g, (**rhs.rc()).clone())? {
        Value::Ctor(d, c, _) if d == bool_data => Some((d, c)) == reg.ctor(Builtin::True),
        _ => return Ok(None),
    };
    Ok(Some(((**lhs.rc()).clone(), polarity)))
}

/// A test's head and arguments, without unfolding it: a call kept folded,
/// or a definition stuck on its arguments. `&&` and `||` are recognised
/// in `Bool.ifThenElse`, with their two sides as the arguments.
fn head_args(g: &Ev, test: &Value) -> Result<Option<(TestHead, Vec<Value>)>> {
    let (f, spine) = match test {
        Value::Call(f, spine, _) | Value::Neutral(Head::Def(f), spine) => (*f, spine),
        _ => return Ok(None),
    };
    let mut args = Vec::new();
    for e in spine.iter() {
        match e {
            Elim::App(v, _) => args.push(v.clone()),
            _ => return Ok(None),
        }
    }
    let reg = g.env.registry();
    if Some(f) == reg.def(Builtin::IfThenElse)
        && let [_, cond, then, otherwise] = &args[..]
        && let Some(trivial) = reg.ctor(Builtin::Trivial)
    {
        let unit = Value::Ctor(trivial.0, trivial.1, Vec::new().into());
        let then = apply(g, then.clone(), unit.clone())?;
        let otherwise = apply(g, otherwise.clone(), unit)?;
        let is = |v: &Value, b: Builtin| -> Result<bool> {
            Ok(matches!(force(g, v.clone())?, Value::Ctor(d, c, _) if Some((d, c)) == reg.ctor(b)))
        };
        if is(&otherwise, Builtin::False)? {
            return Ok(Some((TestHead::And, vec![cond.clone(), then])));
        }
        if is(&then, Builtin::True)? {
            return Ok(Some((TestHead::Or, vec![cond.clone(), otherwise])));
        }
    }
    Ok(Some((TestHead::Def(f), args)))
}

/// [`head_args`] for a test as written, a term: each argument with the
/// number of binders it is under (a side of `&&` or `||` is under its
/// branch's lambda).
fn written_head_args(g: &Ev, test: &Term) -> Option<(TestHead, Vec<(Term, usize)>)> {
    let mut args = Vec::new();
    let mut f = test.strip_loc();
    while let Term::App(fun, arg, _) = f {
        args.push(arg.strip_loc().clone());
        f = fun.strip_loc();
    }
    args.reverse();
    let Term::Def(f) = f else { return None };
    let reg = g.env.registry();
    if Some(*f) == reg.def(Builtin::IfThenElse)
        && let [_, cond, Term::Lam(_, _, then), Term::Lam(_, _, otherwise)] = &args[..]
    {
        let is = |t: &Term, b: Builtin| matches!(t, Term::Ctor(d, c, fs) if fs.is_empty() && Some((*d, *c)) == reg.ctor(b));
        let (then, otherwise) = (then.strip_loc(), otherwise.strip_loc());
        if is(otherwise, Builtin::False) {
            return Some((TestHead::And, vec![(cond.clone(), 0), (then.clone(), 1)]));
        }
        if is(then, Builtin::True) {
            return Some((
                TestHead::Or,
                vec![(cond.clone(), 0), (otherwise.clone(), 1)],
            ));
        }
    }
    Some((
        TestHead::Def(*f),
        args.into_iter().map(|a| (a, 0)).collect(),
    ))
}

impl Elaborator {
    /// The reading filed under `polarity` and `head`, if any.
    fn reading_for(&self, polarity: bool, head: TestHead) -> Option<(DefId, Rc<ReadingInfo>)> {
        self.tables
            .readings
            .iter()
            .find(|(_, r)| r.polarity == polarity && r.head == head)
            .map(|(id, r)| (*id, Rc::clone(r)))
    }

    /// Files theorem `id`, written `@[reading]` at `at`, as a reading,
    /// after checking its statement (`E-READING-SHAPE`), that it is the
    /// only one for its key (`E-READING-OVERLAP`) and that it is declared
    /// with its test (`E-READING-PLACE`).
    pub(crate) fn register_reading(&mut self, id: DefId, at: Span) -> Result<()> {
        let info = self.reading_info(id, at)?;
        self.tables
            .readings
            .insert(&self.session.owners, id, Rc::new(info));
        Ok(())
    }

    /// [`Self::register_reading`]'s checks, and what is filed.
    fn reading_info(&self, id: DefId, at: Span) -> Result<ReadingInfo> {
        let g = &self.ev();
        let def = g.def(id);
        let name = def.name().to_string();
        let shape = |what: String| {
            error(
                "E-READING-SHAPE",
                at,
                format!("`{name}` can't be a reading: {what}"),
            )
            .with_note(
                "a reading is a theorem `test = True ↔ P` or `test = False ↔ P`, whose test is \
                 a function applied to the theorem's parameters, each once: `@[reading] theorem \
                 List.anyReads (xs: List a) (p: a → Bool): xs.any p ↔ ∃ (x: a) => x ∈ xs ∧ p x`",
            )
        };
        let mut params = 0;
        let mut ty = def.ty_value().clone();
        while let Value::Pi(_, _, _, cod) = force(g, ty.clone())? {
            ty = cod.apply(g, Value::var(params))?;
            params += 1;
        }
        // The test as the statement writes it: evaluated, a call may already
        // be unfolded (always, with gluing off), and its function lost.
        let mut names = Vec::new();
        let mut written = def.ty().strip_loc();
        while let Term::Pi(n, _, _, cod) = written {
            names.push(n.clone());
            written = cod.strip_loc();
        }
        let reg = g.env.registry();
        let Some(iff) = reg.data(Builtin::Iff) else {
            return Err(shape("`Iff` isn't loaded".to_string()));
        };
        let Value::Data(d, sides) = force(g, ty)? else {
            return Err(shape("its statement isn't an `↔`".to_string()));
        };
        if d != iff {
            return Err(shape("its statement isn't an `↔`".to_string()));
        }
        let Some((_, polarity)) = test_fact_in(g, &sides[0])? else {
            return Err(shape(
                "the left side of its `↔` isn't a test fact, `e = True` or `e = False` for a \
                 `Bool` `e`"
                    .to_string(),
            ));
        };
        let written_test = match written {
            Term::Data(d, sides) if *d == iff && sides.len() == 2 => match sides[0].strip_loc() {
                Term::Eq(_, test, _) => Some(test.strip_loc()),
                _ => None,
            },
            _ => None,
        };
        let Some((head, args)) = written_test.and_then(|t| written_head_args(g, t)) else {
            return Err(shape(
                "its test must be a function applied to the theorem's parameters, each exactly \
                 once"
                    .to_string(),
            ));
        };
        // Each argument a different parameter, and every parameter one,
        // except that a row argument may be the empty row: a pure `p` given
        // to a function over `{e}` (`xs.any p`) fixes its row there, and
        // every test fact with that head is at the empty row anyway (a row
        // `{e}` is passed as the row and its divergence, `Empty` and
        // `Total` when pure).
        let mut slots = vec![usize::MAX; params];
        let mut pure_rows = Vec::new();
        for (k, (arg, _)) in args.iter().enumerate() {
            if let Term::Ctor(d, c, fields) = arg
                && fields.is_empty()
                && is_pure_row(g, *d, *c)
            {
                pure_rows.push(k);
            }
        }
        let mut distinct = args.len() == params + pure_rows.len() && names.len() == params;
        for (k, (arg, under)) in args.iter().enumerate() {
            if pure_rows.contains(&k) {
                continue;
            }
            match arg {
                Term::Var(i) if *i >= *under && i - under < params => {
                    let l = params - 1 - (i - under);
                    if slots[l] == usize::MAX {
                        slots[l] = k;
                    } else {
                        distinct = false;
                    }
                }
                _ => distinct = false,
            }
        }
        if !distinct || slots.contains(&usize::MAX) {
            let shown = written_test.map_or_else(
                || "…".to_string(),
                |t| stitchwort_core::pretty::term_for_message_in(g, self, &names, t),
            );
            return Err(shape(format!(
                "its test `{shown}` must be a function applied to the theorem's parameters, \
                 each exactly once, so that any test with that head fits it"
            )));
        }
        let home = match head {
            TestHead::Def(f) => {
                if Some(f) == reg.def(Builtin::IfThenElse) {
                    return Err(shape(
                        "an `if` other than `&&` and `||` can't have a reading".to_string(),
                    ));
                }
                // A call of a function given fewer parameters than the test
                // passes it (`def tiny: Nat → Bool := small`) unfolds to
                // what it stands for before anything reads it, so a reading
                // filed under it could never be found.
                let def = g.def(f);
                if !def.opaque() && def.arity() < args.len() {
                    let f = def.name().to_string();
                    let takes = match def.arity() {
                        0 => "no parameters".to_string(),
                        1 => "1 parameter".to_string(),
                        k => format!("{k} parameters"),
                    };
                    let passes = match args.len() {
                        1 => "1 argument".to_string(),
                        k => format!("{k} arguments"),
                    };
                    return Err(shape(format!(
                        "its test passes `{f}` {passes}, but `{f}` takes {takes}, so a call of \
                         it is unfolded to what it stands for before it can be read"
                    ))
                    .with_note(format!(
                        "declare the reading on the function `{f}` stands for, or give `{f}` its \
                         parameters: `def {f} (x: …): Bool := …`"
                    )));
                }
                f
            }
            TestHead::And | TestHead::Or => reg
                .def(Builtin::IfThenElse)
                .expect("`&&` and `||` are made of it"),
        };
        let shown_head = match head {
            TestHead::Def(f) => format!("`{}`", g.def(f).name()),
            TestHead::And => "`&&`".to_string(),
            TestHead::Or => "`||`".to_string(),
        };
        // A derived test (`T.%same`) is made with its type, so it is there
        // whenever the type is, though it is no item of the module.
        if !self.unit.module.def_items.contains_key(&home) && !g.def(home).name().contains('%') {
            return Err(error(
                "E-READING-PLACE",
                at,
                format!("`{name}` must be declared with {shown_head}"),
            )
            .with_note(format!(
                "a reading is declared where its test's function is (the same namespace in a \
                 project, the same file in the library), so that it is there whenever the test \
                 is; {shown_head} is declared elsewhere"
            ))
            .with_note(
                "the theorem itself can still be used by name, without `@[reading]`".to_string(),
            ));
        }
        if let Some((other, _)) = self.reading_for(polarity, head) {
            let fact = if polarity { "True" } else { "False" };
            return Err(error(
                "E-READING-OVERLAP",
                at,
                format!(
                    "{shown_head} already has a reading for `= {fact}`: `{}`",
                    g.def(other).name()
                ),
            )
            .with_note(
                "each test reads as one proposition (and one more for `= False`), so a pattern, \
                 an error and a hover can always say which",
            ));
        }
        Ok(ReadingInfo {
            polarity,
            head,
            slots: slots.into(),
            pure_rows: pure_rows.into(),
        })
    }
}

/// Whether constructor `c` of `d` is what a pure bare row `{e}` is passed
/// as: the empty row, or the divergence `Total`.
fn is_pure_row(g: &Ev, d: DataId, c: usize) -> bool {
    let reg = g.env.registry();
    [Builtin::RowEmpty, Builtin::DivTotal]
        .into_iter()
        .any(|b| reg.ctor(b) == Some((d, c)))
}

/// What the reader finds for a test before any term is built: the
/// reading and the arguments its theorem is applied to.
enum Lookup {
    Found(DefId, Rc<ReadingInfo>, Vec<Value>),
    /// A decision that doesn't compute, `d: Decidable p`: `p` and `d`.
    Decision(Value, Value),
    Pending(Pending),
    Leaf(Option<DefId>),
}

/// A reading of this module's that failed, with no stand-in filed.
#[derive(Clone, Copy)]
pub(crate) struct Pending {
    /// The test's function.
    test: DefId,
    /// The reading's item in the module.
    item: usize,
}

/// How a `@[reading]` theorem's statement names its test's function.
#[derive(Clone, Debug)]
pub(crate) enum WrittenHead {
    /// `f x…`, `Ns.f x…`: the name as written.
    Name(String),
    /// `x.f y…`: the function's last name, and the head of `x`'s written
    /// type where `x` is a parameter of the statement with one. Which
    /// namespace the function is in depends on `x`'s type, so without it
    /// every function with that last name is a candidate.
    Method(String, Option<String>),
}

/// For a `@[reading]` theorem: how its statement names its test's function,
/// and the polarity (`f x… ↔ P` true, `f x… = False ↔ P` false), if the
/// statement has that shape, written with `↔` or as `Iff (…) (…)`. Read
/// from the syntax, so it is known before the theorem is checked.
pub(crate) fn written_reading(decl: &Decl) -> Option<(WrittenHead, bool)> {
    let Decl::Signature {
        ty,
        theorem: true,
        attrs,
        ..
    } = decl
    else {
        return None;
    };
    if !attrs
        .iter()
        .any(|a| a.name.text == crate::attributes::READING)
    {
        return None;
    }
    let mut ty = ty;
    let mut params: Vec<(&str, &Expr)> = Vec::new();
    let lhs = loop {
        match ty {
            Expr::Pi {
                names, dom, cod, ..
            } => {
                params.extend(names.iter().map(|n| (n.text.as_str(), &**dom)));
                ty = cod;
            }
            Expr::Bracketed(inner, _) => ty = inner,
            Expr::App(f, _) => match unbracket(f) {
                Expr::App(iff, lhs) if matches!(unbracket(iff), Expr::Var(n) if last_name(&n.text) == "Iff") =>
                {
                    break &**lhs;
                }
                _ => return None,
            },
            _ => return None,
        }
    };
    let (mut test, polarity) = match unbracket(lhs) {
        Expr::Binary(BinOp::Eq, test, b) => match unbracket(b) {
            Expr::Var(n) if n.text == "False" => (&**test, false),
            Expr::Var(n) if n.text == "True" => (&**test, true),
            _ => return None,
        },
        test => (test, true),
    };
    while let Expr::App(f, _) = unbracket(test) {
        test = f;
    }
    match unbracket(test) {
        Expr::Var(ast::Name { text, .. }) => Some((WrittenHead::Name(text.clone()), polarity)),
        Expr::Field(receiver, ast::Name { text, .. }) => {
            let receiver_type = match unbracket(receiver) {
                Expr::Var(x) => (params.iter().rev().find(|(n, _)| *n == x.text))
                    .and_then(|(_, ty)| crate::module::type_head(ty))
                    .map(|n| n.text.clone()),
                _ => None,
            };
            Some((WrittenHead::Method(text.clone(), receiver_type), polarity))
        }
        _ => None,
    }
}

/// Whether `head`, written in this module, names function `f`.
fn names(e: &Elaborator, head: &WrittenHead, f: DefId) -> bool {
    let name = e.kernel.def(f).name().to_string();
    match head {
        WrittenHead::Method(m, _) => last_name(&name) == m,
        WrittenHead::Name(text) => match e.named(text) {
            Some((crate::Global::Def(id), _)) => *id == f,
            _ => name == *text || name.ends_with(&format!(".{text}")),
        },
    }
}

fn unbracket(mut e: &Expr) -> &Expr {
    while let Expr::Bracketed(inner, _) = e {
        e = inner;
    }
    e
}

fn last_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// The item of this module's reading of `f` at `polarity` whose status
/// `keep` accepts.
fn module_reading(
    e: &Elaborator,
    f: DefId,
    polarity: bool,
    keep: impl Fn(crate::module::Status) -> bool,
) -> Option<usize> {
    let module = &e.unit.module;
    if !module.def_items.contains_key(&f) {
        return None;
    }
    module.items.iter().position(|info| {
        info.reading
            .as_ref()
            .is_some_and(|(head, p)| *p == polarity && keep(info.status) && names(e, head, f))
    })
}

/// A reading of `f` at `polarity` declared in this module that failed, so
/// isn't filed: what reads through it fails with it, quietly.
fn pending(e: &Elaborator, f: DefId, polarity: bool) -> Option<Pending> {
    module_reading(e, f, polarity, crate::module::Status::failed)
        .map(|item| Pending { test: f, item })
}

/// Why a fact of type `ty` isn't read by its test's own reading, where
/// that is because the reading isn't checked yet: checking order puts every
/// use of a test after its reading (D3537), except the reading's own
/// dependencies, which read the test as what it unfolds to.
pub(crate) fn waiting_note(g: &Ev, e: &Elaborator, ty: &Value) -> Result<Option<String>> {
    let Some((test, polarity)) = test_fact_in(g, ty)? else {
        return Ok(None);
    };
    waiting_note_for(g, e, &test, polarity)
}

fn waiting_note_for(
    g: &Ev,
    e: &Elaborator,
    test: &Value,
    polarity: bool,
) -> Result<Option<String>> {
    folded(g, || {
        let mut test = test.clone();
        for _ in 0..=UNFOLD_LIMIT {
            let Some((TestHead::Def(f), _)) = head_args(g, &test)? else {
                return Ok(None);
            };
            let waiting = |s| s == crate::module::Status::Waiting;
            // In the reading's own proof it goes without saying.
            if let Some(item) = module_reading(e, f, polarity, waiting)
                && e.unit.module.item != Some(item)
            {
                let f = g.def(f).name();
                let reading = &e.unit.module.items[item].name;
                return Ok(Some(format!(
                    "`{f}`'s reading, `{reading}`, isn't available here: `{reading}` depends on \
                     this declaration, so here `{f}` reads as what it unfolds to"
                )));
            }
            match &test {
                Value::Call(f, spine, _) if !g.def(*f).opaque() => {
                    test = unfold_once(g, *f, spine.clone())?;
                }
                _ => return Ok(None),
            }
        }
        Ok(None)
    })
}

/// The reading of `test` at `polarity` (§5.4): its head's reading, or else
/// the reading of what it unfolds to, one definition at a time, up to
/// [`UNFOLD_LIMIT`] steps.
fn lookup(g: &Ev, e: &Elaborator, test: &Value, polarity: bool) -> Result<Lookup> {
    folded(g, || lookup_folded(g, e, test, polarity))
}

fn lookup_folded(g: &Ev, e: &Elaborator, test: &Value, polarity: bool) -> Result<Lookup> {
    let mut test = test.clone();
    let mut first_head = None;
    for _ in 0..=UNFOLD_LIMIT {
        if let Some((prop, decision)) = stuck_decision(g, &test)? {
            return Ok(Lookup::Decision(prop, decision));
        }
        let Some((head, args)) = head_args(g, &test)? else {
            break;
        };
        // The function a reading could be declared for: not a decision's
        // field, nor a generated definition, which can't be named.
        if first_head.is_none()
            && let TestHead::Def(f) = head
            && Some(f) != g.env.registry().def(Builtin::Holds)
            && !g.def(f).name().contains('%')
        {
            first_head = Some(f);
        }
        // A test with more or fewer arguments than the reading's (a
        // function returning a function), or at a row the reading isn't
        // stated at, isn't the reading's test.
        if let Some((theorem, info)) = e.reading_for(polarity, head)
            && info.fits(g, &args)?
        {
            return Ok(Lookup::Found(theorem, info, args));
        }
        // Not what it unfolds to: that isn't the reading the program means.
        if let TestHead::Def(f) = head
            && let Some(p) = pending(e, f, polarity)
        {
            return Ok(Lookup::Pending(p));
        }
        // A folded call unfolds a step; a stuck one, or an `opaque` one,
        // is as far as the reader goes.
        match &test {
            Value::Call(f, spine, _) if !g.def(*f).opaque() => {
                test = unfold_once(g, *f, spine.clone())?;
            }
            _ => break,
        }
    }
    Ok(Lookup::Leaf(first_head))
}

/// The reading of `test` at `polarity`, with its terms built in `cx`.
pub(crate) fn read(cx: &Ctx, test: &Value, polarity: bool) -> Result<Read> {
    let lookup = lookup(&cx.g(), cx.e, test, polarity)?;
    Ok(match lookup {
        Lookup::Found(theorem, info, args) => Read::Found(found(cx, theorem, &info, &args)?),
        Lookup::Decision(prop, decision) => {
            Read::Found(by_decision(cx, &prop, &decision, polarity)?)
        }
        Lookup::Pending(p) => Read::Pending(p),
        Lookup::Leaf(head) => Read::Leaf(head),
    })
}

/// A decision's test whose decision doesn't compute: `d.holds`, as the
/// call `Decidable.holds d` or as the field of a call `(f x).holds`, for a
/// `d: Decidable p` that is a variable or a call stuck on one (§5.4, step
/// 2): `p` and `d`. A decision that computes to a record has its test as
/// its `holds`, read by that test's own reading; an unknown one is a leaf
/// (§5.6).
fn stuck_decision(g: &Ev, test: &Value) -> Result<Option<(Value, Value)>> {
    let reg = g.env.registry();
    let (Some(holds), Some(decidable)) = (reg.def(Builtin::Holds), reg.data(Builtin::Decidable))
    else {
        return Ok(None);
    };
    let (prop, decision) = match test {
        Value::Call(f, spine, _) | Value::Neutral(Head::Def(f), spine)
            if *f == holds && spine.len() == 2 =>
        {
            let [Elim::App(prop, _), Elim::App(decision, _)] = &spine[..] else {
                return Ok(None);
            };
            (prop.clone(), decision.clone())
        }
        Value::Call(f, spine, _) if matches!(spine.last(), Some(&Elim::Proj(d, 0)) if d == decidable) =>
        {
            let call: Spine = spine[..spine.len() - 1].iter().cloned().collect();
            let mut ty = g.def(*f).ty_value().clone();
            for e in call.iter() {
                let (Elim::App(arg, _), Value::Pi(_, _, _, cod)) = (e, force(g, ty)?) else {
                    return Ok(None);
                };
                ty = cod.apply(g, arg.clone())?;
            }
            let Value::Data(d, args) = force(g, ty)? else {
                return Ok(None);
            };
            if d != decidable || args.len() != 1 {
                return Ok(None);
            }
            (args[0].clone(), Value::Call(*f, call, Rc::default()))
        }
        _ => return Ok(None),
    };
    Ok(match force(g, decision.clone())? {
        Value::Neutral(Head::Meta(..), _) => None,
        Value::Neutral(..) => Some((prop, decision)),
        _ => None,
    })
}

/// What a decision's test fact reads as: `p`, or `¬p` when it is `False`.
fn decision_reads(g: &Ev, prop: &Value, polarity: bool) -> Result<Value> {
    if polarity {
        return Ok(prop.clone());
    }
    let not = g.env.registry().def(Builtin::Not).expect("in the core");
    Ok(stitchwort_core::value::eval(
        g,
        std::slice::from_ref(prop),
        &Term::app(Term::Def(not), Term::Var(0)),
    )?)
}

/// The reading of a test fact on decision `decision: Decidable prop`.
fn by_decision(cx: &Ctx, prop: &Value, decision: &Value, polarity: bool) -> Result<Found> {
    let reads = decision_reads(&cx.g(), prop, polarity)?;
    Ok(Found {
        steps: vec![Step {
            via: Via::Decision {
                polarity,
                prop: cx.quote_folded(prop)?,
                decision: cx.quote_folded(decision)?,
            },
            prop: reads.clone(),
        }],
        prop: reads,
    })
}

/// What a test fact of type `ty` reads as, if it is one and has a
/// reading, read through as [`read_through`] does: for compiling a pattern
/// on it, which needs to know the type it matches (a record pattern does).
pub(crate) fn read_type(g: &Ev, e: &Elaborator, ty: &Value) -> Result<Option<Value>> {
    let mut prop = None;
    let mut ty = ty.clone();
    for _ in 0..UNFOLD_LIMIT {
        let Some((test, polarity)) = test_fact_in(g, &ty)? else {
            break;
        };
        ty = match lookup(g, e, &test, polarity)? {
            Lookup::Found(theorem, info, args) => {
                let (_, sides) = statement(g, theorem, &info, &args, |_, _| Ok(()))?;
                sides[1].clone()
            }
            Lookup::Decision(p, _) => decision_reads(g, &p, polarity)?,
            _ => break,
        };
        prop = Some(ty.clone());
    }
    Ok(prop)
}

/// The statement of `theorem` applied to `args` as `info` says: `Iff`'s two
/// sides, with `each` called on each argument and how it is passed.
fn statement(
    g: &Ev,
    theorem: DefId,
    info: &ReadingInfo,
    args: &[Value],
    mut each: impl FnMut(&Value, Icit) -> Result<()>,
) -> Result<(DataId, Vec<Value>)> {
    // Folded, so that a test in what the test reads as is read by its own
    // function in turn.
    folded(g, || {
        let mut ty = g.def(theorem).ty_value().clone();
        for &slot in info.slots.iter() {
            let Value::Pi(_, icit, _, cod) = force(g, ty)? else {
                unreachable!("checked when the reading was declared")
            };
            let arg = &args[slot];
            each(arg, icit)?;
            ty = cod.apply(g, arg.clone())?;
        }
        let Value::Data(d, sides) = force(g, ty)? else {
            unreachable!("checked when the reading was declared")
        };
        Ok((d, sides.to_vec()))
    })
}

/// Theorem `theorem` applied to the test's `args` as `info` says.
fn found(cx: &Ctx, theorem: DefId, info: &ReadingInfo, args: &[Value]) -> Result<Found> {
    let mut proof = Term::Def(theorem);
    let (_, sides) = statement(&cx.g(), theorem, info, args, |arg, icit| {
        proof = Term::app_icit(proof.clone(), cx.quote_folded(arg)?, icit);
        Ok(())
    })?;
    Ok(Found {
        steps: vec![Step {
            via: Via::Reading {
                theorem,
                proof,
                fact: sides[0].clone(),
            },
            prop: sides[1].clone(),
        }],
        prop: sides[1].clone(),
    })
}

/// [`read`], then the reading of what that reads as while it is a test
/// fact, up to [`UNFOLD_LIMIT`] readings: for a pattern or a constructor,
/// which need a proposition's data type (§6.4: `Bool.not (a && b) = True`
/// reads as `(a && b) = False`, which reads as `a = False ∨ b = False`).
pub(crate) fn read_through(cx: &Ctx, test: &Value, polarity: bool) -> Result<Read> {
    let mut found = match read(cx, test, polarity)? {
        Read::Found(found) => found,
        leaf => return Ok(leaf),
    };
    for _ in 1..UNFOLD_LIMIT {
        let Some((inner, polarity)) = test_fact(cx, &found.prop)? else {
            break;
        };
        let Read::Found(next) = read(cx, &inner, polarity)? else {
            break;
        };
        found.steps.extend(next.steps);
        found.prop = next.prop;
    }
    Ok(Read::Found(found))
}

/// Definition `f` applied to `args`, each passed as `f`'s type says.
fn applied(cx: &Ctx, f: DefId, args: Vec<Term>) -> Term {
    let mut term = Term::Def(f);
    let mut ty = cx.g().def(f).ty().clone();
    let mut args = args.into_iter();
    while let Term::Pi(_, icit, _, cod) = ty.strip_loc() {
        let Some(arg) = args.next() else { break };
        term = Term::app_icit(term, arg, *icit);
        ty = (**cod).clone();
    }
    term
}

/// One step's proof the way it reads (`forward`) or back, applied to
/// `arg`: for a reading `Iff.forward (r args) arg` or `Iff.backward (r
/// args) arg`; for a decision `d: Decidable p`, `Decidable.sound d arg` and
/// `Decidable.complete d arg` at `True`, `Decidable.refute d arg` and
/// `Decidable.toBoolOfNot d arg` at `False`.
fn step_proof(cx: &Ctx, step: &Step, forward: bool, arg: Term) -> Result<Term> {
    let g = cx.g();
    let reg = g.env.registry();
    Ok(match &step.via {
        Via::Reading { proof, fact, .. } => {
            let iff = reg.data(Builtin::Iff).expect("a reading is an `↔`");
            let field = if forward { 0 } else { 1 };
            let projection =
                cx.e.tables.records[&iff].projections[field].expect("`Iff`'s fields are proofs");
            let args = vec![
                cx.quote_folded(fact)?,
                cx.quote_folded(&step.prop)?,
                proof.clone(),
                arg,
            ];
            applied(cx, projection, args)
        }
        Via::Decision {
            polarity,
            prop,
            decision,
        } => {
            let f = match (polarity, forward) {
                (true, true) => crate::check::decidable_field(cx, 1)?,
                (true, false) => crate::check::decidable_field(cx, 2)?,
                (false, true) => crate::check::builtin_def(cx, Builtin::Refute)?,
                (false, false) => crate::check::builtin_def(cx, Builtin::ToBoolOfNot)?,
            };
            applied(cx, f, vec![prop.clone(), decision.clone(), arg])
        }
    })
}

impl Found {
    /// The fact `h` (a term) as the proposition: `Iff.forward (r args) h`.
    pub(crate) fn forward(&self, cx: &Ctx, h: Term) -> Result<Term> {
        self.steps
            .iter()
            .try_fold(h, |h, step| step_proof(cx, step, true, h))
    }

    /// The test fact from a proof `p` of the proposition.
    pub(crate) fn backward(&self, cx: &Ctx, p: Term) -> Result<Term> {
        self.steps
            .iter()
            .rev()
            .try_fold(p, |p, step| step_proof(cx, step, false, p))
    }

    /// What gave the proposition, for messages: the reading's name, or
    /// for a decision, what it is.
    fn last(&self, cx: &Ctx) -> String {
        match &self.steps.last().expect("at least one reading").via {
            Via::Reading { theorem, .. } => format!("`{}`", cx.g().def(*theorem).name()),
            Via::Decision { .. } => "by its decision".to_string(),
        }
    }
}

/// `E-NO-READING`, for `what` (the fact, as written or shown) used as `how`
/// (`taken apart with \`Both\``, `read with \`.read\``): the test has no
/// reading at its polarity, or reads as `prop`, which isn't a `wanted`.
pub(crate) fn no_reading(
    cx: &Ctx,
    span: Span,
    test: &Value,
    polarity: bool,
    how: &str,
    read: &Read,
    wanted: Option<(DataId, &str)>,
) -> Diagnostic {
    let g = cx.g();
    let fact = if polarity {
        format!("`{}`", cx.show(test))
    } else {
        format!("`{} = False`", cx.show(test))
    };
    let waiting = waiting_note_for(&g, cx.e, test, polarity).ok().flatten();
    let d = match read {
        Read::Pending(p) => return pending_error(cx.e, span, *p),
        Read::Found(found) => {
            let mut d = Diagnostic::error("E-NO-READING", format!("this test fact can't be {how}"))
                .with_label(
                    span,
                    format!(
                        "{fact} reads as `{}` ({})",
                        cx.show(&found.prop),
                        found.last(cx)
                    ),
                );
            if let Some((w, what)) = wanted {
                let name = g.data(w).name();
                let a = if name.starts_with(['A', 'E', 'I', 'O', 'U']) {
                    "an"
                } else {
                    "a"
                };
                d = d.with_note(format!(
                    "{what} {a} `{name}`, and `{}` isn't one",
                    cx.show(&found.prop)
                ));
            }
            d.with_note(
                "a test fact can always be matched by a name, and `.read` gives the proposition",
            )
        }
        Read::Leaf(head) => {
            // The head has a reading, which didn't fit: it fixes a row this
            // test doesn't pass as pure.
            let pure_only = head
                .and_then(|f| cx.e.reading_for(polarity, TestHead::Def(f)))
                .filter(|(_, info)| !info.pure_rows.is_empty());
            let label = if pure_only.is_some() {
                format!("{fact} doesn't fit its function's reading, so it has no parts")
            } else {
                format!("{fact} has no reading, so it has no parts")
            };
            let mut d = Diagnostic::error("E-NO-READING", format!("this test fact can't be {how}"))
                .with_label(span, label);
            if let (Some(f), Some((reading, _))) = (head, pure_only) {
                d = d.with_note(format!(
                    "`{}`'s reading, `{}`, is stated for pure functions, and this test passes \
                     one that may perform abilities",
                    g.def(*f).name(),
                    g.def(reading).name()
                ));
            } else if let Some(f) = head {
                d = d.with_note(format!(
                    "a reading says what a test means: a theorem `{} … = {} ↔ P` marked \
                     `@[reading]`, declared with `{}`",
                    g.def(*f).name(),
                    if polarity { "True" } else { "False" },
                    g.def(*f).name()
                ));
            }
            d.with_note("a test fact can always be matched by a name")
        }
    };
    match waiting {
        Some(note) => d.with_note(note),
        None => d,
    }
}

/// The error for a test fact used where its test's reading `p` failed:
/// `E-FAILED-DEPENDENCY`, which goes without saying beside the reading's
/// own error.
pub(crate) fn pending_error(e: &Elaborator, span: Span, p: Pending) -> Diagnostic {
    let test = e.kernel.def(p.test).name().to_string();
    let reading = &e.unit.module.items[p.item].name;
    Diagnostic::error("E-FAILED-DEPENDENCY", format!("`{reading}` has errors"))
        .with_label(span, format!("`{test}`'s reading, `{reading}`, has errors"))
        .with_note(format!(
            "this can't be accepted until the errors in `{reading}` are fixed"
        ))
}

/// The reading of this module's that a test fact of type `ty` waits for,
/// if its test's function has one not yet filed.
pub(crate) fn pending_of_type(g: &Ev, e: &Elaborator, ty: &Value) -> Result<Option<Pending>> {
    let Some((test, polarity)) = test_fact_in(g, ty)? else {
        return Ok(None);
    };
    Ok(match lookup(g, e, &test, polarity)? {
        Lookup::Pending(p) => Some(p),
        _ => None,
    })
}

/// Whether `d` is a proposition whose constructors a test fact can be read
/// into.
pub(crate) fn readable_data(cx: &Ctx, d: DataId) -> bool {
    cx.g().data(d).sort() == Sort::Prop
}

/// For a constructor `ctor` of data type `d` checked against a test fact
/// `expected` (§6.6): the reading it is checked against, or `None` where
/// `expected` isn't a test fact or `d` isn't a proposition.
pub(crate) fn for_ctor(cx: &Ctx, d: DataId, expected: &Value, span: Span) -> Result<Option<Found>> {
    if !readable_data(cx, d) {
        return Ok(None);
    }
    let Some((test, polarity)) = test_fact(cx, &expected_as_written(cx, expected)?)? else {
        return Ok(None);
    };
    let read = read_through(cx, &test, polarity)?;
    match read {
        Read::Found(found) if matches!(force(&cx.g(), found.prop.clone())?, Value::Data(d2, _) if d2 == d) => {
            Ok(Some(found))
        }
        read => Err(no_reading(
            cx,
            span,
            &test,
            polarity,
            &format!("built with {}", constructors_shown(cx, d)),
            &read,
            Some((d, "this builds")),
        )),
    }
}

/// For a record literal checked against a test fact `expected` (§6.6):
/// the reading it is checked against, or `None` where `expected` isn't a
/// test fact.
pub(crate) fn for_record(cx: &Ctx, expected: &Value, span: Span) -> Result<Option<Found>> {
    let Some((test, polarity)) = test_fact(cx, &expected_as_written(cx, expected)?)? else {
        return Ok(None);
    };
    let read = read_through(cx, &test, polarity)?;
    match read {
        Read::Found(found)
            if matches!(force(&cx.g(), found.prop.clone())?,
                Value::Data(d, _) if readable_data(cx, d) && cx.g().data(d).record()) =>
        {
            Ok(Some(found))
        }
        read => Err(no_reading(
            cx,
            span,
            &test,
            polarity,
            "built with a record",
            &read,
            None,
        )),
    }
}

pub(crate) fn constructors_shown(cx: &Ctx, d: DataId) -> String {
    let g = cx.g();
    let data = g.data(d);
    match data.ctors() {
        [c] => format!("`{}`", c.name),
        _ => format!("a constructor of `{}`", data.name()),
    }
}

/// `h.read` (§6.8), for `h` (the term `rterm`) of type `rty`: the
/// proposition its test reads as and the proof, or `None` where `rty` isn't
/// a test fact. A fact `e = False` whose test has no negative reading reads
/// as `¬e`.
pub(crate) fn dot_read(
    cx: &Ctx,
    rterm: &Term,
    rty: &Value,
    span: Span,
) -> Result<Option<(Term, Value)>> {
    let Some((test, polarity)) = test_fact(cx, &term_as_written(cx, rterm, rty)?)? else {
        return Ok(None);
    };
    match read(cx, &test, polarity)? {
        Read::Found(found) => {
            let term = found.forward(cx, rterm.clone())?;
            Ok(Some((term, found.prop)))
        }
        Read::Leaf(_) if !polarity => Ok(Some(refutes(cx, rterm, &test)?)),
        read => Err(no_reading(
            cx,
            span,
            &test,
            polarity,
            "read with `.read`",
            &read,
            None,
        )),
    }
}

/// `h` (the term `rterm`, of type `rty`) as the proposition its test
/// reads as, where it is a test fact whose test has a reading: for a field
/// of a fact (`h.left` is `h.read.left`, §6.6).
pub(crate) fn read_fact(cx: &Ctx, rterm: &Term, rty: &Value) -> Result<Option<(Term, Value)>> {
    let Some((test, polarity)) = test_fact(cx, &term_as_written(cx, rterm, rty)?)? else {
        return Ok(None);
    };
    match read(cx, &test, polarity)? {
        Read::Found(found) => Ok(Some((found.forward(cx, rterm.clone())?, found.prop))),
        Read::Pending(p) => Err(pending_error(cx.e, cx.span, p)),
        Read::Leaf(_) => Ok(None),
    }
}

/// From `h: e = False`, `¬(e = True)`: `t => Bool.falseNotTrue (Eq.trans
/// (Eq.sym h) t)`.
fn refutes(cx: &Ctx, h: &Term, test: &Value) -> Result<(Term, Value)> {
    let g = cx.g();
    let reg = g.env.registry();
    let def = |b: Builtin| reg.def(b).map(Term::Def).expect("in the core");
    let (bool_data, _) = reg.ctor(Builtin::True).expect("in the core");
    let ctor = |b: Builtin| {
        let (d, c) = reg.ctor(b).expect("in the core");
        Term::Ctor(d, c, Vec::new())
    };
    let bool_ty = Term::Data(bool_data, Vec::new());
    let e = cx.quote_folded(test)?;
    // Under the lambda's binder.
    let up = |t: &Term| t.shift(&g, 1, 0);
    let (bool_up, e_up, h_up) = (bool_ty.clone(), up(&e)?, up(h)?);
    let imp = Icit::Implicit;
    let sym = [bool_up.clone(), e_up.clone(), ctor(Builtin::False)]
        .into_iter()
        .fold(def(Builtin::EqSym), |t, a| Term::app_icit(t, a, imp));
    let sym = Term::app(sym, h_up);
    let trans = [bool_up, ctor(Builtin::False), e_up, ctor(Builtin::True)]
        .into_iter()
        .fold(def(Builtin::EqTrans), |t, a| Term::app_icit(t, a, imp));
    let trans = Term::app(Term::app(trans, sym), Term::Var(0));
    let body = Term::app(def(Builtin::FalseNotTrue), trans);
    let term = Term::Lam("isTrue".into(), Icit::Explicit, Rc::new(body));
    let eq_true = Term::Eq(
        Some(Rc::new(bool_ty)),
        Rc::new(e),
        Rc::new(ctor(Builtin::True)),
    );
    let not = Term::app(def(Builtin::Not), eq_true);
    Ok((term, cx.eval(&not)?))
}

/// What a proposition is about, for pairing a reading with the decisions of
/// what it reads as: the function or data type at its head.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PropHead {
    Def(DefId),
    Data(DataId),
}

fn prop_head(prop: &Value) -> Option<PropHead> {
    match prop {
        Value::Call(f, ..) | Value::Neutral(Head::Def(f), _) => Some(PropHead::Def(*f)),
        Value::Data(d, _) => Some(PropHead::Data(*d)),
        _ => None,
    }
}

/// A definition's parameters as variables, and its type under them,
/// evaluated with calls folded.
struct Opened {
    env: Vec<Value>,
    types: Vec<Value>,
    names: Vec<stitchwort_core::Name>,
    ty: Value,
}

fn opened(g: &Ev, id: DefId) -> Result<Opened> {
    folded(g, || {
        let mut opened = Opened {
            env: Vec::new(),
            types: Vec::new(),
            names: Vec::new(),
            ty: g.def(id).ty_value().clone(),
        };
        while let Value::Pi(x, _, dom, cod) = force(g, opened.ty.clone())? {
            let var = Value::var(opened.env.len());
            opened.env.push(var.clone());
            opened.types.push((*dom).clone());
            opened.names.push(x);
            opened.ty = cod.apply(g, var)?;
        }
        Ok(opened)
    })
}

/// What a positive reading's statement says, under its parameters: its
/// test and what that reads as.
fn reading_sides(g: &Ev, reading: DefId) -> Result<Option<(Opened, Value, Value)>> {
    let opened = opened(g, reading)?;
    let Value::Data(_, sides) = force(g, opened.ty.clone())? else {
        return Ok(None);
    };
    let Some((test, true)) = test_fact_in(g, &sides[0])? else {
        return Ok(None);
    };
    let prop = sides[1].clone();
    Ok(own_proposition(g, &prop)?.then_some((opened, test, prop)))
}

/// Whether `prop` is its head applied to the reading's parameters, each at
/// most once, as a reading's test is to its function's (§5.3): the
/// proposition the test decides on its own (`List.Mem x xs`, `Small n`),
/// whose decision should test with it, rather than a connective or
/// relation decided generically (`lo ≤ x ∧ x ≤ hi`, `n ≤ 10`).
fn own_proposition(g: &Ev, prop: &Value) -> Result<bool> {
    let args: Vec<Value> = match prop {
        Value::Data(_, args) => args.to_vec(),
        Value::Call(_, spine, _) | Value::Neutral(Head::Def(_), spine) => {
            let mut args = Vec::new();
            for e in spine.iter() {
                let Elim::App(v, _) = e else {
                    return Ok(false);
                };
                args.push(v.clone());
            }
            args
        }
        _ => return Ok(false),
    };
    let mut seen = Vec::new();
    for arg in args {
        match force(g, arg)? {
            Value::Neutral(Head::Var(l, _), s) if s.is_empty() && !seen.contains(&l) => {
                seen.push(l)
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// What instance `id` decides, if it is a decision made by its own test:
/// `p` for `Decidable p`. `None` for one that takes a decision (as
/// `Decidable.and` does): its test is built from the decisions it is
/// given, which it doesn't choose.
fn decided(g: &Ev, id: DefId) -> Result<Option<Value>> {
    let Some(decidable) = g.env.registry().data(Builtin::Decidable) else {
        return Ok(None);
    };
    let opened = opened(g, id)?;
    for ty in &opened.types {
        if matches!(force(g, ty.clone())?, Value::Data(d, _) if d == decidable) {
            return Ok(None);
        }
    }
    Ok(match force(g, opened.ty)? {
        Value::Data(d, args) if d == decidable && args.len() == 1 => Some(args[0].clone()),
        _ => None,
    })
}

/// Whether `id` is generated (a derived instance, `T.%instDecidable`):
/// its author can't write it another way, so it isn't warned about.
fn generated(g: &Ev, id: DefId) -> bool {
    g.def(id).name().contains('%')
}

/// A decision's test and the test its proposition's reading reads, where
/// they differ (§13).
struct Mismatch {
    /// What the reading reads as.
    prop: String,
    /// The decision's test.
    holds: String,
    /// The reading's test.
    test: String,
}

impl Elaborator {
    /// Whether `instance`, made a decision of what positive reading
    /// `reading` reads as (`P`, under the reading's parameters), tests
    /// something other than the reading's test: its `holds`, through the
    /// decisions it is made from, isn't a call of the reading's test's
    /// function. `None` too where `instance` isn't a decision of `P`.
    fn decision_mismatch(&self, reading: DefId, instance: DefId) -> Result<Option<Mismatch>> {
        let g = &self.ev();
        let Some((opened, test, prop)) = reading_sides(g, reading)? else {
            return Ok(None);
        };
        let level = opened.env.len();
        self.clear_metas();
        let mut cx = Ctx::from_parts(self, opened.env, opened.types, opened.names, Span::NOWHERE);
        let found = crate::auto::instance_for(&mut cx, instance, &prop)
            .and_then(|found| found.map(|t| self.zonk(&t, level)).transpose());
        let result = (|| {
            let Some(decision) = found? else {
                return Ok(None);
            };
            let reg = g.env.registry();
            let (Some(holds), Some(decidable)) =
                (reg.def(Builtin::Holds), reg.data(Builtin::Decidable))
            else {
                return Ok(None);
            };
            let term = applied(&cx, holds, vec![cx.quote_folded(&prop)?, decision]);
            let mut value = folded(g, || cx.eval(&term))?;
            // Through the decisions it is made from to the test itself.
            for _ in 0..UNFOLD_LIMIT {
                match &value {
                    Value::Call(f, spine, _)
                        if *f == holds
                            || matches!(spine.last(), Some(&Elim::Proj(d, 0)) if d == decidable) =>
                    {
                        value = folded(g, || Ok(unfold_once(g, *f, spine.clone())?))?;
                    }
                    _ => break,
                }
            }
            // The function, not its arguments: those come from the
            // decisions it is made from (`if a ∧ b` decides `a = True` by
            // `Bool`'s `DecEq`), which the instance doesn't choose.
            let same = folded(g, || -> Result<bool> {
                Ok(matches!(
                    (head_args(g, &value)?, head_args(g, &test)?),
                    (Some((h1, _)), Some((h2, _))) if h1 == h2
                ))
            })?;
            Ok((!same).then(|| Mismatch {
                prop: cx.show(&prop),
                holds: cx.show(&value),
                test: cx.show(&test),
            }))
        })();
        self.clear_metas();
        result
    }

    fn decision_warning(
        &self,
        at: Span,
        reading: DefId,
        instance: DefId,
        m: Mismatch,
    ) -> Diagnostic {
        let g = self.ev();
        let (reading, instance) = (g.def(reading).name(), g.def(instance).name());
        let Mismatch { prop, holds, test } = m;
        Diagnostic::warning(
            "W-DECISION-TEST",
            format!("`{instance}` decides `{prop}` by a test other than the one that reads as it"),
        )
        .with_label(
            at,
            format!("`if {prop}` tests `{holds}`, but `{reading}` reads `{test}` as `{prop}`"),
        )
        .with_note(format!(
            "write the decision with that test, `holds = {test}`, its proofs from `{reading}`: \
             then `if {prop}` and `if {test}` are one test, and `rewrite` and `match h:` treat \
             them alike"
        ))
    }

    /// After reading `reading`, written `@[reading]` at `at`, is filed: a
    /// warning for each decision instance already checked whose test isn't
    /// the reading's, for what it reads as (§13). Every one, wherever it is
    /// written: checking order isn't source order, and an instance checked
    /// after the reading is warned about when it is.
    pub(crate) fn check_reading_decisions(&mut self, reading: DefId, at: Span) {
        let found = (|| -> Result<Vec<(DefId, Mismatch)>> {
            let g = &self.ev();
            let Some((_, _, prop)) = reading_sides(g, reading)? else {
                return Ok(Vec::new());
            };
            let Some(head) = prop_head(&prop) else {
                return Ok(Vec::new());
            };
            let instances: Vec<DefId> = (0..g.env.defs().len())
                .map(DefId)
                .filter(|&id| {
                    g.def(id).instance()
                        && g.def(id).body().is_some()
                        && !generated(g, id)
                        && crate::auto::visible(self, id)
                })
                .collect();
            let mut out = Vec::new();
            for instance in instances {
                if decided(g, instance)?.as_ref().and_then(prop_head) == Some(head)
                    && let Some(m) = self.decision_mismatch(reading, instance)?
                {
                    out.push((instance, m));
                }
            }
            Ok(out)
        })();
        for (instance, m) in found.unwrap_or_default() {
            let warning = self.decision_warning(at, reading, instance, m);
            self.unit.warnings.push(warning);
        }
    }

    /// After decision instance `instance`, declared at `at`, is admitted: a
    /// warning for each positive reading filed for what it decides whose
    /// test isn't the decision's (§13).
    pub(crate) fn check_instance_readings(&mut self, instance: DefId, at: Span) {
        let found = (|| -> Result<Vec<(DefId, Mismatch)>> {
            let g = &self.ev();
            if generated(g, instance) {
                return Ok(Vec::new());
            }
            let Some(head) = decided(g, instance)?.as_ref().and_then(prop_head) else {
                return Ok(Vec::new());
            };
            let readings: Vec<DefId> = (self.tables.readings.iter())
                .filter(|(id, r)| r.polarity && crate::auto::visible(self, **id))
                .map(|(id, _)| *id)
                .collect();
            let mut out = Vec::new();
            for reading in readings {
                let Some((_, _, prop)) = reading_sides(g, reading)? else {
                    continue;
                };
                if prop_head(&prop) == Some(head)
                    && let Some(m) = self.decision_mismatch(reading, instance)?
                {
                    out.push((reading, m));
                }
            }
            Ok(out)
        })();
        for (reading, m) in found.unwrap_or_default() {
            let warning = self.decision_warning(at, reading, instance, m);
            self.unit.warnings.push(warning);
        }
    }
}

/// For a type mismatch where `found` is a test fact and `expected` is what
/// it reads as (§6.7): the note saying so, and that `.read` gives it.
pub(crate) fn read_note(cx: &Ctx, expected: &Value, found: &Value) -> Result<Option<String>> {
    let g = &cx.g();
    let Some((test, polarity)) = test_fact(cx, found)? else {
        return Ok(None);
    };
    let prop = match lookup(g, cx.e, &test, polarity)? {
        Lookup::Found(theorem, info, args) => {
            statement(g, theorem, &info, &args, |_, _| Ok(()))?.1[1].clone()
        }
        Lookup::Decision(p, _) => decision_reads(g, &p, polarity)?,
        Lookup::Leaf(_) if !polarity => {
            let h = Term::Var(0);
            refutes(cx, &h, &test)?.1
        }
        _ => return Ok(None),
    };
    if !stitchwort_core::value::conv(g, cx.level(), &prop, expected)? {
        return Ok(None);
    }
    Ok(Some(format!(
        "this is the test fact `{}`, which reads as `{}`: add `.read` to use it as that",
        cx.show(found),
        cx.show(&prop)
    )))
}
