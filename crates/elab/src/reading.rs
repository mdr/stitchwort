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
use stitchwort_core::value::{Elim, Head, apply, force, unfold_once};
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
    theorem: DefId,
    /// `r args`.
    proof: Term,
    /// The test fact, as the reading states it.
    fact: Value,
    /// What it reads as.
    prop: Value,
}

/// What the reader found for a test.
pub(crate) enum Read {
    Found(Found),
    /// The test's function has a reading in this module that isn't filed:
    /// declared below the use (`failed` false), or failed to check.
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
                 List.anyReads (xs: List a) (f: a → Bool): xs.any f ↔ ∃ (x: a) => x ∈ xs ∧ f x`",
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
        // Each argument a different parameter, and every parameter one.
        let mut slots = vec![usize::MAX; params];
        let mut distinct = args.len() == params && names.len() == params;
        for (k, (arg, under)) in args.iter().enumerate() {
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
        if !self.unit.module.def_items.contains_key(&home) {
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
        })
    }
}

/// What the reader finds for a test before any term is built: the
/// reading and the arguments its theorem is applied to.
enum Lookup {
    Found(DefId, Rc<ReadingInfo>, Vec<Value>),
    Pending(Pending),
    Leaf(Option<DefId>),
}

/// A reading of this module's not yet filed when a test needs it.
#[derive(Clone, Copy)]
pub(crate) struct Pending {
    /// The test's function.
    test: DefId,
    /// The reading's item in the module.
    item: usize,
    failed: bool,
}

/// How a `@[reading]` theorem's statement names its test's function.
#[derive(Clone, Debug)]
pub(crate) enum WrittenHead {
    /// `f x…`, `Ns.f x…`: the name as written.
    Name(String),
    /// `x.f y…`: the function's last name; which namespace it is in
    /// depends on `x`'s type.
    Method(String),
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
    let lhs = loop {
        match ty {
            Expr::Pi { cod, .. } => ty = cod,
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
        Expr::Field(_, ast::Name { text, .. }) => {
            Some((WrittenHead::Method(text.clone()), polarity))
        }
        _ => None,
    }
}

/// Whether `head`, written in this module, names function `f`.
fn names(e: &Elaborator, head: &WrittenHead, f: DefId) -> bool {
    let name = e.kernel.def(f).name().to_string();
    match head {
        WrittenHead::Method(m) => last_name(&name) == m,
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

/// A reading of `f` at `polarity` declared in this module but not filed:
/// below the declaration being checked, or failed.
fn pending(e: &Elaborator, f: DefId, polarity: bool) -> Option<Pending> {
    let module = &e.unit.module;
    if !module.def_items.contains_key(&f) {
        return None;
    }
    let current = module.item.map(|i| module.items[i].position);
    module.items.iter().enumerate().find_map(|(item, info)| {
        let (head, p) = info.reading.as_ref()?;
        if *p != polarity || !names(e, head, f) {
            return None;
        }
        let failed = info.status.failed();
        let below = info.status == crate::module::Status::Waiting
            && current.is_some_and(|c| info.position > c);
        (failed || below).then_some(Pending {
            test: f,
            item,
            failed,
        })
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
        let Some((head, args)) = head_args(g, &test)? else {
            break;
        };
        if first_head.is_none()
            && let TestHead::Def(f) = head
        {
            first_head = Some(f);
        }
        // A test with more or fewer arguments than the reading's (a
        // function returning a function) isn't the reading's test.
        if let Some((theorem, info)) = e.reading_for(polarity, head)
            && info.slots.len() == args.len()
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
        Lookup::Pending(p) => Read::Pending(p),
        Lookup::Leaf(head) => Read::Leaf(head),
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
        let Lookup::Found(theorem, info, args) = lookup(g, e, &test, polarity)? else {
            break;
        };
        let (_, sides) = statement(g, theorem, &info, &args, |_, _| Ok(()))?;
        ty = sides[1].clone();
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
            theorem,
            proof,
            fact: sides[0].clone(),
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

/// `Iff.forward` (`field` 0) or `Iff.backward` (1) of `found`, applied to
/// `arg`.
fn iff_field(cx: &Ctx, found: &Step, field: usize, arg: Term) -> Result<Term> {
    let g = cx.g();
    let iff = g
        .env
        .registry()
        .data(Builtin::Iff)
        .expect("a reading is an `↔`");
    let projection =
        cx.e.tables.records[&iff].projections[field].expect("`Iff`'s fields are proofs");
    let mut term = Term::Def(projection);
    let mut ty = g.def(projection).ty().clone();
    let mut args = vec![
        cx.quote_folded(&found.fact)?,
        cx.quote_folded(&found.prop)?,
        found.proof.clone(),
        arg,
    ]
    .into_iter();
    while let Term::Pi(_, icit, _, cod) = ty.strip_loc() {
        let Some(arg) = args.next() else { break };
        term = Term::app_icit(term, arg, *icit);
        ty = (**cod).clone();
    }
    Ok(term)
}

impl Found {
    /// The fact `h` (a term) as the proposition: `Iff.forward (r args) h`.
    pub(crate) fn forward(&self, cx: &Ctx, h: Term) -> Result<Term> {
        self.steps
            .iter()
            .try_fold(h, |h, step| iff_field(cx, step, 0, h))
    }

    /// The test fact from a proof `p` of the proposition.
    pub(crate) fn backward(&self, cx: &Ctx, p: Term) -> Result<Term> {
        self.steps
            .iter()
            .rev()
            .try_fold(p, |p, step| iff_field(cx, step, 1, p))
    }

    /// The reading that gave the proposition.
    fn last(&self) -> DefId {
        self.steps.last().expect("at least one reading").theorem
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
    match read {
        Read::Pending(p) => pending_error(cx.e, span, *p, how),
        Read::Found(found) => {
            let mut d = Diagnostic::error("E-NO-READING", format!("this test fact can't be {how}"))
                .with_label(
                    span,
                    format!(
                        "{fact} reads as `{}` (`{}`)",
                        cx.show(&found.prop),
                        g.def(found.last()).name()
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
            let mut d = Diagnostic::error("E-NO-READING", format!("this test fact can't be {how}"))
                .with_label(span, format!("{fact} has no reading, so it has no parts"));
            if let Some(f) = head {
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
    }
}

/// The error for a test fact used as `how` where its test's reading is
/// `p`, not filed: `E-NO-READING` saying it is declared below, or, where it
/// failed, `E-FAILED-DEPENDENCY`, which goes without saying beside the
/// reading's own error.
pub(crate) fn pending_error(e: &Elaborator, span: Span, p: Pending, how: &str) -> Diagnostic {
    let info = &e.unit.module.items[p.item];
    let test = e.kernel.def(p.test).name().to_string();
    let reading = &info.name;
    if p.failed {
        return Diagnostic::error("E-FAILED-DEPENDENCY", format!("`{reading}` has errors"))
            .with_label(span, format!("`{test}`'s reading, `{reading}`, has errors"))
            .with_note(format!(
                "this can't be accepted until the errors in `{reading}` are fixed"
            ));
    }
    Diagnostic::error("E-NO-READING", format!("this test fact can't be {how} yet"))
        .with_label(
            span,
            format!("`{test}`'s reading, `{reading}`, is declared below"),
        )
        .with_label(info.span, "declared here")
        .with_note(format!(
            "a reading is used from where it is declared on: move `{reading}` above this"
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
        Read::Pending(p) => Err(pending_error(cx.e, cx.span, p, "read")),
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
