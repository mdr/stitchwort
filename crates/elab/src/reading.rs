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
//! Nothing here is trusted: what the elaborator writes is
//! `Iff.forward (r args) h` or `Iff.backward (r args) p`, which the kernel
//! checks.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, apply, force, unfold_once};
use stitchwort_core::{DataId, DefId, Ev, Icit, Sort, Term, Value};
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

/// A reading found for a test: the theorem applied to the test's
/// arguments, and the two sides of its `↔`, in the caller's context.
pub(crate) struct Found {
    pub theorem: DefId,
    /// `r args`.
    pub proof: Term,
    /// The test fact, as the reading states it.
    pub fact: Value,
    /// What it reads as.
    pub prop: Value,
}

/// What the reader found for a test.
pub(crate) enum Read {
    Found(Found),
    /// No reading, after unfolding what could be: the test's head when it
    /// is a function (for the note on `@[reading]`).
    Leaf(Option<DefId>),
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
        let cx = crate::check::Ctx::new(self, at);
        let Some((test, polarity)) = test_fact(&cx, &sides[0])? else {
            return Err(shape(
                "the left side of its `↔` isn't a test fact, `e = True` or `e = False` for a \
                 `Bool` `e`"
                    .to_string(),
            ));
        };
        let Some((head, args)) = head_args(g, &test)? else {
            return Err(shape(
                "its test must be a function applied to the theorem's parameters, each exactly \
                 once"
                    .to_string(),
            ));
        };
        // Each argument a different parameter, and every parameter one.
        let mut slots = vec![usize::MAX; params];
        let mut distinct = args.len() == params;
        for (k, arg) in args.iter().enumerate() {
            match force(g, arg.clone())? {
                Value::Neutral(Head::Var(l, _), s) if s.is_empty() && slots[l] == usize::MAX => {
                    slots[l] = k;
                }
                _ => distinct = false,
            }
        }
        if !distinct || slots.contains(&usize::MAX) {
            return Err(shape(format!(
                "its test `{}` must be a function applied to the theorem's parameters, each \
                 exactly once, so that any test with that head fits it",
                cx.show(&test)
            )));
        }
        let home = match head {
            TestHead::Def(f) => {
                if Some(f) == reg.def(Builtin::IfThenElse) {
                    return Err(shape(
                        "an `if` other than `&&` and `||` can't have a reading".to_string(),
                    ));
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
    Leaf(Option<DefId>),
}

/// The reading of `test` at `polarity` (§5.4): its head's reading, or else
/// the reading of what it unfolds to, one definition at a time, up to
/// [`UNFOLD_LIMIT`] steps.
fn lookup(g: &Ev, e: &Elaborator, test: &Value, polarity: bool) -> Result<Lookup> {
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
        if let Some((theorem, info)) = e.reading_for(polarity, head) {
            return Ok(Lookup::Found(theorem, info, args));
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
        Lookup::Leaf(head) => Read::Leaf(head),
    })
}

/// What a test fact of type `ty` reads as, if it is one and has a
/// reading: for compiling a pattern on it, which needs to know the type it
/// matches (a record pattern does).
pub(crate) fn read_type(g: &Ev, e: &Elaborator, ty: &Value) -> Result<Option<Value>> {
    let Some((test, polarity)) = test_fact_in(g, ty)? else {
        return Ok(None);
    };
    let Lookup::Found(theorem, info, args) = lookup(g, e, &test, polarity)? else {
        return Ok(None);
    };
    let (_, sides) = statement(g, theorem, &info, &args, |_, _| Ok(()))?;
    Ok(Some(sides[1].clone()))
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
}

/// Theorem `theorem` applied to the test's `args` as `info` says.
fn found(cx: &Ctx, theorem: DefId, info: &ReadingInfo, args: &[Value]) -> Result<Found> {
    let mut proof = Term::Def(theorem);
    let (_, sides) = statement(&cx.g(), theorem, info, args, |arg, icit| {
        proof = Term::app_icit(proof.clone(), cx.quote_folded(arg)?, icit);
        Ok(())
    })?;
    Ok(Found {
        theorem,
        proof,
        fact: sides[0].clone(),
        prop: sides[1].clone(),
    })
}

/// `Iff.forward` (`field` 0) or `Iff.backward` (1) of `found`, applied to
/// `arg`.
fn iff_field(cx: &Ctx, found: &Found, field: usize, arg: Term) -> Result<Term> {
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
        iff_field(cx, self, 0, h)
    }

    /// The test fact from a proof `p` of the proposition.
    pub(crate) fn backward(&self, cx: &Ctx, p: Term) -> Result<Term> {
        iff_field(cx, self, 1, p)
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
    wanted: Option<DataId>,
) -> Diagnostic {
    let g = cx.g();
    let fact = if polarity {
        format!("`{}`", cx.show(test))
    } else {
        format!("`{} = False`", cx.show(test))
    };
    match read {
        Read::Found(found) => {
            let mut d = Diagnostic::error("E-NO-READING", format!("this test fact can't be {how}"))
                .with_label(
                    span,
                    format!(
                        "{fact} reads as `{}` (`{}`)",
                        cx.show(&found.prop),
                        g.def(found.theorem).name()
                    ),
                );
            if let Some(w) = wanted {
                d = d.with_note(format!(
                    "this pattern matches `{}`, and `{}` isn't one",
                    g.data(w).name(),
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
    let Some((test, polarity)) = test_fact(cx, expected)? else {
        return Ok(None);
    };
    let read = read(cx, &test, polarity)?;
    match read {
        Read::Found(found) if matches!(force(&cx.g(), found.prop.clone())?, Value::Data(d2, _) if d2 == d) => {
            Ok(Some(found))
        }
        read => Err(no_reading(
            cx,
            span,
            &test,
            polarity,
            &format!("built with `{}`", constructors_shown(cx, d)),
            &read,
            Some(d),
        )),
    }
}

/// For a record literal checked against a test fact `expected` (§6.6):
/// the reading it is checked against, or `None` where `expected` isn't a
/// test fact.
pub(crate) fn for_record(cx: &Ctx, expected: &Value, span: Span) -> Result<Option<Found>> {
    let Some((test, polarity)) = test_fact(cx, expected)? else {
        return Ok(None);
    };
    let read = read(cx, &test, polarity)?;
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
        [c] => c.name.to_string(),
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
    let Some((test, polarity)) = test_fact(cx, rty)? else {
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
    let Some((test, polarity)) = test_fact(cx, rty)? else {
        return Ok(None);
    };
    match read(cx, &test, polarity)? {
        Read::Found(found) => Ok(Some((found.forward(cx, rterm.clone())?, found.prop))),
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
