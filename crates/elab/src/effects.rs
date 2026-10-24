//! Abilities, translated into the prelude's `Comp` trees
//! (docs/proposals/abilities.md).
//!
//! - An `ability` declaration becomes a data type of its operations, a
//!   function giving each operation's result type, and an eliminator that
//!   handlers use (see `Elaborator::ability`).
//! - A row `{A, B | e}` becomes a chain of `Plus`es of the abilities'
//!   operation types, in declaration order, ending in `NoOp` (closed) or in
//!   `sigOp e` for a row variable `e : Sig`. A function type `a -> {E} b` is
//!   `a -> Comp (ops of E) (results of E) b`.
//! - Code checked against `Comp` over a row is elaborated in *computation
//!   mode*: effectful arguments are run first, left to right, with `bind`; an
//!   operation call becomes a `Call` of the operation injected into the row;
//!   and a call to an effectful function whose row differs is moved into the
//!   current row with `translate` along a generated `SigMap`.
//! - `handle` becomes `foldComp`, with the clauses dispatched by the
//!   ability's eliminator and every other operation forwarded.
//!
//! Everything generated here is re-checked by the kernel.

use std::rc::Rc;

use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Elim, Head, Spine, apply, force};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{BinOp, Bracket, Clause, Expr, Name as AstName, Pattern};

use crate::Global;
use crate::check::{
    Ctx, Result, builtin_data, builtin_def, check, check_if, check_type, infer, infer_head, insert,
};

/// An ability declared with `ability`.
pub struct AbilityInfo {
    pub name: String,
    /// One constructor per operation, holding its argument. It has the
    /// ability's parameters.
    pub op_data: DataId,
    /// `(params) -> Op params -> Type`: what each operation returns.
    pub res: DefId,
    /// `[params] -> [r : Type] -> clause₁ -> … -> (o : Op params) ->
    /// (res o -> r) -> r`, where clause i is `(x : Aᵢ) -> (Bᵢ -> r) -> r`.
    pub elim: DefId,
    /// Operation names, in constructor order.
    pub ops: Vec<String>,
    /// Where it sorts in a row: the library's first, then by full logical
    /// name (`Std.IO`, `Main.Counter`, `Day05.Log`). Rows list abilities in
    /// this order, which depends only on names.
    pub order: (bool, String),
}

/// A row: abilities (each at most once), then a tail, and whether it's
/// `Partial`, which isn't an ability but a mode: a computation in a partial
/// row is a `Delay` rather than a `Comp` (docs/proposals/partial.md §7.3.1).
#[derive(Clone)]
pub struct Row {
    pub labels: Vec<Label>,
    /// A row variable (a value of type `Sig`), or `None` for a closed row.
    pub tail: Option<Value>,
    pub partial: bool,
}

/// The `ability` of a label that's the private recursion signature of the
/// partial group being described (`Rec A`, answered with `RecRes B`; see
/// [`Recursion`]). It's always first in a description's row, and never
/// written in a type.
pub const REC: usize = usize::MAX;

/// While a partial recursive group's members are described: what their
/// requests are (docs/proposals/partial.md §7.3).
#[derive(Clone)]
pub struct Recursion {
    /// What each request is answered with, `B : A -> Type`, in terms of the
    /// group's fixed parameters (the first variables in scope).
    pub ans: Value,
    /// The group's request data type, to recognise it in types.
    pub req_data: DataId,
    /// The members' names, for messages.
    pub names: Vec<String>,
}

#[derive(Clone)]
pub struct Label {
    pub ability: usize,
    pub args: Vec<Value>,
}

impl Row {
    pub fn empty() -> Row {
        Row {
            labels: Vec::new(),
            tail: None,
            partial: false,
        }
    }

    fn suffix(&self, from: usize) -> Row {
        Row {
            labels: self.labels[from..].to_vec(),
            tail: self.tail.clone(),
            partial: self.partial,
        }
    }

    /// Whether this is the empty row: no abilities, no row variable, and
    /// total. A computation in it can perform nothing, so it's run where it
    /// stands rather than sequenced (see [`in_place`]).
    pub fn is_empty(&self) -> bool {
        self.labels.is_empty() && self.tail.is_none() && !self.partial
    }

    /// The same abilities, in total mode.
    fn total(&self) -> Row {
        Row {
            partial: false,
            ..self.clone()
        }
    }

    fn position(&self, ability: usize) -> Option<usize> {
        self.labels.iter().position(|l| l.ability == ability)
    }
}

// The prelude's machinery, by identity (the built-in registry)

fn data(cx: &Ctx, b: Builtin) -> Result<DataId> {
    builtin_data(cx, b)
}

fn def(cx: &Ctx, b: Builtin) -> Result<DefId> {
    builtin_def(cx, b)
}

/// `b [implicits…] explicits…`, quoting the implicit arguments.
fn call(cx: &Ctx, b: Builtin, implicits: &[Value], explicits: Vec<Term>) -> Result<Term> {
    let mut term = Term::Def(def(cx, b)?);
    for v in implicits {
        term = Term::app_icit(term, cx.quote(v)?, Icit::Implicit);
    }
    for t in explicits {
        term = Term::app(term, t);
    }
    Ok(term)
}

// Rows as types

fn label_ops(cx: &Ctx, label: &Label) -> Value {
    if label.ability == REC {
        // `Rec A`, recognised by `decode` only while describing.
        let rec = data(cx, Builtin::Rec).expect("the prelude declares `Rec`");
        return Value::Data(rec, label.args.clone());
    }
    Value::Data(cx.e.abilities[label.ability].op_data, label.args.clone())
}

fn label_res(cx: &Ctx, label: &Label) -> Result<Value> {
    if label.ability == REC {
        // `RecRes [A] B`.
        let rec = cx.e.recursion.as_ref().expect("only while describing");
        let f = Value::Neutral(Head::Def(def(cx, Builtin::RecRes)?), Spine::new());
        let f =
            stitchwort_core::value::apply_icit(cx.g(), f, label.args[0].clone(), Icit::Implicit)?;
        return Ok(apply(cx.g(), f, rec.ans.clone())?);
    }
    let info = &cx.e.abilities[label.ability];
    let mut f = Value::Neutral(Head::Def(info.res), Spine::new());
    for a in &label.args {
        f = apply(cx.g(), f, a.clone())?;
    }
    Ok(f)
}

/// The operation type of a row: `Plus A (Plus B … end)`.
pub fn ops(cx: &Ctx, row: &Row) -> Result<Value> {
    let g = cx.g();
    let mut value = match &row.tail {
        Some(e) => apply(
            g,
            Value::Neutral(Head::Def(def(cx, Builtin::SigOp)?), Spine::new()),
            e.clone(),
        )?,
        None => Value::Data(data(cx, Builtin::NoOp)?, Vec::new()),
    };
    let plus = data(cx, Builtin::Plus)?;
    for label in row.labels.iter().rev() {
        value = Value::Data(plus, vec![label_ops(cx, label), value]);
    }
    Ok(value)
}

/// The result-type function of a row: `PlusRes resA (PlusRes resB … end)`.
pub fn res(cx: &Ctx, row: &Row) -> Result<Value> {
    let g = cx.g();
    let mut value = match &row.tail {
        Some(e) => apply(
            g,
            Value::Neutral(Head::Def(def(cx, Builtin::SigRes)?), Spine::new()),
            e.clone(),
        )?,
        None => Value::Neutral(Head::Def(def(cx, Builtin::NoRes)?), Spine::new()),
    };
    let plus_res = def(cx, Builtin::PlusRes)?;
    for (i, label) in row.labels.iter().enumerate().rev() {
        let rest_ops = ops(cx, &row.suffix(i + 1))?;
        let mut f = Value::Neutral(Head::Def(plus_res), Spine::new());
        f = stitchwort_core::value::apply_icit(g, f, label_ops(cx, label), Icit::Implicit)?;
        f = stitchwort_core::value::apply_icit(g, f, rest_ops, Icit::Implicit)?;
        f = apply(g, f, label_res(cx, label)?)?;
        value = apply(g, f, value)?;
    }
    Ok(value)
}

/// `Comp (ops row) (res row) t`, or `Delay (ops row) (res row) t` for a
/// partial row.
pub fn comp_type(cx: &Ctx, row: &Row, t: Value) -> Result<Value> {
    if row.partial {
        let delay = primitive(cx, Primitive::Delay)?;
        let mut ty = Value::Neutral(Head::Def(delay), Spine::new());
        for arg in [ops(cx, row)?, res(cx, row)?, t] {
            ty = apply(cx.g(), ty, arg)?;
        }
        return Ok(ty);
    }
    Ok(Value::Data(
        data(cx, Builtin::Comp)?,
        vec![ops(cx, row)?, res(cx, row)?, t],
    ))
}

/// The definition admitted as primitive `prim`.
fn primitive(cx: &Ctx, prim: Primitive) -> Result<DefId> {
    cx.g().builtins.primitive_id(prim).ok_or_else(|| {
        cx.error(
            "E-UNKNOWN-NAME",
            format!("`Partial` needs the prelude's `{}`", prim.name()),
            "here",
        )
    })
}

/// The row an operation type stands for, if it's built from abilities.
pub fn decode(cx: &Ctx, op_type: &Value) -> Result<Option<Row>> {
    let g = cx.g();
    let ability_of =
        |d: DataId| -> Option<usize> { cx.e.abilities.iter().position(|a| a.op_data == d) };
    let (Ok(plus), Ok(no_op), Ok(sig), Ok(sig_op)) = (
        data(cx, Builtin::Plus),
        data(cx, Builtin::NoOp),
        data(cx, Builtin::Sig),
        def(cx, Builtin::SigOp),
    ) else {
        return Ok(None);
    };
    // A description's private recursion signature, `Rec A`.
    let rec = match cx.e.recursion {
        Some(_) => data(cx, Builtin::Rec).ok(),
        None => None,
    };
    let mut labels = Vec::new();
    let mut value = force(g, op_type.clone())?;
    loop {
        match value {
            Value::Data(d, args) if d == plus => {
                match force(g, args[0].clone())? {
                    Value::Data(od, oargs) if Some(od) == rec => labels.push(Label {
                        ability: REC,
                        args: oargs,
                    }),
                    Value::Data(od, oargs) => match ability_of(od) {
                        Some(ability) => labels.push(Label {
                            ability,
                            args: oargs,
                        }),
                        None => return Ok(None),
                    },
                    _ => return Ok(None),
                }
                value = force(g, args[1].clone())?;
            }
            Value::Data(d, _) if d == no_op => {
                no_duplicates(cx, &labels)?;
                return Ok(Some(Row {
                    labels,
                    tail: None,
                    partial: false,
                }));
            }
            Value::Neutral(Head::Def(id), spine) if id == sig_op && spine.len() == 1 => {
                let stitchwort_core::value::Elim::App(x, _) = &spine[0] else {
                    return Ok(None);
                };
                match force(g, x.clone())? {
                    Value::Ctor(d, 0, fields) if d == sig => value = force(g, fields[0].clone())?,
                    x => {
                        no_duplicates(cx, &labels)?;
                        return Ok(Some(Row {
                            labels,
                            tail: Some(x),
                            partial: false,
                        }));
                    }
                }
            }
            _ => return Ok(None),
        }
    }
}

/// A row has each ability at most once. Rows written in source and rows the
/// elaborator builds always do, but a row variable `e : Sig` instantiated by
/// hand with a `Sig` that repeats an ability (`{Log | e}` with `e` holding
/// `Log`) reads as a row that doesn't. Source operations always use the
/// first copy, and moving a computation between rows maps every copy to the
/// one of the same ability, so the copies would silently merge. This is the
/// "lacks" check, made where a row is read (docs/proposals/abilities.md).
fn no_duplicates(cx: &Ctx, labels: &[Label]) -> Result<()> {
    for (i, label) in labels.iter().enumerate() {
        if label.ability != REC && labels[..i].iter().any(|l| l.ability == label.ability) {
            return Err(cx
                .error(
                    "E-DUPLICATE",
                    format!("`{}` appears twice in this row", ability_name(cx, label)),
                    "here",
                )
                .with_note("a row has each ability at most once")
                .with_note(
                    "a row variable (`e` in `{A | e}`) can't stand for a signature that \
                     already contains `A`",
                ));
        }
    }
    Ok(())
}

/// If `ty` is `Comp` or `Delay` over a row of abilities: the row (partial
/// for a `Delay`) and the result type.
pub fn comp_parts(cx: &Ctx, ty: &Value) -> Result<Option<(Row, Value)>> {
    let Ok(comp) = data(cx, Builtin::Comp) else {
        return Ok(None);
    };
    let delay = cx.g().builtins.primitive_id(Primitive::Delay);
    Ok(match force(cx.g(), ty.clone())? {
        Value::Data(d, args) if d == comp => {
            decode(cx, &args[0])?.map(|row| (row, args[2].clone()))
        }
        Value::Neutral(Head::Def(d), spine) if Some(d) == delay && spine.len() == 3 => {
            let arg = |i: usize| match &spine[i] {
                Elim::App(v, _) => Some(v.clone()),
                Elim::J { .. } => None,
            };
            match (arg(0), arg(2)) {
                (Some(op), Some(t)) => decode(cx, &op)?.map(|row| {
                    (
                        Row {
                            partial: true,
                            ..row
                        },
                        t,
                    )
                }),
                _ => None,
            }
        }
        _ => None,
    })
}

fn ability_name(cx: &Ctx, label: &Label) -> String {
    if label.ability == REC {
        return "Partial".to_string();
    }
    cx.e.abilities[label.ability].name.clone()
}

/// Makes the abilities in common agree, then solves an unknown tail of
/// `open` with whatever `other` has that `open` doesn't.
fn solve_tail(cx: &mut Ctx, open: &Row, other: &Row) -> Result<bool> {
    let Some(tail) = &open.tail else {
        return Ok(false);
    };
    if !matches!(
        force(cx.g(), tail.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return Ok(false);
    }
    for label in &open.labels {
        if let Some(p) = other.position(label.ability) {
            agree(cx, label, &other.labels[p])?;
        }
    }
    let rest = Row {
        labels: other
            .labels
            .iter()
            .filter(|l| open.position(l.ability).is_none())
            .cloned()
            .collect(),
        tail: other.tail.clone(),
        partial: false,
    };
    let sig = Value::Ctor(
        data(cx, Builtin::Sig)?,
        0,
        vec![ops(cx, &rest)?, res(cx, &rest)?].into(),
    );
    cx.unify(tail, &sig)
}

fn agree(cx: &mut Ctx, a: &Label, b: &Label) -> Result<()> {
    for (x, y) in a.args.iter().zip(&b.args) {
        if !cx.unify(x, y)? {
            if a.ability == REC {
                // Requests for a different instance of the group: a call
                // that changes its type parameters.
                let names =
                    cx.e.recursion
                        .as_ref()
                        .map(|r| r.names.join("`, `"))
                        .unwrap_or_default();
                return Err(cx
                    .error(
                        "E-PARTIAL-NONUNIFORM",
                        format!("this recursive call to `{names}` changes its type parameters"),
                        format!(
                            "this calls it at `{}`, but it's being defined at `{}`",
                            show_request(cx, x),
                            show_request(cx, y)
                        ),
                    )
                    .with_note(
                        "a partial recursive function's recursive calls must pass its type \
                         parameters on unchanged (non-uniform recursion, which changes them, \
                         isn't supported)",
                    ));
            }
            return Err(cx.error(
                "E-TYPE-MISMATCH",
                format!(
                    "`{}` is used with different arguments: `{}` and `{}`",
                    ability_name(cx, a),
                    cx.show(x),
                    cx.show(y)
                ),
                "here",
            ));
        }
    }
    Ok(())
}

/// A partial group's request type, `f.Request ps`, as its parameters `ps`.
fn show_request(cx: &Ctx, req: &Value) -> String {
    match force(cx.g(), req.clone()) {
        Ok(Value::Data(_, args)) if !args.is_empty() => args
            .iter()
            .map(|a| cx.show(a))
            .collect::<Vec<_>>()
            .join(" "),
        _ => cx.show(req),
    }
}

fn same_shape(cx: &Ctx, a: &Row, b: &Row) -> Result<bool> {
    Ok(a.labels.len() == b.labels.len()
        && a.labels
            .iter()
            .zip(&b.labels)
            .all(|(x, y)| x.ability == y.ability)
        && match (&a.tail, &b.tail) {
            (None, None) => true,
            (Some(x), Some(y)) => cx.unify(x, y)?,
            _ => false,
        })
}

fn not_allowed(cx: &Ctx, label: &Label) -> Diagnostic {
    if label.ability == REC {
        return escape(cx);
    }
    let name = ability_name(cx, label);
    cx.error(
        "E-ABILITY",
        format!("this may perform `{name}`, which isn't allowed here"),
        format!("`{name}` isn't in the abilities of the enclosing function or handler"),
    )
    .with_note(format!(
        "add `{name}` to the function's type (`-> {{{name} …}} …`), or handle it"
    ))
}

/// A recursive call of the partial group being described, used where
/// nothing can answer its requests (docs/proposals/partial.md §7.3.4).
pub(crate) fn escape(cx: &Ctx) -> Diagnostic {
    let names = match &cx.e.recursion {
        Some(rec) => rec.names.clone(),
        None => Vec::new(),
    };
    let shown = names
        .iter()
        .map(|n| format!("`{n}`"))
        .collect::<Vec<_>>()
        .join(", ");
    let first = names.first().cloned().unwrap_or_default();
    cx.error(
        "E-PARTIAL-ESCAPE",
        format!("a recursive call to {shown} can't escape its definition"),
        format!("this calls {shown}, but it's returned or stored where nothing can run the call"),
    )
    .with_note(format!(
        "inside `{first}`'s definition, a call to {shown} is a request that only `{first}`'s own \
         definition can answer, so it can't be part of the result"
    ))
    .with_note(
        "move the loop into a definition of its own and return a function that calls that \
         definition",
    )
}

/// Running a partial computation (`term`) in total code.
fn partial_in_total(cx: &Ctx, term: &Term) -> Diagnostic {
    let label = match term.spine().0 {
        Term::Def(id) => format!(
            "`{}` is `Partial`: it might not finish",
            cx.g().def(*id).name
        ),
        _ => "this is `Partial`: it might not finish".to_string(),
    };
    cx.error(
        "E-PARTIAL",
        "a computation that might not finish can't run here",
        label,
    )
    .with_note(
        "code whose type doesn't say `Partial` must finish, so it can't run anything that might \
         not; add `Partial` to the enclosing function's type (`-> {Partial} …`)",
    )
}

/// Moves `term : Comp from t` (or `Delay from t`) into `to`, solving an
/// unknown tail of `from`. A total computation moves into a partial row
/// with `lift`; a partial one can't move into a total row.
fn lift(cx: &mut Ctx, term: Term, from: Row, to: &Row, t: &Value) -> Result<Term> {
    if from.partial && !to.partial {
        return Err(partial_in_total(cx, &term));
    }
    let mut from = refresh(cx, &from)?;
    let mut to = refresh(cx, to)?;
    let missing_in = |a: &Row, b: &Row| -> Vec<Label> {
        b.labels
            .iter()
            .filter(|l| a.position(l.ability).is_none())
            .cloned()
            .collect()
    };
    let from_open = match &from.tail {
        Some(t) => is_unknown(cx, t)?,
        None => false,
    };
    let to_open = match &to.tail {
        Some(t) => is_unknown(cx, t)?,
        None => false,
    };
    // The same unknown on both sides (compared without solving anything).
    let meta_of = |row: &Row| -> Result<Option<usize>> {
        Ok(
            match row
                .tail
                .as_ref()
                .map(|t| force(cx.g(), t.clone()))
                .transpose()?
            {
                Some(Value::Neutral(Head::Meta(m), _)) => Some(m),
                _ => None,
            },
        )
    };
    let same_tail = from_open && to_open && meta_of(&from)? == meta_of(&to)?;
    if from_open && to_open && !same_tail {
        // `{A | ?f}` into `{B | ?t}`: with a fresh `?r`, `?f` is `B∖A | ?r`
        // and `?t` is `A∖B | ?r`.
        let fresh = cx.fresh_meta();
        let fresh = cx.eval(&fresh)?;
        let (for_from, for_to) = (missing_in(&from, &to), missing_in(&to, &from));
        extend_with(cx, &from, for_from, fresh.clone())?;
        extend_with(cx, &to, for_to, fresh)?;
        from = refresh(cx, &from)?;
        to = refresh(cx, &to)?;
    } else if from_open && !same_tail {
        solve_tail(cx, &from, &to)?;
        from = refresh(cx, &from)?;
    } else {
        // Abilities the context doesn't list yet go into its unknown tail.
        let missing = missing_in(&to, &from);
        if let Some(first) = missing.first() {
            if same_tail {
                return Err(not_allowed(cx, first));
            }
            match extend(cx, &to, missing.clone())? {
                Some(wider) => to = wider,
                None => return Err(not_allowed(cx, first)),
            }
        }
    }
    for label in &from.labels {
        match to.position(label.ability) {
            Some(p) => agree(cx, label, &to.labels[p])?,
            None => return Err(not_allowed(cx, label)),
        }
    }
    let to = &to;
    let moved = if same_shape(cx, &from, to)? {
        term
    } else {
        let m = mapping(cx, &from, to)?;
        call(
            cx,
            if from.partial {
                Builtin::MapSig
            } else {
                Builtin::Translate
            },
            &[
                ops(cx, &from)?,
                res(cx, &from)?,
                ops(cx, to)?,
                res(cx, to)?,
                t.clone(),
            ],
            vec![m, term],
        )?
    };
    if to.partial && !from.partial {
        return call(
            cx,
            Builtin::Lift,
            &[ops(cx, to)?, res(cx, to)?, t.clone()],
            vec![moved],
        );
    }
    Ok(moved)
}

/// `bind`, or `bindD` in a partial row.
fn bind_name(row: &Row) -> Builtin {
    if row.partial {
        Builtin::BindD
    } else {
        Builtin::Bind
    }
}

/// Re-reads a row whose tail may have been solved since it was read.
fn refresh(cx: &Ctx, row: &Row) -> Result<Row> {
    if row.tail.is_none() {
        return Ok(row.clone());
    }
    let ty = cx.eval(&cx.quote(&ops(cx, row)?)?)?;
    Ok(match decode(cx, &ty)? {
        Some(fresh) => Row {
            partial: row.partial,
            ..fresh
        },
        None => row.clone(),
    })
}

fn is_unknown(cx: &Ctx, value: &Value) -> Result<bool> {
    Ok(matches!(
        force(cx.g(), value.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ))
}

/// If `row` ends in an unknown, adds `extra` to it, keeping it open for
/// more (the unknown becomes `extra` and a fresh unknown). Returns the
/// wider row.
fn extend(cx: &mut Ctx, row: &Row, extra: Vec<Label>) -> Result<Option<Row>> {
    match &row.tail {
        Some(tail) if is_unknown(cx, tail)? => {}
        _ => return Ok(None),
    }
    let fresh = cx.fresh_meta();
    let fresh = cx.eval(&fresh)?;
    if !extend_with(cx, row, extra, fresh)? {
        return Ok(None);
    }
    Ok(Some(refresh(cx, row)?))
}

/// Solves `row`'s unknown tail as `extra` followed by `tail`.
fn extend_with(cx: &mut Ctx, row: &Row, extra: Vec<Label>, tail: Value) -> Result<bool> {
    let Some(old) = &row.tail else {
        return Ok(false);
    };
    let added = Row {
        labels: extra,
        tail: Some(tail),
        partial: false,
    };
    let sig = Value::Ctor(
        data(cx, Builtin::Sig)?,
        0,
        vec![ops(cx, &added)?, res(cx, &added)?].into(),
    );
    cx.unify(old, &sig)
}

/// A `SigMap` from row `from` into row `to`, whose abilities include all of
/// `from`'s (with the same tail, if `from` has one).
fn mapping(cx: &mut Ctx, from: &Row, to: &Row) -> Result<Term> {
    let mut m = match &from.tail {
        None => call(
            cx,
            Builtin::SigFromNo,
            &[ops(cx, to)?, res(cx, to)?],
            Vec::new(),
        )?,
        Some(t) => {
            let same = match to.tail.as_ref() {
                Some(u) => cx.unify(t, u)?,
                None => false,
            };
            if !same {
                return Err(cx.error(
                    "E-ABILITY",
                    "this may perform abilities that aren't allowed here",
                    "its row variable isn't part of the enclosing function's abilities",
                ));
            }
            injection(cx, to, to.labels.len())?
        }
    };
    for (j, label) in from.labels.iter().enumerate().rev() {
        let pos = to.position(label.ability).expect("checked by the caller");
        let rest = from.suffix(j + 1);
        let inj = injection(cx, to, pos)?;
        m = call(
            cx,
            Builtin::SigCase,
            &[
                label_ops(cx, label),
                ops(cx, &rest)?,
                ops(cx, to)?,
                label_res(cx, label)?,
                res(cx, &rest)?,
                res(cx, to)?,
            ],
            vec![inj, m],
        )?;
    }
    Ok(m)
}

/// The mapping of position `pos` of `to` (an ability, or the tail if `pos`
/// is the number of abilities) into `to`.
fn injection(cx: &Ctx, to: &Row, pos: usize) -> Result<Term> {
    let k = to.labels.len();
    let right = |j: usize| -> Result<Term> {
        let x = &to.labels[j];
        let rest = to.suffix(j + 1);
        call(
            cx,
            Builtin::SigRight,
            &[
                label_ops(cx, x),
                ops(cx, &rest)?,
                label_res(cx, x)?,
                res(cx, &rest)?,
            ],
            Vec::new(),
        )
    };
    // `m` maps `(src_ops, src_res)` into `to.suffix(start)`.
    let (mut m, src_ops, src_res, start) = if pos == k {
        if k == 0 {
            let id = call(
                cx,
                Builtin::SigId,
                &[ops(cx, to)?, res(cx, to)?],
                Vec::new(),
            )?;
            return Ok(id);
        }
        let tail = to.suffix(k);
        (right(k - 1)?, ops(cx, &tail)?, res(cx, &tail)?, k - 1)
    } else {
        let x = &to.labels[pos];
        let rest = to.suffix(pos + 1);
        let left = call(
            cx,
            Builtin::SigLeft,
            &[
                label_ops(cx, x),
                ops(cx, &rest)?,
                label_res(cx, x)?,
                res(cx, &rest)?,
            ],
            Vec::new(),
        )?;
        (left, label_ops(cx, x), label_res(cx, x)?, pos)
    };
    for j in (0..start).rev() {
        let mid = to.suffix(j + 1);
        let outer = to.suffix(j);
        m = call(
            cx,
            Builtin::SigCompose,
            &[
                src_ops.clone(),
                src_res.clone(),
                ops(cx, &mid)?,
                res(cx, &mid)?,
                ops(cx, &outer)?,
                res(cx, &outer)?,
            ],
            vec![m, right(j)?],
        )?;
    }
    Ok(m)
}

// Rows in types

/// Elaborates `{abilities | tail} ty` as a type.
pub fn effect_type(
    cx: &mut Ctx,
    row: &stitchwort_syntax::ast::Row,
    ty: &Expr,
) -> Result<(Term, stitchwort_core::Sort)> {
    let (result, sort) = check_type(cx, ty)?;
    if row.abilities.is_empty() && row.tail.is_none() {
        return Ok((result, sort));
    }
    let mut labels: Vec<Label> = Vec::new();
    let mut partial = false;
    for ability in &row.abilities {
        // `Partial` is a mode, not an ability: it makes the type a `Delay`.
        if let Expr::Var(name) = ability
            && name.text == "Partial"
        {
            if partial {
                return Err(cx
                    .error("E-DUPLICATE", "`Partial` appears twice in this row", "here")
                    .with_note("a row has each ability at most once"));
            }
            partial = true;
            continue;
        }
        let label = ability_label(cx, ability)?;
        if labels.iter().any(|l| l.ability == label.ability) {
            return Err(cx
                .error(
                    "E-DUPLICATE",
                    format!("`{}` appears twice in this row", ability_name(cx, &label)),
                    "here",
                )
                .with_note("a row has each ability at most once"));
        }
        labels.push(label);
    }
    labels.sort_by(|a, b| {
        cx.e.abilities[a.ability]
            .order
            .cmp(&cx.e.abilities[b.ability].order)
    });
    let tail = match &row.tail {
        None => None,
        Some(name) => {
            let sig = Value::Data(data(cx, Builtin::Sig)?, Vec::new());
            let term = check(cx, &Expr::Var(name.clone()), &sig)?;
            Some(cx.eval(&term)?)
        }
    };
    let result_value = cx.eval(&result)?;
    let row = Row {
        labels,
        tail,
        partial,
    };
    let ty = comp_type(cx, &row, result_value)?;
    if !matches!(sort, stitchwort_core::Sort::Type(0)) {
        return Err(cx.error(
            "E-UNIVERSE",
            "an effectful function's result must be a type of data",
            "this is in a larger universe, or a proposition",
        ));
    }
    Ok((cx.quote(&ty)?, stitchwort_core::Sort::Type(0)))
}

/// `State s` in a row.
fn ability_label(cx: &mut Ctx, expr: &Expr) -> Result<Label> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f;
    }
    args.reverse();
    let Expr::Var(name) = head else {
        return Err(cx.error("E-ABILITY", "expected an ability", "here"));
    };
    cx.e.note_name(name);
    let found = cx.e.named(&name.text).copied();
    if let Some((Global::Unchecked(item), _)) = found {
        return Err(cx.e.unchecked(name, item));
    }
    if let Some((Global::Failed, _)) = found {
        return Err(crate::module::failed_name(name));
    }
    if let Some((Global::Pending(file, _), _)) = found {
        return Err(cx.e.unloaded(name, file));
    }
    let Some((Global::Ability(a), _)) = found else {
        let mut d = cx.error(
            "E-ABILITY",
            format!("`{}` isn't an ability", name.text),
            "rows list abilities, declared with `ability`",
        );
        // A library ability outside the prelude needs an import (D266).
        if found.is_none()
            && cx.e.scope.is_std_root(&name.text)
            && !cx.e.scope.is_prelude(&name.text)
        {
            d = d.with_note(format!(
                "`{0}` is `Std.{0}`, which isn't in the prelude; add `import Std ({0})`, or write `Std.{0}`",
                name.text
            ));
        }
        return Err(d);
    };
    let op_data = cx.e.abilities[a].op_data;
    let params = cx.g().data(op_data).params.clone();
    if args.len() != params.len() {
        return Err(cx.error(
            "E-ARITY",
            format!("`{}` takes {} argument(s)", name.text, params.len()),
            "here",
        ));
    }
    let mut values = Vec::new();
    for ((_, param_ty), arg) in params.iter().zip(args) {
        let ty = stitchwort_core::value::eval(cx.g(), &values, param_ty)?;
        let term = check(cx, arg, &ty)?;
        values.push(cx.eval(&term)?);
    }
    Ok(Label {
        ability: a,
        args: values,
    })
}

// Computation mode

/// Whether elaborating `expr` may perform operations: it calls an operation,
/// an effectful function (with enough arguments), or contains sequencing,
/// `handle`, or a `let` whose value or rest may. Lambda bodies don't count.
pub fn may_perform(cx: &Ctx, expr: &Expr) -> Result<bool> {
    cx.g().budget.nesting(crate::check::PASS)?;
    let any = |items: &mut dyn Iterator<Item = &Expr>| -> Result<bool> {
        for item in items {
            if may_perform(cx, item)? {
                return Ok(true);
            }
        }
        Ok(false)
    };
    Ok(match expr {
        Expr::Var(_) | Expr::App(..) => call_performs(cx, expr, 0)?,
        // `x |> y => body` runs `body`; `x |> y z => …` is a function.
        Expr::Pipe(value, f) => {
            may_perform(cx, value)?
                || match &**f {
                    Expr::Lam(names, body, _) => names.len() == 1 && may_perform(cx, body)?,
                    Expr::TypedLam(_, _, body, _) => may_perform(cx, body)?,
                    f => call_performs(cx, f, 1)?,
                }
        }
        Expr::Binary(_, a, b) => any(&mut [&**a, &**b].into_iter())?,
        Expr::Match {
            scrutinees, alts, ..
        } => any(&mut scrutinees
            .iter()
            .map(|s| &s.expr)
            .chain(alts.iter().map(|a| &a.body)))?,
        Expr::Neg(a, _) => may_perform(cx, a)?,
        // A `let` performs what its value or the rest of the block does
        // (docs/proposals/let.md §5). The rest is judged here without the
        // name in scope, and asked again once it is (so a call of a bound
        // effectful function is judged by its type then).
        Expr::Let { value, body, .. } => may_perform(cx, value)? || may_perform(cx, body)?,
        Expr::Seq(..) | Expr::Handle { .. } => true,
        // The definitions are elaborated on their own; what's run is the
        // rest of the block (asked again once the names are in scope).
        Expr::LocalDefs { body, .. } => may_perform(cx, body)?,
        Expr::If {
            cond,
            then,
            otherwise,
            ..
        } => any(&mut [&**cond, &**then, &**otherwise].into_iter())?,
        Expr::List(items, _) => any(&mut items.iter())?,
        Expr::Record { base, fields, .. } => any(&mut base
            .iter()
            .map(|b| &**b)
            .chain(fields.iter().map(|(_, e)| e)))?,
        Expr::CtorFields { fields, .. } => any(&mut fields.iter().map(|(_, e)| e))?,
        Expr::Field(e, field) => may_perform(cx, e)? || dot_performs(cx, e, field, 0)?,
        Expr::Ann(e, _, _) | Expr::NamedArg(_, e, _, _) => may_perform(cx, e)?,
        Expr::Tuple(a, b, _) => any(&mut [&**a, &**b].into_iter())?,
        _ => false,
    })
}

/// Whether the call `expr` (a variable, or an application) may perform
/// operations, given `extra` more arguments (the value piped in by `|>`).
fn call_performs(cx: &Ctx, expr: &Expr, extra: usize) -> Result<bool> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f;
    }
    for arg in &args {
        if may_perform(cx, arg)? {
            return Ok(true);
        }
    }
    let explicit = extra
        + args
            .iter()
            .filter(|a| !matches!(a, Expr::NamedArg(.., Bracket::Square)))
            .count();
    // With explicit arguments by name, what the call reaches is where they
    // put it: up to the last one given, or, if it leaves a parameter out,
    // up to that parameter, since the rest is inside the function it
    // becomes (docs/proposals/named-arguments.md §4.5 R3).
    let named = args
        .iter()
        .any(|a| matches!(a, Expr::NamedArg(.., Bracket::Round)));
    args.reverse();
    let reached =
        |ty: &Value| crate::named::reached(cx, ty, expr, &args, extra).unwrap_or(explicit);
    Ok(match head {
        Expr::Var(name) => match head_type(cx, name) {
            // An operation on its own is a function value.
            HeadType::Op => explicit > 0,
            HeadType::Typed(ty) if named => performs_after(cx, ty.clone(), reached(&ty))?,
            HeadType::Typed(ty) => performs_after(cx, ty, explicit)?,
            HeadType::Def(id) if named => {
                let ty = cx.g().def(id).ty_value.clone();
                performs_after(cx, ty.clone(), reached(&ty))?
            }
            HeadType::Def(id) => def_performs_after(cx, id, explicit)?,
            HeadType::Other => false,
        },
        Expr::Field(recv, field) => {
            may_perform(cx, recv)? || dot_performs(cx, recv, field, explicit)?
        }
        other => may_perform(cx, other)?,
    })
}

/// Whether `recv.field` with `explicit` more arguments reaches a computation
/// type, when what it calls can be found without elaborating `recv`.
fn dot_performs(cx: &Ctx, recv: &Expr, field: &AstName, explicit: usize) -> Result<bool> {
    // A local definition named from outside: the receiver isn't an argument.
    if let Some(f) = crate::dot::helper(cx, recv, field) {
        return def_performs_after(cx, f, explicit);
    }
    match crate::dot::target(cx, recv, field)? {
        Some(f) => def_performs_after(cx, f, explicit + 1),
        None => Ok(false),
    }
}

enum HeadType {
    Op,
    Typed(Value),
    Def(DefId),
    Other,
}

fn head_type(cx: &Ctx, name: &AstName) -> HeadType {
    if let Ok(Some((_, ty))) = cx.local(&name.text) {
        return HeadType::Typed(ty);
    }
    if let Some(level) = cx.lookup(&name.text) {
        return HeadType::Typed(cx.types[level].clone());
    }
    match cx.e.named(&name.text) {
        Some((Global::Op(..), _)) => HeadType::Op,
        Some((Global::Def(id), _)) => HeadType::Def(*id),
        _ => HeadType::Other,
    }
}

/// [`performs_after`] for a call of definition `id`. Remembered for a final
/// definition (`Elaborator::performs`): its type never changes, and this is
/// asked for every call each time an expression around it is checked. What
/// else the answer reads (the abilities declared so far, and whether a
/// description's recursion is in scope, [`decode`]) is part of the key.
fn def_performs_after(cx: &Ctx, id: DefId, explicit: usize) -> Result<bool> {
    let g = cx.g();
    let key = (id, explicit, cx.e.abilities.len(), cx.e.recursion.is_some());
    if let Some(&known) = cx.e.performs.borrow().get(&key) {
        return Ok(known);
    }
    let found = performs_after(cx, g.def(id).ty_value.clone(), explicit)?;
    if g.def(id).state() == stitchwort_core::globals::State::Final {
        cx.e.performs.borrow_mut().insert(key, found);
    }
    Ok(found)
}

/// Whether a function of type `ty`, given `explicit` arguments, reaches a
/// computation type.
fn performs_after(cx: &Ctx, mut ty: Value, mut explicit: usize) -> Result<bool> {
    let g = cx.g();
    let mut level = cx.level();
    loop {
        if comp_parts(cx, &ty)?.is_some() {
            return Ok(true);
        }
        match force(g, ty)? {
            Value::Pi(_, icit, _, cod) => {
                if !icit.is_implicit() {
                    if explicit == 0 {
                        return Ok(false);
                    }
                    explicit -= 1;
                }
                ty = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            _ => return Ok(false),
        }
    }
}

/// `Done v` (or `now v`), as a computation in `row` returning a `t`.
fn done(cx: &Ctx, row: &Row, t: &Value, v: Term) -> Result<Term> {
    if row.partial {
        return call(
            cx,
            Builtin::Now,
            &[ops(cx, row)?, res(cx, row)?, t.clone()],
            vec![v],
        );
    }
    let ty = comp_type(cx, row, t.clone())?;
    Ok(Term::Ann(
        Rc::new(Term::ctor(data(cx, Builtin::Comp)?, 0, vec![v])),
        Rc::new(cx.quote(&ty)?),
    ))
}

/// Checks `expr` as a computation in `row` returning a `t`.
pub fn comp_check(cx: &mut Ctx, expr: &Expr, row: &Row, t: &Value) -> Result<Term> {
    cx.g().budget.nesting(crate::check::PASS)?;
    match expr {
        Expr::LocalDefs { defs, body, .. } => {
            crate::local::around(cx, defs, |cx| comp_check(cx, body, row, t))
        }
        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            // The variable's type as written, for dot notation: the
            // annotation, or the value's.
            let mut written = None;
            let (term, ty, effectful) = match ty {
                Some(ty) => {
                    let (ty, _) = check_type(cx, ty)?;
                    written = Some(crate::dot::Written::With(
                        Rc::new(ty.clone()),
                        cx.env.clone(),
                    ));
                    let ty = cx.eval(&ty)?;
                    if may_perform(cx, value)? {
                        (comp_check(cx, value, row, &ty)?, ty, true)
                    } else {
                        (check(cx, value, &ty)?, ty, false)
                    }
                }
                // A call whose effectful arguments run first: the final
                // call is pure, and its written result type is recorded.
                None if matches!(&**value, Expr::App(..)) && may_perform(cx, value)? => {
                    let (c, ty, w) = comp_app(cx, value, row, None)?;
                    written = w;
                    (c, ty, true)
                }
                None if may_perform(cx, value)? => {
                    let (c, ty) = comp_infer(cx, value, row)?;
                    (c, ty, true)
                }
                None => {
                    let (term, ty) = infer(cx, value)?;
                    let (term, ty) = insert(cx, term, ty)?;
                    written = crate::dot::written_of(cx, &term)?;
                    (term, ty, false)
                }
            };
            sequence(cx, row, t, &name.text, term, ty, effectful, |cx| {
                if let Some(w) = written {
                    cx.set_written(w);
                }
                comp_check(cx, body, row, t)
            })
        }
        Expr::Seq(first, rest) => {
            let (term, ty, effectful) = if may_perform(cx, first)? {
                let (c, ty) = comp_infer(cx, first, row)?;
                (c, ty, true)
            } else {
                let (term, ty) = infer(cx, first)?;
                let (term, ty) = insert(cx, term, ty)?;
                (term, ty, false)
            };
            sequence(cx, row, t, "_", term, ty, effectful, |cx| {
                comp_check(cx, rest, row, t)
            })
        }
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            if !may_perform(cx, cond)? {
                return branches(cx, row, t, |cx, expected| {
                    check_if(cx, binder.as_ref(), cond, then, otherwise, expected)
                });
            }
            if binder.is_some() {
                return Err(cx.error(
                    "E-ABILITY",
                    "`if h: P` needs a proposition, which can't perform operations",
                    "here",
                ));
            }
            // Run the condition first, then branch on its result.
            let bool_ty = Value::Data(data(cx, Builtin::Bool)?, Vec::new());
            let c = comp_check(cx, cond, row, &bool_ty)?;
            let var = Expr::Var(AstName {
                text: "%cond".into(),
                span: cond.span(),
            });
            sequence(cx, row, t, "%cond", c, bool_ty, true, |cx| {
                branches(cx, row, t, |cx, expected| {
                    check_if(cx, None, &var, then, otherwise, expected)
                })
            })
        }
        Expr::Match {
            scrutinees,
            alts,
            span,
            kind,
        } => {
            let mut performs = false;
            for s in scrutinees {
                performs |= may_perform(cx, &s.expr)?;
            }
            if !performs {
                return branches(cx, row, t, |cx, expected| {
                    crate::matching::check_match(cx, expr, expected)
                });
            }
            // Every scrutinee runs once, left to right, before anything else,
            // and the `match` matches the results
            // (docs/proposals/syntax-conveniences.md §4.7).
            run_scrutinees(cx, row, t, scrutinees, Vec::new(), &|cx, bound| {
                let matched = Expr::Match {
                    scrutinees: bound,
                    alts: alts.clone(),
                    span: *span,
                    kind: *kind,
                };
                branches(cx, row, t, |cx, expected| {
                    crate::matching::check_match(cx, &matched, expected)
                })
            })
        }
        Expr::Handle {
            body,
            clauses,
            span,
        } => {
            let saved = std::mem::replace(&mut cx.span, *span);
            let result = handle(cx, body, clauses, row, t);
            cx.span = saved;
            result
        }
        // `a && b`, `a || b`: as an `if`, so `b` runs only if it's needed.
        Expr::Binary(op @ (BinOp::And | BinOp::Or), a, b) if may_perform(cx, expr)? => {
            comp_check(cx, &crate::logic::as_if(*op, a, b), row, t)
        }
        _ if may_perform(cx, expr)? => {
            let (c, ty) = comp_call(cx, expr, row, Some(t))?;
            if cx.unify(&ty, t)? {
                Ok(c)
            } else {
                Err(cx.mismatch(t, &ty))
            }
        }
        _ => {
            let v = check(cx, expr, t)?;
            done(cx, row, t, v)
        }
    }
}

/// An `if`'s or a `match`'s branches, checked by `check` against a
/// computation in `row` returning a `t`. In the empty row they're checked
/// against `t` itself, each running in place what it runs, and the whole is
/// `Done` of that ([`in_place`]).
fn branches(
    cx: &mut Ctx,
    row: &Row,
    t: &Value,
    check: impl FnOnce(&mut Ctx, &Value) -> Result<Term>,
) -> Result<Term> {
    if row.is_empty() {
        let v = check(cx, t)?;
        return done(cx, row, t, v);
    }
    let expected = comp_type(cx, row, t.clone())?;
    check(cx, &expected)
}

/// Runs the scrutinees of a `match` in order, binding each result to a new
/// variable, then elaborates `rest` with the `match`'s scrutinees replaced
/// by those variables (keeping their equations' names, so `h : readLine ()`
/// is about the bound result).
fn run_scrutinees(
    cx: &mut Ctx,
    row: &Row,
    t: &Value,
    scrutinees: &[stitchwort_syntax::ast::Scrutinee],
    mut bound: Vec<stitchwort_syntax::ast::Scrutinee>,
    rest: &dyn Fn(&mut Ctx, Vec<stitchwort_syntax::ast::Scrutinee>) -> Result<Term>,
) -> Result<Term> {
    let Some((first, others)) = scrutinees.split_first() else {
        return rest(cx, bound);
    };
    let (term, ty, effectful) = if may_perform(cx, &first.expr)? {
        let (c, ty) = comp_infer(cx, &first.expr, row)?;
        (c, ty, true)
    } else {
        let (term, ty) = infer(cx, &first.expr)?;
        let (term, ty) = insert(cx, term, ty)?;
        (term, ty, false)
    };
    let name = format!("%scrutinee{}", bound.len());
    bound.push(stitchwort_syntax::ast::Scrutinee {
        name: first.name.clone(),
        expr: Expr::Var(AstName {
            text: name.clone(),
            span: first.expr.span(),
        }),
    });
    sequence(cx, row, t, &name, term, ty, effectful, |cx| {
        run_scrutinees(cx, row, t, others, bound, rest)
    })
}

/// Elaborates `expr` as a computation in `row`, inferring its result type.
pub fn comp_infer(cx: &mut Ctx, expr: &Expr, row: &Row) -> Result<(Term, Value)> {
    cx.g().budget.nesting(crate::check::PASS)?;
    match expr {
        Expr::LocalDefs { defs, body, .. } => {
            crate::local::around(cx, defs, |cx| comp_infer(cx, body, row))
        }
        Expr::Let { .. } | Expr::Seq(..) | Expr::If { .. } | Expr::Handle { .. } => {
            let t = cx.fresh_meta();
            let t = cx.eval(&t)?;
            let c = comp_check(cx, expr, row, &t)?;
            Ok((c, t))
        }
        Expr::Match { .. } => {
            let t = crate::matching::unknown_type(cx, expr);
            let t = cx.eval(&t)?;
            let c = comp_check(cx, expr, row, &t)?;
            Ok((c, t))
        }
        Expr::Binary(BinOp::And | BinOp::Or, ..) if may_perform(cx, expr)? => {
            let t = Value::Data(data(cx, Builtin::Bool)?, Vec::new());
            let c = comp_check(cx, expr, row, &t)?;
            Ok((c, t))
        }
        _ if may_perform(cx, expr)? => comp_call(cx, expr, row, None),
        _ => {
            let (term, ty) = infer(cx, expr)?;
            let (term, ty) = insert(cx, term, ty)?;
            Ok((done(cx, row, &ty, term)?, ty))
        }
    }
}

/// `let name = term` (a computation if `effectful`), then `body`.
#[allow(clippy::too_many_arguments)]
fn sequence(
    cx: &mut Ctx,
    row: &Row,
    t: &Value,
    name: &str,
    term: Term,
    ty: Value,
    effectful: bool,
    body: impl FnOnce(&mut Ctx) -> Result<Term>,
) -> Result<Term> {
    let mark = cx.mark();
    // In the empty row an effectful value is run in place, and then bound
    // as a pure one is.
    let (term, effectful) = match effectful.then(|| in_place(cx, row, &term, &ty)) {
        Some(found) => match found? {
            Some(value) => (value, false),
            None => (term, true),
        },
        None => (term, false),
    };
    if !effectful {
        // A pure `let` is a transparent one around the rest of the
        // computation (docs/proposals/let.md §5, option A).
        let ty_term = cx.quote(&ty)?;
        cx.define(Some(name), name.into(), ty, ty_term.clone(), term.clone())?;
        let result = body(cx);
        cx.reset(mark);
        return Ok(Term::let_(name.into(), ty_term, term, result?));
    }
    cx.bind(name, ty.clone());
    let result = body(cx);
    cx.reset(mark);
    let lam = Term::Lam(name.into(), Icit::Explicit, Rc::new(result?));
    call(
        cx,
        bind_name(row),
        &[ops(cx, row)?, res(cx, row)?, ty, t.clone()],
        vec![term, lam],
    )
}

/// A variable holding the result of an earlier computation.
struct Bound {
    name: String,
    /// The computation, or in the empty row `runPure` of it.
    comp: Term,
    ty: Value,
    mark: crate::check::Mark,
    /// In the empty row, the variable is a transparent `let` of `comp`, of
    /// this type, rather than a `bind`'s.
    in_place: Option<Term>,
}

/// Puts the result of `c`, a computation in `row` returning a `ty`, in
/// scope as `name`, for [`wrap`] to run first.
fn hold(cx: &mut Ctx, row: &Row, name: &str, c: Term, ty: Value) -> Result<Bound> {
    let mark = cx.mark();
    let (comp, in_place) = match in_place(cx, row, &c, &ty)? {
        Some(value) => {
            let ty_term = cx.quote(&ty)?;
            cx.define(
                Some(name),
                name.into(),
                ty.clone(),
                ty_term.clone(),
                value.clone(),
            )?;
            (value, Some(ty_term))
        }
        None => {
            cx.bind(name, ty.clone());
            (c, None)
        }
    };
    Ok(Bound {
        name: name.to_string(),
        comp,
        ty,
        mark,
        in_place,
    })
}

/// `runPure c`, for a computation `c` in the empty row, which is run where
/// it stands; `None` in any other row. A computation there can't perform
/// anything (an ability outside the row is refused when a call is lifted
/// into it, and `runPure`'s `Call` case is absurd), so running it in place
/// means what sequencing it with `bind` does, and what's built from its
/// result is an ordinary value: an equation about a handler's result is an
/// equation (docs/proposals/abilities.md, "Effectful calls at the empty
/// row").
fn in_place(cx: &Ctx, row: &Row, c: &Term, ty: &Value) -> Result<Option<Term>> {
    if !row.is_empty() {
        return Ok(None);
    }
    Ok(Some(call(
        cx,
        Builtin::RunPure,
        std::slice::from_ref(ty),
        vec![c.clone()],
    )?))
}

/// An application or variable that performs operations, as a computation
/// in `row`, with its result type.
pub fn comp_call(
    cx: &mut Ctx,
    expr: &Expr,
    row: &Row,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    if let Expr::Pipe(value, f) = expr {
        return pipe_call(cx, value, f, row, expected);
    }
    // `o.orAbort` with no arguments is a call that performs, not a field of
    // an effectful receiver: elaborated as calls are (SW-217).
    if let Expr::Field(recv, field) = expr
        && dot_performs(cx, recv, field, 0)?
    {
        let (term, ty, _) = comp_app(cx, expr, row, expected)?;
        return Ok((term, ty));
    }
    if let Expr::Binary(..)
    | Expr::Neg(..)
    | Expr::List(..)
    | Expr::Tuple(..)
    | Expr::Ann(..)
    | Expr::Record { .. }
    | Expr::CtorFields { .. }
    | Expr::Field(..) = expr
    {
        return comp_compound(cx, expr, row, expected);
    }
    let (term, ty, _) = comp_app(cx, expr, row, expected)?;
    Ok((term, ty))
}

/// An application or variable that performs operations (not a pipe or a
/// compound), as a computation in `row`, with its result type, and that
/// type as written when the final call is a pure one whose written result
/// type is known (for a `let`'s dot notation, docs/proposals/let.md §7).
fn comp_app(
    cx: &mut Ctx,
    expr: &Expr,
    row: &Row,
    expected: Option<&Value>,
) -> Result<(Term, Value, Option<crate::dot::Written>)> {
    let base = cx.level();
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a);
        head = f;
    }
    args.reverse();
    if let Expr::Var(name) = head
        && cx.lookup(&name.text).is_none()
        && cx.local(&name.text)?.is_none()
        && let Some((Global::Op(a, i), _)) = cx.e.named(&name.text).copied()
    {
        cx.e.note_name(name);
        let (term, ty) = op_call(cx, name, a, i, &args, row)?;
        return Ok((term, ty, None));
    }

    let mut bound: Vec<Bound> = Vec::new();
    // The head, then effectful arguments, run first, left to right, into
    // variables.
    let head = match head {
        Expr::Var(_) => head.clone(),
        // Dot notation: the receiver runs first, then the arguments as
        // written, whatever their places in the call (§4.8.2).
        Expr::Field(recv, field) => Expr::Field(
            Box::new(run_first(cx, recv, row, &mut bound)?),
            field.clone(),
        ),
        other => run_first(cx, other, row, &mut bound)?,
    };
    let mut owned: Vec<Expr> = Vec::new();
    for arg in &args {
        owned.push(match arg {
            Expr::NamedArg(name, value, span, bracket) => Expr::NamedArg(
                name.clone(),
                Box::new(run_first(cx, value, row, &mut bound)?),
                *span,
                *bracket,
            ),
            other => run_first(cx, other, row, &mut bound)?,
        });
    }

    // Apply the head one argument at a time: when a partial application is
    // already a computation (`k s s` with `k : s -> {e} (s -> {e} …)`), run
    // it and continue with its result.
    let (term, ty) = match &head {
        Expr::Var(_) => infer_head(cx, &head)?,
        // A call by dot notation is elaborated whole, receiver first.
        Expr::Field(recv, field) => {
            let call = {
                let args = crate::check::args_of(&owned);
                crate::dot::infer_dot(cx, recv, field, &args)?
            };
            owned.clear();
            call
        }
        other => infer(cx, other)?,
    };
    // Named arguments go to their parameters' places, now that what they
    // compute is in variables: they ran in written order, and the stages
    // run in parameter order (docs/proposals/named-arguments.md §4.5 R1,
    // R2). From the first parameter left out on, the call is a function of
    // the missing ones (R3).
    let written_args = crate::check::args_of(&owned);
    let head_ty = ty.clone();
    let (given, rest) = if crate::named::any(&written_args) {
        let sig = crate::named::signature(cx, &ty)?;
        let slots = crate::named::plan(cx, &sig, &written_args, None)?;
        let first = (slots.iter())
            .position(|s| matches!(s, crate::named::Slot::Missing(_)))
            .unwrap_or(slots.len());
        let given = crate::named::positional(&slots[..first]).expect("nothing missing before");
        (given, slots[first..].to_vec())
    } else {
        (written_args.clone(), Vec::new())
    };
    let snapshot = crate::undo::Snapshot::take(cx);
    let span = head.span();
    let apply = |cx: &mut Ctx,
                 bound: &mut Vec<Bound>,
                 mut term: Term,
                 mut ty: Value|
     -> Result<(Term, Value)> {
        // The value type the call returns is compared with the expected one
        // before the arguments are checked, as a pure call's is (SW-223).
        let mut given = &given[..];
        if rest.is_empty()
            && let Some(t) = expected
            && let Some(applied) =
                crate::check::propagate_comp(cx, &(term.clone(), ty.clone()), given, t)?
        {
            (term, ty) = applied;
            given = &[];
        }
        for arg in given {
            (term, ty) = run_stage(cx, row, bound, span, term, ty)?;
            (term, ty) = crate::check::apply_args(cx, (term, ty), std::slice::from_ref(arg))?;
        }
        if rest.is_empty() {
            return Ok((term, ty));
        }
        // The stages before the first parameter left out run now, once.
        (term, ty) = run_stage(cx, row, bound, span, term, ty)?;
        let explicit = rest
            .iter()
            .filter(|s| !matches!(s, crate::named::Slot::Given(crate::check::Arg::Named(..))))
            .count();
        if explicit > 1 && performs_after(cx, ty.clone(), explicit - 1)? {
            return Err(cx
                .error(
                    "E-EFFECT-ORDER",
                    "this call leaves out a parameter before a stage of the function",
                    "the function performs operations after taking the parameter left out",
                )
                .with_note(
                    "a stage after a parameter left out would run each time the function the \
                     call makes is called, which isn't supported yet: write the lambda, as in \
                     `y => f x y z`",
                ));
        }
        crate::named::apply_slots(cx, (term, ty), &rest)
    };
    let applied: Result<(Term, Value)> = apply(cx, &mut bound, term, ty);
    let (term, ty) = match applied {
        Ok(applied) => applied,
        Err(e) if crate::undo::fatal(&e) || !crate::named::any(&written_args) => return Err(e),
        Err(e) => {
            snapshot.restore(cx);
            let order = effect_order(cx, &head_ty, &written_args, &owned)?;
            return Err(order.unwrap_or(e));
        }
    };
    let (term, ty) = insert(cx, term, ty)?;
    let mut written = None;
    let (result, result_ty) = match comp_parts(cx, &ty)? {
        Some((from, t)) => (lift(cx, term, from, row, &t)?, t),
        None => {
            written = written_outside(cx, &term, base)?;
            (done(cx, row, &ty, term)?, ty)
        }
    };
    // Unknowns in the result type are solved from the expected type before
    // checking it doesn't depend on the variables bound here.
    if let Some(t) = expected
        && !cx.unify(&result_ty, t)?
    {
        let error = cx.mismatch(t, &result_ty);
        if let Some(first) = bound.first() {
            cx.reset(first.mark);
        }
        return Err(error);
    }
    let result = wrap(cx, row, bound, result, &result_ty)?;
    Ok((result, result_ty, written))
}

/// A partial application `term: ty` that is already a computation (`k s`
/// with `k : s -> {e} (s -> {e} …)`): run it, into a variable bound for
/// [`wrap`], and continue with its result. Anything else is returned as it
/// is.
fn run_stage(
    cx: &mut Ctx,
    row: &Row,
    bound: &mut Vec<Bound>,
    span: stitchwort_syntax::Span,
    term: Term,
    ty: Value,
) -> Result<(Term, Value)> {
    if !performs_after(cx, ty.clone(), 0)? {
        return Ok((term, ty));
    }
    let (t2, ty2) = insert(cx, term, ty)?;
    let (from, t) = comp_parts(cx, &ty2)?.expect("reached a computation type");
    let c = lift(cx, t2, from, row, &t)?;
    let name = format!("%{}", cx.level());
    bound.push(hold(cx, row, &name, c, t.clone())?);
    let var = Expr::Var(AstName { text: name, span });
    infer_head(cx, &var)
}

/// Why a named call that failed can't run its computations where they're
/// written (docs/proposals/named-arguments.md §4.5 R5, D1113): a
/// computation run first (into a variable, `written[i]` in `owned`) whose
/// type isn't settled yet, for a parameter whose type needs a parameter the
/// call leaves out, or one given by a computation written after it.
/// `head_ty` is the function's type; the state is as before the arguments
/// were applied.
fn effect_order(
    cx: &Ctx,
    head_ty: &Value,
    written: &[crate::check::Arg],
    owned: &[Expr],
) -> Result<Option<Diagnostic>> {
    let sig = crate::named::signature(cx, head_ty)?;
    let deps = crate::named::dependencies(cx, head_ty)?;
    let Some(filled) = crate::named::filled_by(cx, &sig, written) else {
        return Ok(None);
    };
    let Some(last) = filled.iter().rposition(Option::is_some) else {
        return Ok(None);
    };
    // The variable a computation was run into, by argument.
    let ran = |w: usize| -> Option<usize> {
        let value = match &owned[w] {
            Expr::NamedArg(_, value, ..) => &**value,
            other => other,
        };
        match value {
            Expr::Var(name) if name.text.starts_with('%') => cx.lookup(&name.text),
            _ => None,
        }
    };
    for (p, by) in filled.iter().enumerate() {
        let Some(w) = *by else { continue };
        let Some(level) = ran(w) else { continue };
        if !unsettled(cx, &cx.types[level])? {
            continue;
        }
        for &q in deps.get(p).map(|d| &d[..]).unwrap_or(&[]) {
            let needed = &sig.params[q].name;
            let later = match filled[q] {
                None if q < last && sig.params[q].icit == Icit::Explicit => None,
                Some(w2) if w2 > w && ran(w2).is_some() => Some(w2),
                _ => continue,
            };
            let span = value_span(&owned[w]);
            let mut d = Diagnostic::error(
                "E-EFFECT-ORDER",
                match later {
                    Some(_) => format!(
                        "this runs first, where it's written, but its type needs `{needed}`, \
                         which comes later"
                    ),
                    None => format!(
                        "this runs first, where it's written, but its type needs `{needed}`, \
                         which the call leaves out"
                    ),
                },
            )
            .with_label(span, format!("its type needs `{needed}`"));
            d = match later {
                Some(w2) => d
                    .with_label(
                        value_span(&owned[w2]),
                        format!("`{needed}` is computed here, after it"),
                    )
                    .with_note(format!(
                        "run them in the order you need, then call: `let {needed} := …` first, \
                         then pass `({needed} := {needed})`"
                    )),
                None => d.with_note(format!(
                    "give `{needed}` too: a computation in a call runs once, where it's \
                     written, so it can't wait for a parameter of the function the call makes"
                )),
            };
            return Ok(Some(d));
        }
    }
    Ok(None)
}

/// Where an argument's value is written: `e` in `(x := e)`.
fn value_span(arg: &Expr) -> stitchwort_syntax::Span {
    match arg {
        Expr::NamedArg(_, value, ..) => value.span(),
        other => other.span(),
    }
}

/// Whether `ty` mentions an unknown nothing has solved.
fn unsettled(cx: &Ctx, ty: &Value) -> Result<bool> {
    let term = cx.quote(ty)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    Ok(term.subterms().any(|(t, _)| match t {
        Term::Meta(m) => cx.g().meta_solution(*m).is_none(),
        _ => false,
    }))
}

/// `term`'s type as written (`dot::written_of`), unless it depends on a
/// variable bound at `base` or later (the results of operations run first,
/// which are gone once the call is wrapped).
fn written_outside(cx: &Ctx, term: &Term, base: usize) -> Result<Option<crate::dot::Written>> {
    let Some(written) = crate::dot::written_of(cx, term)? else {
        return Ok(None);
    };
    let crate::dot::Written::With(ty, env) = &written else {
        return Ok(None);
    };
    let inner = cx.level() - base;
    // Only the values the written type refers to matter.
    for (ix, v) in env.iter().rev().enumerate() {
        if !ty.mentions(ix) {
            continue;
        }
        let quoted = cx.quote(v)?;
        if (0..inner).any(|i| quoted.mentions(i)) {
            return Ok(None);
        }
    }
    Ok(Some(written))
}

/// `value |> f` that performs operations: `value` runs first, then the call
/// (docs/syntax.md). A lambda on the right is a `let`: `x |> y => body`
/// runs `x`, then `body` with `y` bound to its result.
fn pipe_call(
    cx: &mut Ctx,
    value: &Expr,
    f: &Expr,
    row: &Row,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let mut bound = Vec::new();
    let value = run_first(cx, value, row, &mut bound)?;
    let (result, ty) = match f {
        Expr::Lam(names, body, span) if names.len() == 1 => {
            let as_let = Expr::Let {
                name: names[0].clone(),
                ty: None,
                value: Box::new(value),
                body: body.clone(),
                span: *span,
            };
            comp_infer(cx, &as_let, row)?
        }
        Expr::TypedLam(name, ty, body, span) => {
            let as_let = Expr::Let {
                name: name.clone(),
                ty: Some(ty.clone()),
                value: Box::new(value),
                body: body.clone(),
                span: *span,
            };
            comp_infer(cx, &as_let, row)?
        }
        _ => {
            let pipe = Expr::Pipe(Box::new(value.clone()), Box::new(f.clone()));
            if may_perform(cx, &pipe)? {
                // The call performs operations: `f … value`, with `value`
                // already run.
                let call = Expr::App(Box::new(f.clone()), Box::new(value));
                comp_call(cx, &call, row, None)?
            } else {
                let (term, ty) = infer(cx, &pipe)?;
                let (term, ty) = insert(cx, term, ty)?;
                (done(cx, row, &ty, term)?, ty)
            }
        }
    };
    if let Some(t) = expected
        && !cx.unify(&ty, t)?
    {
        let error = cx.mismatch(t, &ty);
        if let Some(first) = bound.first() {
            cx.reset(first.mark);
        }
        return Err(error);
    }
    let result = wrap(cx, row, bound, result, &ty)?;
    Ok((result, ty))
}

/// Runs `e` first if it performs operations, binding its result to a fresh
/// variable, and returns what to use in its place.
fn run_first(cx: &mut Ctx, e: &Expr, row: &Row, bound: &mut Vec<Bound>) -> Result<Expr> {
    if !may_perform(cx, e)? {
        return Ok(e.clone());
    }
    let (c, ty) = comp_infer(cx, e, row)?;
    let name = format!("%{}", cx.level());
    bound.push(hold(cx, row, &name, c, ty)?);
    Ok(Expr::Var(AstName {
        text: name,
        span: e.span(),
    }))
}

/// Wraps `result : Comp row ty` in a `bind` for each of `bound` (run in
/// order). `ty` can't mention the variables bound.
fn wrap(cx: &mut Ctx, row: &Row, bound: Vec<Bound>, mut result: Term, ty: &Value) -> Result<Term> {
    let quoted = cx.quote(ty)?;
    if (0..bound.len()).any(|i| quoted.mentions(i)) {
        if let Some(first) = bound.first() {
            cx.reset(first.mark);
        }
        return Err(cx
            .error(
                "E-EFFECT-ESCAPE",
                "the result's type depends on the result of an operation",
                "here",
            )
            .with_note(
                "return the value together with what its type depends on, as a dependent pair",
            ));
    }
    for b in bound.into_iter().rev() {
        cx.reset(b.mark);
        if let Some(ty_term) = b.in_place {
            result = Term::let_(b.name.as_str().into(), ty_term, b.comp, result);
            continue;
        }
        let lam = Term::Lam(b.name.as_str().into(), Icit::Explicit, Rc::new(result));
        result = call(
            cx,
            bind_name(row),
            &[ops(cx, row)?, res(cx, row)?, b.ty, ty.clone()],
            vec![b.comp, lam],
        )?;
    }
    Ok(result)
}

/// `a + b`, `-a`, `[a, b]`, `(e : T)`, a record literal or update, or
/// `e.field`, when a part performs operations: the parts run first, left to
/// right. Arithmetic and comparisons run every effectful leaf of their group
/// first, however deeply it's nested, and are then typed as a whole
/// (docs/proposals/integers.md, "Effects and evaluation order"). A
/// record's base runs first, then its field expressions in the order written
/// (docs/proposals/records.md §6.1); the record is then built from their
/// results, at `expected` if given.
fn comp_compound(
    cx: &mut Ctx,
    expr: &Expr,
    row: &Row,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let mut bound = Vec::new();
    let pure = match expr {
        Expr::Record { base, fields, span } => {
            let base = match base {
                Some(b) => Some(Box::new(run_first(cx, b, row, &mut bound)?)),
                None => None,
            };
            let mut pure = Vec::new();
            for (name, value) in fields {
                pure.push((name.clone(), run_first(cx, value, row, &mut bound)?));
            }
            Expr::Record {
                base,
                fields: pure,
                span: *span,
            }
        }
        // `C { f = e, … }`: as a record literal, the fields run in the
        // order written (docs/proposals/variant-fields.md §4.5).
        Expr::CtorFields { ctor, fields, span } => {
            let mut pure = Vec::new();
            for (name, value) in fields {
                pure.push((name.clone(), run_first(cx, value, row, &mut bound)?));
            }
            Expr::CtorFields {
                ctor: ctor.clone(),
                fields: pure,
                span: *span,
            }
        }
        Expr::Field(e, name) => {
            Expr::Field(Box::new(run_first(cx, e, row, &mut bound)?), name.clone())
        }
        Expr::Binary(BinOp::Append, a, b) => {
            let a = run_first(cx, a, row, &mut bound)?;
            let b = run_first(cx, b, row, &mut bound)?;
            Expr::Binary(BinOp::Append, Box::new(a), Box::new(b))
        }
        Expr::Binary(op, a, b) if nested_effects(cx, a, b)? => {
            // As before groups where that works, so existing programs
            // elaborate to the same terms: each operand runs as a
            // computation of its own. Otherwise, as for `(1 + get ()) * i`
            // with an `Int` `i`, the whole group is typed at once.
            let before = |cx: &mut Ctx| -> Result<(Term, Value)> {
                let mut bound = Vec::new();
                let a = run_first(cx, a, row, &mut bound)?;
                let b = run_first(cx, b, row, &mut bound)?;
                let pure = Expr::Binary(*op, Box::new(a), Box::new(b));
                let (term, ty) = infer(cx, &pure)?;
                let (term, ty) = insert(cx, term, ty)?;
                if let Some(t) = expected
                    && !cx.unify(&ty, t)?
                {
                    return Err(cx.mismatch(t, &ty));
                }
                let result = done(cx, row, &ty, term)?;
                Ok((wrap(cx, row, bound, result, &ty)?, ty))
            };
            if let Some(found) = crate::numbers::attempt(cx, before)? {
                return Ok(found);
            }
            crate::numbers::map_leaves(cx, expr, &mut |cx, leaf| {
                run_first(cx, leaf, row, &mut bound)
            })?
        }
        Expr::Binary(..) | Expr::Neg(..) => {
            crate::numbers::map_leaves(cx, expr, &mut |cx, leaf| {
                run_first(cx, leaf, row, &mut bound)
            })?
        }
        Expr::Tuple(a, b, span) => {
            let a = run_first(cx, a, row, &mut bound)?;
            let b = run_first(cx, b, row, &mut bound)?;
            Expr::Tuple(Box::new(a), Box::new(b), *span)
        }
        Expr::List(items, span) => {
            let mut pure = Vec::new();
            for item in items {
                pure.push(run_first(cx, item, row, &mut bound)?);
            }
            Expr::List(pure, *span)
        }
        Expr::Ann(e, ty, _) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty = cx.eval(&ty)?;
            return Ok((comp_check(cx, e, row, &ty)?, ty));
        }
        _ => unreachable!("only called on compound expressions"),
    };
    let (term, ty) = match (expected, &pure) {
        (
            Some(t),
            Expr::Record { .. } | Expr::CtorFields { .. } | Expr::Tuple(..) | Expr::Neg(..),
        ) => (check(cx, &pure, t)?, t.clone()),
        (Some(t), Expr::Binary(op, ..)) if crate::numbers::is_arith(*op) => {
            (check(cx, &pure, t)?, t.clone())
        }
        _ => {
            let (term, ty) = infer(cx, &pure)?;
            insert(cx, term, ty)?
        }
    };
    let result = done(cx, row, &ty, term)?;
    Ok((wrap(cx, row, bound, result, &ty)?, ty))
}

/// Whether an operand of `a op b` is itself arithmetic (or a prefix `-`)
/// that performs operations: then running each operand as a computation of
/// its own, as before groups, differs from running the group's leaves first.
fn nested_effects(cx: &Ctx, a: &Expr, b: &Expr) -> Result<bool> {
    for side in [a, b] {
        let nested = match side {
            Expr::Binary(op, ..) => crate::numbers::is_arith(*op),
            Expr::Neg(..) => !crate::numbers::any_literal(side),
            _ => false,
        };
        if nested && may_perform(cx, side)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// `op arg`: a `Call` of the operation, injected into `row`.
fn op_call(
    cx: &mut Ctx,
    name: &AstName,
    a: usize,
    i: usize,
    args: &[&Expr],
    row: &Row,
) -> Result<(Term, Value)> {
    let info = &cx.e.abilities[a];
    let [arg] = args else {
        return Err(cx.error(
            "E-ARITY",
            format!("the operation `{}` takes one argument", name.text),
            format!("it's given {}", args.len()),
        ));
    };
    let mut row = refresh(cx, row)?;
    let pos = match row.position(a) {
        Some(pos) => pos,
        None => {
            // An unknown tail of the row can take the ability.
            let params = cx.g().data(info.op_data).params.len();
            let args = (0..params)
                .map(|_| {
                    let m = cx.fresh_meta();
                    cx.eval(&m)
                })
                .collect::<Result<_>>()?;
            let label = Label { ability: a, args };
            match extend(cx, &row, vec![label.clone()])? {
                Some(wider) => {
                    row = wider;
                    row.position(a).expect("just added")
                }
                None => return Err(not_allowed(cx, &label)),
            }
        }
    };
    let row = &row;
    let label = row.labels[pos].clone();
    let op_data = info.op_data;
    let field_ty = cx.g().data(op_data).ctors[i].fields[0].1.clone();
    let dom = stitchwort_core::value::eval(cx.g(), &label.args, &field_ty)?;

    let make = |cx: &mut Ctx, x: Term| make_call(cx, op_data, i, &label, pos, row, x);

    if !may_perform(cx, arg)? {
        let x = check(cx, arg, &dom)?;
        // The result type comes from the operation's `res`, which usually
        // looks only at which operation it is: `(%arg => op %arg) x`, so
        // that neither this nor the kernel's check of `Call`'s fields
        // computes `x` (docs/proposals/checker-evaluation.md, option (a)).
        let whole = |cx: &Ctx, ty: &Value| comp_type(cx, row, ty.clone());
        if let Some(found) = crate::bind::bind_argument(cx, "%arg", &dom, &x, make, whole)? {
            return Ok(found);
        }
        return make(cx, x);
    }
    // An effectful argument runs first.
    let c = comp_check(cx, arg, row, &dom)?;
    let mark = cx.mark();
    cx.bind("%op", dom.clone());
    let (inner, result_ty) = make(cx, Term::Var(0))?;
    if cx.quote(&result_ty)?.mentions(0) {
        cx.reset(mark);
        return Err(cx.error(
            "E-EFFECT-ESCAPE",
            "the result's type depends on the result of an operation",
            "here",
        ));
    }
    cx.reset(mark);
    let lam = Term::Lam("%op".into(), Icit::Explicit, Rc::new(inner));
    let bind = call(
        cx,
        bind_name(row),
        &[ops(cx, row)?, res(cx, row)?, dom, result_ty.clone()],
        vec![c, lam],
    )?;
    Ok((bind, result_ty))
}

/// `Call (op x) (r => Done r)`, with the operation injected at position
/// `pos` of `row`, and its result type.
fn make_call(
    cx: &mut Ctx,
    op_data: DataId,
    i: usize,
    label: &Label,
    pos: usize,
    row: &Row,
    x: Term,
) -> Result<(Term, Value)> {
    let x_value = cx.eval(&x)?;
    let op_value = Value::Ctor(op_data, i, [x_value].into());
    let result_ty = apply(cx.g(), label_res(cx, label)?, op_value)?;
    let plus = data(cx, Builtin::Plus)?;
    let mut injected = Term::ctor(plus, 0, vec![Term::ctor(op_data, i, vec![x])]);
    for _ in 0..pos {
        injected = Term::ctor(plus, 1, vec![injected]);
    }
    let comp = comp_type(cx, &row.total(), result_ty.clone())?;
    let comp_inner = stitchwort_core::value::quote(cx.g(), cx.level() + 1, &comp)?;
    let done = Term::Ann(
        Rc::new(Term::ctor(data(cx, Builtin::Comp)?, 0, vec![Term::Var(0)])),
        Rc::new(comp_inner),
    );
    let rest = Term::Lam("r".into(), Icit::Explicit, Rc::new(done));
    let op_call = Term::Ann(
        Rc::new(Term::ctor(
            data(cx, Builtin::Comp)?,
            1,
            vec![injected, rest],
        )),
        Rc::new(cx.quote(&comp)?),
    );
    if row.partial {
        let lifted = call(
            cx,
            Builtin::Lift,
            &[ops(cx, row)?, res(cx, row)?, result_ty.clone()],
            vec![op_call],
        )?;
        return Ok((lifted, result_ty));
    }
    Ok((op_call, result_ty))
}

/// An operation used as a value, `op`: the function `x => op x`, of type
/// `(x : A) -> {Ability args} B`.
pub fn op_value(cx: &mut Ctx, a: usize, i: usize) -> Result<(Term, Value)> {
    let op_data = cx.e.abilities[a].op_data;
    let params = cx.g().data(op_data).params.len();
    let args: Vec<Value> = (0..params)
        .map(|_| {
            let m = cx.fresh_meta();
            cx.eval(&m)
        })
        .collect::<Result<_>>()?;
    let label = Label { ability: a, args };
    let row = Row {
        labels: vec![label.clone()],
        tail: None,
        partial: false,
    };
    let field_ty = cx.g().data(op_data).ctors[i].fields[0].1.clone();
    let dom = stitchwort_core::value::eval(cx.g(), &label.args, &field_ty)?;
    let mark = cx.mark();
    cx.bind_hidden("x".into(), dom.clone());
    let result = make_call(cx, op_data, i, &label, 0, &row, Term::Var(0));
    let cod = result.and_then(|(call, b)| Ok((call, cx.quote(&comp_type(cx, &row, b)?)?)));
    cx.reset(mark);
    let (call, cod) = cod?;
    let ty = Term::Pi(
        "x".into(),
        Icit::Explicit,
        Rc::new(cx.quote(&dom)?),
        Rc::new(cod),
    );
    let ty = cx.eval(&ty)?;
    Ok((Term::Lam("x".into(), Icit::Explicit, Rc::new(call)), ty))
}

/// A `let` that performs nothing, in a pure context, checked against
/// `expected` or inferred: the kernel's transparent `Let(name, A, value,
/// body)`, so `body` knows `name` is `value` (docs/proposals/let.md, stage
/// 3). The rest of the block may still perform what it handles itself,
/// such as a call of an effectful function bound here; `check`/`infer` ask
/// again once `name` is in scope.
pub fn pure_let(
    cx: &mut Ctx,
    name: &AstName,
    ann: Option<&Expr>,
    value: &Expr,
    body: &Expr,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    // The variable's type as written, for dot notation: the annotation, or
    // the value's.
    let (term, ty, ty_term, written) = match ann {
        Some(ann) => {
            let (ty_term, _) = check_type(cx, ann)?;
            let written = crate::dot::Written::With(Rc::new(ty_term.clone()), cx.env.clone());
            let ty = cx.eval(&ty_term)?;
            (check(cx, value, &ty)?, ty, ty_term, Some(written))
        }
        None => {
            let (term, ty) = infer(cx, value)?;
            let (term, ty) = insert(cx, term, ty)?;
            let written = crate::dot::written_of(cx, &term)?;
            let ty_term = cx.quote(&ty)?;
            (term, ty, ty_term, written)
        }
    };
    let mark = cx.mark();
    let x: stitchwort_core::Name = name.text.as_str().into();
    let result = cx
        .define(
            Some(&name.text),
            x.clone(),
            ty,
            ty_term.clone(),
            term.clone(),
        )
        .and_then(|()| {
            if let Some(w) = written {
                cx.set_written(w);
            }
            // The body's type is computed with the name standing for the
            // value, so it never mentions the name: it's the block's type.
            match expected {
                Some(t) => check(cx, body, t).map(|b| (b, t.clone())),
                None => infer(cx, body),
            }
        });
    cx.reset(mark);
    let (body, block_ty) = result?;
    Ok((Term::let_(x, ty_term, term, body), block_ty))
}

/// Runs a computation that performs nothing, in a pure context.
pub fn run_pure(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    let empty = Row::empty();
    let (c, ty) = match expected {
        Some(t) => (comp_check(cx, expr, &empty, t)?, t.clone()),
        None => comp_infer(cx, expr, &empty)?,
    };
    // What ran in place is `let`s around a `Done v`: that's `v` under the
    // `let`s, with nothing left to run.
    if let Some(v) = done_value(cx, &c)? {
        return Ok((v, ty));
    }
    Ok((
        call(cx, Builtin::RunPure, std::slice::from_ref(&ty), vec![c])?,
        ty,
    ))
}

/// `v`, for a computation `Done v` (as [`done`] builds it in a total row)
/// under any `let`s, with the `let`s around it.
fn done_value(cx: &Ctx, c: &Term) -> Result<Option<Term>> {
    Ok(match c {
        Term::Let(x, a, v, b, e) => {
            done_value(cx, b)?.map(|b| Term::Let(x.clone(), a.clone(), v.clone(), Rc::new(b), *e))
        }
        Term::Loc(span, t) => done_value(cx, t)?.map(|t| Term::Loc(*span, Rc::new(t))),
        Term::Ann(inner, _) => match inner.strip_loc() {
            Term::Ctor(d, 0, fields) if *d == data(cx, Builtin::Comp)? && fields.len() == 1 => {
                Some(fields[0].as_ref().clone())
            }
            _ => None,
        },
        _ => None,
    })
}

// Handlers

/// `handle body with clauses`, as a computation in `out` returning a `t`.
fn handle(cx: &mut Ctx, body: &Expr, clauses: &[Clause], out: &Row, t: &Value) -> Result<Term> {
    let out = &refresh(cx, out)?;
    // Which ability, and the clauses for its operations.
    let mut ability = None;
    let mut ret = None;
    for clause in clauses {
        match clause {
            Clause::Return { var, body } => {
                if ret.is_some() {
                    return Err(cx.error("E-DUPLICATE", "two `return` clauses", "here"));
                }
                ret = Some((var, body));
            }
            Clause::Op { op, .. } => {
                cx.e.note_name(op);
                let found = cx.e.named(&op.text).copied();
                if let Some((Global::Unchecked(item), _)) = found {
                    return Err(cx.e.unchecked(op, item));
                }
                if let Some((Global::Failed, _)) = found {
                    return Err(crate::module::failed_name(op));
                }
                if let Some((Global::Pending(file, _), _)) = found {
                    return Err(cx.e.unloaded(op, file));
                }
                let Some((Global::Op(a, _), _)) = found else {
                    return Err(Diagnostic::error(
                        "E-ABILITY",
                        format!("`{}` isn't an operation", op.text),
                    )
                    .with_label(op.span, "a handler clause needs an operation"));
                };
                if ability.is_some_and(|b| b != a) {
                    return Err(
                        Diagnostic::error("E-ABILITY", "a handler handles one ability")
                            .with_label(op.span, "this operation is from a different ability"),
                    );
                }
                ability = Some(a);
            }
        }
    }
    let Some(a) = ability else {
        return Err(cx.error("E-ABILITY", "this handler has no operation clauses", "here"));
    };
    let Some((ret_var, ret_body)) = ret else {
        return Err(cx
            .error("E-HANDLER", "this handler has no `return` clause", "here")
            .with_note("add `| return x -> …` saying what to do with the result"));
    };
    let info = &cx.e.abilities[a];
    let (op_data, elim, op_names) = (info.op_data, info.elim, info.ops.clone());
    let mut op_clauses = Vec::new();
    for (i, name) in op_names.iter().enumerate() {
        // A clause names its operation as written: `get`, or `State.get`.
        let matching: Vec<_> = clauses
            .iter()
            .filter_map(|c| match c {
                Clause::Op { op, arg, k, body }
                    if matches!(cx.e.named(&op.text), Some((Global::Op(b, j), _)) if *b == a && *j == i) =>
                {
                    Some((op, arg, k, body))
                }
                _ => None,
            })
            .collect();
        match matching[..] {
            [one] => op_clauses.push(one),
            [] => {
                return Err(cx
                    .error(
                        "E-HANDLER",
                        format!("this handler has no clause for `{name}`"),
                        "here",
                    )
                    .with_note(
                        "a handler for an ability needs a clause for each of its operations",
                    ));
            }
            _ => {
                return Err(cx.error("E-DUPLICATE", format!("two clauses for `{name}`"), "here"));
            }
        }
    }

    // The handled computation's row: this ability first, then everything in
    // `out` except this ability.
    let params = cx.g().data(op_data).params.len();
    let args: Vec<Value> = (0..params)
        .map(|_| {
            let m = cx.fresh_meta();
            cx.eval(&m)
        })
        .collect::<Result<_>>()?;
    let handled = Label { ability: a, args };
    let rest = Row {
        labels: out
            .labels
            .iter()
            .filter(|l| l.ability != a)
            .cloned()
            .collect(),
        tail: out.tail.clone(),
        partial: false,
    };
    let mut inner_labels = vec![handled.clone()];
    inner_labels.extend(rest.labels.iter().cloned());
    // The handled computation is total even in a partial context: a
    // handler is a fold over a `Comp`, and there's nothing to fold in a
    // `Delay` (docs/proposals/partial.md §7.3.8).
    let inner = Row {
        labels: inner_labels,
        tail: rest.tail.clone(),
        partial: false,
    };
    let (body_c, t_in) = comp_infer(cx, body, &inner).map_err(|mut e| {
        if e.code == "E-PARTIAL" {
            e.notes.clear();
            e.with_note(
                "the computation a handler handles can't be `Partial`: a handler folds over \
                 every way a computation can go, which needs it to finish",
            )
        } else {
            e
        }
    })?;
    let r = comp_type(cx, out, t.clone())?;

    // return x -> …
    let mark = cx.mark();
    cx.bind(&ret_var.text, t_in.clone());
    let ret_term = comp_check(cx, ret_body, out, t);
    cx.reset(mark);
    let done_fn = Term::Lam(
        ret_var.text.as_str().into(),
        Icit::Explicit,
        Rc::new(ret_term?),
    );

    // op x => k -> …, for each operation in order.
    let mut elim_term = Term::Def(elim);
    for v in &handled.args {
        elim_term = Term::app_icit(elim_term, cx.quote(v)?, Icit::Implicit);
    }
    elim_term = Term::app_icit(elim_term, cx.quote(&r)?, Icit::Implicit);
    for (i, (_, arg, k, body)) in op_clauses.into_iter().enumerate() {
        let field_ty = cx.g().data(op_data).ctors[i].fields[0].1.clone();
        let dom = stitchwort_core::value::eval(cx.g(), &handled.args, &field_ty)?;
        let mark = cx.mark();
        let x_name = match arg {
            Pattern::Var(n) => n.text.clone(),
            Pattern::Wildcard(_) => "_".to_string(),
            Pattern::Absurd(_) => {
                let unit = Value::Data(data(cx, Builtin::UnitType)?, Vec::new());
                if !cx.unify(&dom, &unit)? {
                    cx.reset(mark);
                    return Err(cx.mismatch(&dom, &unit));
                }
                "_".to_string()
            }
            other => {
                return Err(Diagnostic::error(
                    "E-HANDLER",
                    "a clause's argument is a name, `_` or `()`",
                )
                .with_label(other.span(), "here"));
            }
        };
        let x_level = cx.level();
        cx.bind(&x_name, dom.clone());
        let op_value = Value::Ctor(op_data, i, [Value::var(x_level)].into());
        let b = apply(cx.g(), label_res(cx, &handled)?, op_value)?;
        let k_ty = Value::Pi(
            "y".into(),
            Icit::Explicit,
            Rc::new(b),
            stitchwort_core::value::Closure {
                env: cx.env.as_slice().into(),
                body: Rc::new(cx.quote(&r)?.shift(cx.g(), 1, 0)?),
            },
        );
        cx.bind(&k.text, k_ty);
        let body = comp_check(cx, body, out, t);
        cx.reset(mark);
        let clause = Term::Lam(
            x_name.as_str().into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                k.text.as_str().into(),
                Icit::Explicit,
                Rc::new(body?),
            )),
        );
        elim_term = Term::app(elim_term, clause);
    }

    // Everything else is forwarded to `out`, with the handler around the rest:
    // `o k => Call (sigInject m o) (y => k (sigReply m o y))`.
    // Elaborating the body may have added abilities to an unknown tail.
    let out = &refresh(cx, out)?;
    let rest = refresh(cx, &rest)?;
    let m = mapping(cx, &rest, out)?;
    let (rest_ops, rest_res, out_ops, out_res) = (
        ops(cx, &rest)?,
        res(cx, &rest)?,
        ops(cx, out)?,
        res(cx, out)?,
    );
    let forward = {
        let level = cx.level();
        let with_implicits = |b: Builtin, depth: usize| -> Result<Term> {
            let mut term = Term::Def(def(cx, b)?);
            for v in [&rest_ops, &rest_res, &out_ops, &out_res] {
                let v = stitchwort_core::value::quote(cx.g(), level + depth, v)?;
                term = Term::app_icit(term, v, Icit::Implicit);
            }
            Ok(term)
        };
        // Under `o` and `k`: `o` is Var(1). Under `y` as well: `o` is Var(2),
        // `k` is Var(1).
        let inject = Term::app(
            Term::app(
                with_implicits(Builtin::SigInject, 2)?,
                m.shift(cx.g(), 2, 0)?,
            ),
            Term::Var(1),
        );
        let reply = Term::app(
            Term::app(
                Term::app(
                    with_implicits(Builtin::SigReply, 3)?,
                    m.shift(cx.g(), 3, 0)?,
                ),
                Term::Var(2),
            ),
            Term::Var(0),
        );
        let rest_fn = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::app(Term::Var(1), reply)),
        );
        let call_term = if out.partial {
            // `bindD (lift (Call (sigInject m o) Done)) (\y -> k (…))`: the
            // carrier is a `Delay`, so the operation is performed, and then
            // the handler goes on.
            let quoted = |v: &Value| stitchwort_core::value::quote(cx.g(), level + 2, v);
            let ans = Term::app(quoted(&out_res)?, inject.clone());
            let done = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::ctor(data(cx, Builtin::Comp)?, 0, vec![Term::Var(0)])),
            );
            let op = Term::ctor(data(cx, Builtin::Comp)?, 1, vec![inject, done]);
            let mut lifted = Term::Def(primitive(cx, Primitive::Lift)?);
            let mut bind = Term::Def(primitive(cx, Primitive::BindD)?);
            for v in [quoted(&out_ops)?, quoted(&out_res)?, ans] {
                lifted = Term::app_icit(lifted, v.clone(), Icit::Implicit);
                bind = Term::app_icit(bind, v, Icit::Implicit);
            }
            bind = Term::app_icit(bind, quoted(t)?, Icit::Implicit);
            Term::app(Term::app(bind, Term::app(lifted, op)), rest_fn)
        } else {
            Term::ctor(data(cx, Builtin::Comp)?, 1, vec![inject, rest_fn])
        };
        Term::Lam(
            "o".into(),
            Icit::Explicit,
            Rc::new(Term::Lam("k".into(), Icit::Explicit, Rc::new(call_term))),
        )
    };
    let step = call(
        cx,
        Builtin::HandlePlus,
        &[
            label_ops(cx, &handled),
            rest_ops,
            label_res(cx, &handled)?,
            rest_res,
            r.clone(),
        ],
        vec![elim_term, forward],
    )?;
    call(
        cx,
        Builtin::FoldComp,
        &[ops(cx, &inner)?, res(cx, &inner)?, t_in, r],
        vec![done_fn, step, body_c],
    )
}

// Coercions between rows in a different order

/// Why `found` doesn't fit `expected`, when that's because of `Partial`
/// (docs/proposals/partial.md §7.3.4, §7.3.6): a recursive call of the group
/// being described where nothing can answer it, or a partial function where
/// a total one is expected.
pub fn partial_mismatch(
    cx: &mut Ctx,
    found: &Value,
    expected: &Value,
) -> Result<Option<Diagnostic>> {
    // While describing a partial group: a recursive call where nothing can
    // answer it (its type mentions the group's private request type).
    if let Some(rec) = &cx.e.recursion {
        let req = rec.req_data;
        let mentions = |t: &Term| {
            t.subterms()
                .any(|(t, _)| matches!(t, Term::Data(d, _) if *d == req))
        };
        if mentions(&cx.quote(found)?) && !mentions(&cx.quote(expected)?) {
            return Ok(Some(escape(cx)));
        }
    }
    // A partial function where a total one is expected.
    let g = cx.g();
    let mark = cx.mark();
    let (mut found, mut expected) = (found.clone(), expected.clone());
    let result = (|| -> Result<Option<Diagnostic>> {
        while let (Value::Pi(x, i1, d1, c1), Value::Pi(_, i2, _, c2)) =
            (force(g, found.clone())?, force(g, expected.clone())?)
        {
            if i1 != i2 {
                return Ok(None);
            }
            let v = Value::var(cx.level());
            cx.bind_hidden(x, (*d1).clone());
            found = c1.apply(g, v.clone())?;
            expected = c2.apply(g, v)?;
        }
        Ok(
            match (comp_parts(cx, &found)?, comp_parts(cx, &expected)?) {
                (Some((f, _)), Some((e, _))) if f.partial && !e.partial => Some(
                    cx.error(
                        "E-PARTIAL",
                        "a partial function can't be used where a total one is expected",
                        "this might not finish: its type says `Partial`",
                    )
                    .with_note(
                        "a function whose type doesn't say `Partial` must finish; a row variable \
                     like `e` never stands for `Partial`, so a function taking `{… | e}` can't \
                     be given a partial one",
                    )
                    .with_note(
                        "to accept partial functions, write `Partial` in the row: `{Partial | e}`",
                    ),
                ),
                _ => None,
            },
        )
    })();
    cx.reset(mark);
    result
}

/// If `found` and `expected` are both effectful function types, and
/// `found`'s abilities are among `expected`'s (after solving unknown tails)
/// though not in the same form, wraps `term` so it has the expected type:
/// `x … => translate m (term x …)` (or `mapSig`, or `lift` from a total
/// function to a partial one).
pub fn coerce(cx: &mut Ctx, term: &Term, found: &Value, expected: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let mark = cx.mark();
    let mut found = found.clone();
    let mut expected = expected.clone();
    let mut names: Vec<Name> = Vec::new();
    let result = (|| -> Result<Option<Term>> {
        while let (Value::Pi(x, Icit::Explicit, d1, c1), Value::Pi(_, Icit::Explicit, d2, c2)) =
            (force(g, found.clone())?, force(g, expected.clone())?)
        {
            if !cx.unify(&d1, &d2)? {
                return Ok(None);
            }
            let v = Value::var(cx.level());
            cx.bind_hidden(x.clone(), (*d1).clone());
            names.push(x);
            found = c1.apply(g, v.clone())?;
            expected = c2.apply(g, v)?;
        }
        let Some((re, te)) = comp_parts(cx, &expected)? else {
            return Ok(None);
        };
        let n = names.len();
        let mut applied = term.shift(cx.g(), n, 0)?;
        for i in (0..n).rev() {
            applied = Term::app(applied, Term::Var(i));
        }
        let Some((rf, tf)) = comp_parts(cx, &found)? else {
            // A pure function where an effectful one is expected: it
            // performs nothing, so it fits any row, as a lambda with a pure
            // body does: `x … => Done (term x …)` (SW-393). Only for a
            // function (a pure value isn't a computation here), and not
            // while its result type is still unknown: that might yet be a
            // computation.
            if n == 0
                || matches!(force(g, found.clone())?, Value::Neutral(Head::Meta(_), _))
                || !cx.unify(&found, &te)?
            {
                return Ok(None);
            }
            return Ok(Some(done(cx, &re, &te, applied)?));
        };
        // `lift` solves unknown tails on either side, and refuses abilities
        // that aren't allowed.
        if !cx.unify(&tf, &te)? {
            return Ok(None);
        }
        match lift(cx, applied, rf, &re, &tf) {
            Ok(term) => Ok(Some(term)),
            // Running out of resources isn't "doesn't fit".
            Err(e) if e.code == "E-RESOURCE" => Err(e),
            Err(_) => Ok(None),
        }
    })();
    cx.reset(mark);
    let Some(mut term) = result? else {
        return Ok(None);
    };
    for name in names.into_iter().rev() {
        term = Term::Lam(name, Icit::Explicit, Rc::new(term));
    }
    Ok(Some(term))
}
