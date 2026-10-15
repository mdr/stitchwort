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

use stitchwort_core::value::{Head, apply, force};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Clause, Expr, Name as AstName, Pattern};

use crate::Global;
use crate::check::{Ctx, Result, check, check_if, check_type, infer, infer_head, insert};

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
    /// Where it's declared: the module (counting from the prelude) and its
    /// position there. Rows list abilities in this order, which is the
    /// source's, whatever order the declarations were checked in.
    pub order: (usize, usize),
}

/// A row: abilities (each at most once), then a tail.
#[derive(Clone)]
pub struct Row {
    pub labels: Vec<Label>,
    /// A row variable (a value of type `Sig`), or `None` for a closed row.
    pub tail: Option<Value>,
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
        }
    }

    fn suffix(&self, from: usize) -> Row {
        Row {
            labels: self.labels[from..].to_vec(),
            tail: self.tail.clone(),
        }
    }

    fn position(&self, ability: usize) -> Option<usize> {
        self.labels.iter().position(|l| l.ability == ability)
    }
}

// Prelude names

fn global(cx: &Ctx, name: &str) -> Result<Global> {
    match cx.e.names.get(name) {
        Some((g, _)) => Ok(*g),
        None => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("abilities need the prelude's `{name}`"),
            "here",
        )),
    }
}

fn data(cx: &Ctx, name: &str) -> Result<DataId> {
    match global(cx, name)? {
        Global::Data(d) => Ok(d),
        _ => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("`{name}` isn't a data type"),
            "here",
        )),
    }
}

fn def(cx: &Ctx, name: &str) -> Result<DefId> {
    match global(cx, name)? {
        Global::Def(id) => Ok(id),
        _ => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("`{name}` isn't a definition"),
            "here",
        )),
    }
}

/// `name [implicits…] explicits…`, quoting the implicit arguments.
fn call(cx: &Ctx, name: &str, implicits: &[Value], explicits: Vec<Term>) -> Result<Term> {
    let mut term = Term::Def(def(cx, name)?);
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
    Value::Data(cx.e.abilities[label.ability].op_data, label.args.clone())
}

fn label_res(cx: &Ctx, label: &Label) -> Result<Value> {
    let info = &cx.e.abilities[label.ability];
    let mut f = Value::Neutral(Head::Def(info.res), Vec::new());
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
            Value::Neutral(Head::Def(def(cx, "sigOp")?), Vec::new()),
            e.clone(),
        )?,
        None => Value::Data(data(cx, "NoOp")?, Vec::new()),
    };
    let plus = data(cx, "Plus")?;
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
            Value::Neutral(Head::Def(def(cx, "sigRes")?), Vec::new()),
            e.clone(),
        )?,
        None => Value::Neutral(Head::Def(def(cx, "NoRes")?), Vec::new()),
    };
    let plus_res = def(cx, "PlusRes")?;
    for (i, label) in row.labels.iter().enumerate().rev() {
        let rest_ops = ops(cx, &row.suffix(i + 1))?;
        let mut f = Value::Neutral(Head::Def(plus_res), Vec::new());
        f = stitchwort_core::value::apply_icit(g, f, label_ops(cx, label), Icit::Implicit)?;
        f = stitchwort_core::value::apply_icit(g, f, rest_ops, Icit::Implicit)?;
        f = apply(g, f, label_res(cx, label)?)?;
        value = apply(g, f, value)?;
    }
    Ok(value)
}

/// `Comp (ops row) (res row) t`.
pub fn comp_type(cx: &Ctx, row: &Row, t: Value) -> Result<Value> {
    Ok(Value::Data(
        data(cx, "Comp")?,
        vec![ops(cx, row)?, res(cx, row)?, t],
    ))
}

/// The row an operation type stands for, if it's built from abilities.
pub fn decode(cx: &Ctx, op_type: &Value) -> Result<Option<Row>> {
    let g = cx.g();
    let ability_of =
        |d: DataId| -> Option<usize> { cx.e.abilities.iter().position(|a| a.op_data == d) };
    let (Ok(plus), Ok(no_op), Ok(sig), Ok(sig_op)) = (
        data(cx, "Plus"),
        data(cx, "NoOp"),
        data(cx, "Sig"),
        def(cx, "sigOp"),
    ) else {
        return Ok(None);
    };
    let mut labels = Vec::new();
    let mut value = force(g, op_type.clone())?;
    loop {
        match value {
            Value::Data(d, args) if d == plus => {
                match force(g, args[0].clone())? {
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
            Value::Data(d, _) if d == no_op => return Ok(Some(Row { labels, tail: None })),
            Value::Neutral(Head::Def(id), spine) if id == sig_op && spine.len() == 1 => {
                let stitchwort_core::value::Elim::App(x, _) = &spine[0] else {
                    return Ok(None);
                };
                match force(g, x.clone())? {
                    Value::Ctor(d, 0, fields) if d == sig => value = force(g, fields[0].clone())?,
                    x => {
                        return Ok(Some(Row {
                            labels,
                            tail: Some(x),
                        }));
                    }
                }
            }
            _ => return Ok(None),
        }
    }
}

/// If `ty` is `Comp` over a row of abilities: the row and the result type.
pub fn comp_parts(cx: &Ctx, ty: &Value) -> Result<Option<(Row, Value)>> {
    let Ok(comp) = data(cx, "Comp") else {
        return Ok(None);
    };
    Ok(match force(cx.g(), ty.clone())? {
        Value::Data(d, args) if d == comp => {
            decode(cx, &args[0])?.map(|row| (row, args[2].clone()))
        }
        _ => None,
    })
}

fn ability_name(cx: &Ctx, label: &Label) -> String {
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
    };
    let sig = Value::Ctor(
        data(cx, "Sig")?,
        0,
        vec![ops(cx, &rest)?, res(cx, &rest)?].into(),
    );
    cx.unify(tail, &sig)
}

fn agree(cx: &mut Ctx, a: &Label, b: &Label) -> Result<()> {
    for (x, y) in a.args.iter().zip(&b.args) {
        if !cx.unify(x, y)? {
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

/// Moves `term : Comp from t` into `to`, solving an unknown tail of `from`.
fn lift(cx: &mut Ctx, term: Term, from: Row, to: &Row, t: &Value) -> Result<Term> {
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
    if same_shape(cx, &from, &to)? {
        return Ok(term);
    }
    let to = &to;
    let m = mapping(cx, &from, to)?;
    call(
        cx,
        "translate",
        &[
            ops(cx, &from)?,
            res(cx, &from)?,
            ops(cx, to)?,
            res(cx, to)?,
            t.clone(),
        ],
        vec![m, term],
    )
}

/// Re-reads a row whose tail may have been solved since it was read.
fn refresh(cx: &Ctx, row: &Row) -> Result<Row> {
    if row.tail.is_none() {
        return Ok(row.clone());
    }
    let ty = cx.eval(&cx.quote(&ops(cx, row)?)?)?;
    Ok(decode(cx, &ty)?.unwrap_or_else(|| row.clone()))
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
    };
    let sig = Value::Ctor(
        data(cx, "Sig")?,
        0,
        vec![ops(cx, &added)?, res(cx, &added)?].into(),
    );
    cx.unify(old, &sig)
}

/// A `SigMap` from row `from` into row `to`, whose abilities include all of
/// `from`'s (with the same tail, if `from` has one).
fn mapping(cx: &mut Ctx, from: &Row, to: &Row) -> Result<Term> {
    let mut m = match &from.tail {
        None => call(cx, "sigFromNo", &[ops(cx, to)?, res(cx, to)?], Vec::new())?,
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
            "sigCase",
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
            "sigRight",
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
            let id = call(cx, "sigId", &[ops(cx, to)?, res(cx, to)?], Vec::new())?;
            return Ok(id);
        }
        let tail = to.suffix(k);
        (right(k - 1)?, ops(cx, &tail)?, res(cx, &tail)?, k - 1)
    } else {
        let x = &to.labels[pos];
        let rest = to.suffix(pos + 1);
        let left = call(
            cx,
            "sigLeft",
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
            "sigCompose",
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
    for ability in &row.abilities {
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
    labels.sort_by_key(|l| cx.e.abilities[l.ability].order);
    let tail = match &row.tail {
        None => None,
        Some(name) => {
            let sig = Value::Data(data(cx, "Sig")?, Vec::new());
            let term = check(cx, &Expr::Var(name.clone()), &sig)?;
            Some(cx.eval(&term)?)
        }
    };
    let result_value = cx.eval(&result)?;
    let ty = comp_type(cx, &Row { labels, tail }, result_value)?;
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
    let found = cx.e.names.get(&name.text).copied();
    if let Some((Global::Unchecked(item), _)) = found {
        return Err(cx.e.unchecked(name, item));
    }
    if let Some((Global::Failed, _)) = found {
        return Err(crate::module::failed_name(name));
    }
    let Some((Global::Ability(a), _)) = found else {
        return Err(cx.error(
            "E-ABILITY",
            format!("`{}` isn't an ability", name.text),
            "rows list abilities, declared with `ability`",
        ));
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
/// an effectful function (with enough arguments), or contains `let`,
/// sequencing or `handle`. Lambda bodies don't count.
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
        Expr::Var(_) | Expr::App(..) => {
            let mut args = Vec::new();
            let mut head = expr;
            while let Expr::App(f, a) = head {
                args.push(a.as_ref());
                head = f;
            }
            if any(&mut args.iter().copied())? {
                return Ok(true);
            }
            let explicit = args
                .iter()
                .filter(|a| !matches!(a, Expr::NamedArg(..)))
                .count();
            match head {
                Expr::Var(name) => match head_type(cx, name) {
                    // An operation on its own is a function value.
                    HeadType::Op => explicit > 0,
                    HeadType::Typed(ty) => performs_after(cx, ty, explicit)?,
                    HeadType::Other => false,
                },
                other => may_perform(cx, other)?,
            }
        }
        Expr::Binary(_, a, b) => any(&mut [&**a, &**b].into_iter())?,
        Expr::Let { .. } | Expr::Seq(..) | Expr::Handle { .. } => true,
        Expr::If {
            cond,
            then,
            otherwise,
            ..
        } => any(&mut [&**cond, &**then, &**otherwise].into_iter())?,
        Expr::List(items, _) => any(&mut items.iter())?,
        Expr::Ann(e, _, _) | Expr::NamedArg(_, e, _) => may_perform(cx, e)?,
        _ => false,
    })
}

enum HeadType {
    Op,
    Typed(Value),
    Other,
}

fn head_type(cx: &Ctx, name: &AstName) -> HeadType {
    if let Some(level) = cx.lookup(&name.text) {
        return HeadType::Typed(cx.types[level].clone());
    }
    match cx.e.names.get(&name.text) {
        Some((Global::Op(..), _)) => HeadType::Op,
        Some((Global::Def(id), _)) => HeadType::Typed(cx.g().def(*id).ty_value.clone()),
        _ => HeadType::Other,
    }
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

/// `Done v`, as a computation in `row` returning a `t`.
fn done(cx: &Ctx, row: &Row, t: &Value, v: Term) -> Result<Term> {
    let ty = comp_type(cx, row, t.clone())?;
    Ok(Term::Ann(
        Rc::new(Term::ctor(data(cx, "Comp")?, 0, vec![v])),
        Rc::new(cx.quote(&ty)?),
    ))
}

/// Checks `expr` as a computation in `row` returning a `t`.
pub fn comp_check(cx: &mut Ctx, expr: &Expr, row: &Row, t: &Value) -> Result<Term> {
    cx.g().budget.nesting(crate::check::PASS)?;
    match expr {
        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            let (term, ty, effectful) = match ty {
                Some(ty) => {
                    let (ty, _) = check_type(cx, ty)?;
                    let ty = cx.eval(&ty)?;
                    if may_perform(cx, value)? {
                        (comp_check(cx, value, row, &ty)?, ty, true)
                    } else {
                        (check(cx, value, &ty)?, ty, false)
                    }
                }
                None if may_perform(cx, value)? => {
                    let (c, ty) = comp_infer(cx, value, row)?;
                    (c, ty, true)
                }
                None => {
                    let (term, ty) = infer(cx, value)?;
                    let (term, ty) = insert(cx, term, ty)?;
                    (term, ty, false)
                }
            };
            sequence(cx, row, t, &name.text, term, ty, effectful, |cx| {
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
            let expected = comp_type(cx, row, t.clone())?;
            if !may_perform(cx, cond)? {
                return check_if(cx, binder.as_ref(), cond, then, otherwise, &expected);
            }
            if binder.is_some() {
                return Err(cx.error(
                    "E-ABILITY",
                    "`if h : P` needs a proposition, which can't perform operations",
                    "here",
                ));
            }
            // Run the condition first, then branch on its result.
            let bool_ty = match cx.e.names.get("Bool") {
                Some((Global::Data(d), _)) => Value::Data(*d, Vec::new()),
                _ => {
                    return Err(cx.error(
                        "E-UNKNOWN-NAME",
                        "`if` needs the prelude's `Bool`",
                        "here",
                    ));
                }
            };
            let c = comp_check(cx, cond, row, &bool_ty)?;
            let var = Expr::Var(AstName {
                text: "%cond".into(),
                span: cond.span(),
            });
            sequence(cx, row, t, "%cond", c, bool_ty, true, |cx| {
                check_if(cx, None, &var, then, otherwise, &expected)
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

/// Elaborates `expr` as a computation in `row`, inferring its result type.
pub fn comp_infer(cx: &mut Ctx, expr: &Expr, row: &Row) -> Result<(Term, Value)> {
    cx.g().budget.nesting(crate::check::PASS)?;
    match expr {
        Expr::Let { .. } | Expr::Seq(..) | Expr::If { .. } | Expr::Handle { .. } => {
            let t = cx.fresh_meta();
            let t = cx.eval(&t)?;
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
    cx.bind(name, ty.clone());
    let result = body(cx);
    cx.reset(mark);
    let lam = Term::Lam(name.into(), Icit::Explicit, Rc::new(result?));
    if effectful {
        return call(
            cx,
            "bind",
            &[ops(cx, row)?, res(cx, row)?, ty, t.clone()],
            vec![term, lam],
        );
    }
    // A pure `let` is `(\name -> body) term`, annotated so the kernel can
    // check it.
    let comp = comp_type(cx, row, t.clone())?;
    let pi = Term::Pi(
        name.into(),
        Icit::Explicit,
        Rc::new(cx.quote(&ty)?),
        Rc::new(stitchwort_core::value::quote(
            cx.g(),
            cx.level() + 1,
            &comp,
        )?),
    );
    Ok(Term::app(Term::Ann(Rc::new(lam), Rc::new(pi)), term))
}

/// A variable holding the result of an earlier computation.
struct Bound {
    name: String,
    comp: Term,
    ty: Value,
    mark: crate::check::Mark,
}

/// An application or variable that performs operations, as a computation
/// in `row`, with its result type.
pub fn comp_call(
    cx: &mut Ctx,
    expr: &Expr,
    row: &Row,
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    if let Expr::Binary(..) | Expr::List(..) | Expr::Ann(..) = expr {
        return comp_compound(cx, expr, row);
    }
    let mut args: Vec<&Expr> = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a);
        head = f;
    }
    args.reverse();
    if let Expr::Var(name) = head
        && cx.lookup(&name.text).is_none()
        && let Some((Global::Op(a, i), _)) = cx.e.names.get(&name.text).copied()
    {
        return op_call(cx, name, a, i, &args, row);
    }

    let mut bound: Vec<Bound> = Vec::new();
    // The head, then effectful arguments, run first, left to right, into
    // variables.
    let head = match head {
        Expr::Var(_) => head.clone(),
        other => run_first(cx, other, row, &mut bound)?,
    };
    let mut owned: Vec<Expr> = Vec::new();
    for arg in &args {
        owned.push(match arg {
            Expr::NamedArg(name, value, span) => Expr::NamedArg(
                name.clone(),
                Box::new(run_first(cx, value, row, &mut bound)?),
                *span,
            ),
            other => run_first(cx, other, row, &mut bound)?,
        });
    }

    // Apply the head one argument at a time: when a partial application is
    // already a computation (`k s s` with `k : s -> {e} (s -> {e} …)`), run
    // it and continue with its result.
    let (mut term, mut ty) = match &head {
        Expr::Var(_) => infer_head(cx, &head)?,
        other => infer(cx, other)?,
    };
    for arg in &owned {
        if performs_after(cx, ty.clone(), 0)? {
            let (t2, ty2) = insert(cx, term, ty)?;
            let (from, t) = comp_parts(cx, &ty2)?.expect("reached a computation type");
            let c = lift(cx, t2, from, row, &t)?;
            let name = format!("%{}", cx.level());
            let mark = cx.mark();
            cx.bind(&name, t.clone());
            bound.push(Bound {
                name: name.clone(),
                comp: c,
                ty: t.clone(),
                mark,
            });
            let var = Expr::Var(AstName {
                text: name,
                span: head.span(),
            });
            (term, ty) = infer_head(cx, &var)?;
        }
        (term, ty) = crate::check::apply_one(cx, (term, ty), arg)?;
    }
    let (term, ty) = insert(cx, term, ty)?;
    let (result, result_ty) = match comp_parts(cx, &ty)? {
        Some((from, t)) => (lift(cx, term, from, row, &t)?, t),
        None => (done(cx, row, &ty, term)?, ty),
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
    Ok((result, result_ty))
}

/// Runs `e` first if it performs operations, binding its result to a fresh
/// variable, and returns what to use in its place.
fn run_first(cx: &mut Ctx, e: &Expr, row: &Row, bound: &mut Vec<Bound>) -> Result<Expr> {
    if !may_perform(cx, e)? {
        return Ok(e.clone());
    }
    let (c, ty) = comp_infer(cx, e, row)?;
    let name = format!("%{}", cx.level());
    let mark = cx.mark();
    cx.bind(&name, ty.clone());
    bound.push(Bound {
        name: name.clone(),
        comp: c,
        ty,
        mark,
    });
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
        let lam = Term::Lam(b.name.as_str().into(), Icit::Explicit, Rc::new(result));
        result = call(
            cx,
            "bind",
            &[ops(cx, row)?, res(cx, row)?, b.ty, ty.clone()],
            vec![b.comp, lam],
        )?;
    }
    Ok(result)
}

/// `a + b`, `[a, b]` or `(e : T)`, when a part performs operations: the
/// parts run first, left to right.
fn comp_compound(cx: &mut Ctx, expr: &Expr, row: &Row) -> Result<(Term, Value)> {
    let mut bound = Vec::new();
    let pure = match expr {
        Expr::Binary(op, a, b) => {
            let a = run_first(cx, a, row, &mut bound)?;
            let b = run_first(cx, b, row, &mut bound)?;
            Expr::Binary(*op, Box::new(a), Box::new(b))
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
    let (term, ty) = infer(cx, &pure)?;
    let (term, ty) = insert(cx, term, ty)?;
    let result = done(cx, row, &ty, term)?;
    Ok((wrap(cx, row, bound, result, &ty)?, ty))
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
        "bind",
        &[ops(cx, row)?, res(cx, row)?, dom, result_ty.clone()],
        vec![c, lam],
    )?;
    Ok((bind, result_ty))
}

/// `Call (op x) (\r -> Done r)`, with the operation injected at position
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
    let plus = data(cx, "Plus")?;
    let mut injected = Term::ctor(plus, 0, vec![Term::ctor(op_data, i, vec![x])]);
    for _ in 0..pos {
        injected = Term::ctor(plus, 1, vec![injected]);
    }
    let comp = comp_type(cx, row, result_ty.clone())?;
    let comp_inner = stitchwort_core::value::quote(cx.g(), cx.level() + 1, &comp)?;
    let done = Term::Ann(
        Rc::new(Term::ctor(data(cx, "Comp")?, 0, vec![Term::Var(0)])),
        Rc::new(comp_inner),
    );
    let rest = Term::Lam("r".into(), Icit::Explicit, Rc::new(done));
    let call = Term::Ann(
        Rc::new(Term::ctor(data(cx, "Comp")?, 1, vec![injected, rest])),
        Rc::new(cx.quote(&comp)?),
    );
    Ok((call, result_ty))
}

/// An operation used as a value, `op`: the function `\x -> op x`, of type
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

/// Runs a computation that performs nothing, in a pure context.
pub fn run_pure(cx: &mut Ctx, expr: &Expr, expected: Option<&Value>) -> Result<(Term, Value)> {
    let empty = Row::empty();
    let (c, ty) = match expected {
        Some(t) => (comp_check(cx, expr, &empty, t)?, t.clone()),
        None => comp_infer(cx, expr, &empty)?,
    };
    Ok((call(cx, "runPure", std::slice::from_ref(&ty), vec![c])?, ty))
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
                let found = cx.e.names.get(&op.text).copied();
                if let Some((Global::Unchecked(item), _)) = found {
                    return Err(cx.e.unchecked(op, item));
                }
                if let Some((Global::Failed, _)) = found {
                    return Err(crate::module::failed_name(op));
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
    for name in &op_names {
        let matching: Vec<_> = clauses
            .iter()
            .filter_map(|c| match c {
                Clause::Op { op, arg, k, body } if op.text == *name => Some((op, arg, k, body)),
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
    };
    let mut inner_labels = vec![handled.clone()];
    inner_labels.extend(rest.labels.iter().cloned());
    let inner = Row {
        labels: inner_labels,
        tail: rest.tail.clone(),
    };
    let (body_c, t_in) = comp_infer(cx, body, &inner)?;
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
                let unit = Value::Data(data(cx, "UnitType")?, Vec::new());
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
    // `\o k -> Call (sigInject m o) (\y -> k (sigReply m o y))`.
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
        let with_implicits = |name: &str, depth: usize| -> Result<Term> {
            let mut term = Term::Def(def(cx, name)?);
            for v in [&rest_ops, &rest_res, &out_ops, &out_res] {
                let v = stitchwort_core::value::quote(cx.g(), level + depth, v)?;
                term = Term::app_icit(term, v, Icit::Implicit);
            }
            Ok(term)
        };
        // Under `o` and `k`: `o` is Var(1). Under `y` as well: `o` is Var(2),
        // `k` is Var(1).
        let inject = Term::app(
            Term::app(with_implicits("sigInject", 2)?, m.shift(cx.g(), 2, 0)?),
            Term::Var(1),
        );
        let reply = Term::app(
            Term::app(
                Term::app(with_implicits("sigReply", 3)?, m.shift(cx.g(), 3, 0)?),
                Term::Var(2),
            ),
            Term::Var(0),
        );
        let rest_fn = Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::app(Term::Var(1), reply)),
        );
        let call_term = Term::ctor(data(cx, "Comp")?, 1, vec![inject, rest_fn]);
        Term::Lam(
            "o".into(),
            Icit::Explicit,
            Rc::new(Term::Lam("k".into(), Icit::Explicit, Rc::new(call_term))),
        )
    };
    let step = call(
        cx,
        "handlePlus",
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
        "foldComp",
        &[ops(cx, &inner)?, res(cx, &inner)?, t_in, r],
        vec![done_fn, step, body_c],
    )
}

// Coercions between rows in a different order

/// If `found` and `expected` are both effectful function types, and
/// `found`'s abilities are among `expected`'s (after solving unknown tails)
/// though not in the same form, wraps `term` so it has the expected type:
/// `\x … -> translate m (term x …)`.
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
        // `lift` solves unknown tails on either side, and refuses abilities
        // that aren't allowed.
        let (Some((rf, tf)), Some((re, te))) =
            (comp_parts(cx, &found)?, comp_parts(cx, &expected)?)
        else {
            return Ok(None);
        };
        if !cx.unify(&tf, &te)? {
            return Ok(None);
        }
        let n = names.len();
        let mut applied = term.shift(cx.g(), n, 0)?;
        for i in (0..n).rev() {
            applied = Term::app(applied, Term::Var(i));
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
