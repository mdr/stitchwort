//! Dot notation by type (docs/proposals/namespaces.md §4.8): `e.f` is `T.f`
//! with `e` in the place of `T.f`'s first explicit parameter of type `T`,
//! where `T` is found from `e`'s type. A record's field is the special case
//! where `T.f` is its generated projection.
//!
//! The namespace comes from the **type-head view** of `e`'s type *as
//! written* (a term), not of its value, since evaluation unfolds nicknames
//! like `Price = Nat` at once: `p : Price` tries `Price.show` and then
//! `Nat.show`.

use std::rc::Rc;

use stitchwort_core::value::{Head, eval, force};
use stitchwort_core::{DataId, DefId, Globals, Icit, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Expr, Name as AstName, SECTION};

use crate::check::{Arg, Ctx, Result, apply_args, check, implicit_arg, infer, insert};
use crate::{Global, scope};

/// A variable's type as written.
#[derive(Clone, Debug)]
pub(crate) enum Written {
    /// A term in the context of the variables before the one it's the type
    /// of, whose values are read from the context where it's used (so a case
    /// branch's refinements apply).
    Here(Rc<Term>),
    /// A term with the values of its free variables (levels).
    With(Rc<Term>, Vec<Value>),
}

/// Where the type-head view has got to: a type as written, with the values
/// of its free variables, or a value (once a case tree has run, or where
/// nothing was written).
#[derive(Clone)]
enum Ty {
    Term(Rc<Term>, Vec<Value>),
    Value(Value),
}

/// A head the view can find a namespace from.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum TyHead {
    Data(DataId),
    /// A folded definition: a nickname, or an application of a type-level
    /// function.
    Def(DefId),
    /// The built-in equality, `x = y`: namespace `Eq`.
    Eq,
}

/// One step of the view.
enum Step {
    /// A namespace to try. For a definition, the type at this step, to
    /// unfold if the namespace has nothing.
    Head(TyHead, Option<Ty>),
    /// An unsolved metavariable.
    Unknown,
    /// No namespace: what the type is instead.
    Nothing(&'static str),
}

/// What a type is, without unfolding a definition at its head.
fn step(g: &Globals, ty: Ty) -> Result<Step> {
    let (term, env) = match ty {
        Ty::Value(v) => return step_value(g, v),
        Ty::Term(term, env) => (term, env),
    };
    let stripped = strip(&term);
    let (head, args) = stripped.spine();
    match head {
        Term::Data(d, _) if args.is_empty() => Ok(Step::Head(TyHead::Data(*d), None)),
        Term::Eq(..) if args.is_empty() => Ok(Step::Head(TyHead::Eq, None)),
        Term::Pi(..) if args.is_empty() => Ok(Step::Nothing("a function")),
        Term::Sort(_) if args.is_empty() => Ok(Step::Nothing("a type")),
        Term::Def(id) => Ok(Step::Head(TyHead::Def(*id), Some(Ty::Term(term, env)))),
        _ => step_value(g, eval(g, &env, &term)?),
    }
}

fn step_value(g: &Globals, value: Value) -> Result<Step> {
    Ok(match force(g, value)? {
        Value::Data(d, _) => Step::Head(TyHead::Data(d), None),
        Value::Eq(..) => Step::Head(TyHead::Eq, None),
        Value::Neutral(Head::Def(id), _) => Step::Head(TyHead::Def(id), None),
        Value::Neutral(Head::Meta(_), _) => Step::Unknown,
        Value::Neutral(Head::Var(_), _) => Step::Nothing("a type variable"),
        Value::Pi(..) => Step::Nothing("a function"),
        Value::Sort(_) => Step::Nothing("a type"),
        _ => Step::Nothing("not a type"),
    })
}

/// Unfolds the definition `id` at the head of `ty` once: by substituting
/// its arguments into its body if that's not a case tree, or else by
/// running it. `None` if it can't unfold (it's stuck, say on a variable).
fn unfold(g: &Globals, id: DefId, ty: Option<Ty>) -> Result<Option<Ty>> {
    let (term, env) = match ty {
        // A value is already as unfolded as evaluation could make it.
        None | Some(Ty::Value(_)) => return Ok(None),
        Some(Ty::Term(term, env)) => (term, env),
    };
    let stripped = strip(&term);
    let (_, args) = stripped.spine();
    let def = g.def(id);
    if let Some(body) = def.body()
        && def.arity == args.len()
    {
        let inner = Term::peel_lams_rc(body, def.arity);
        if !matches!(inner.strip_loc(), Term::Case(..) | Term::NumCase(..)) {
            let mut values = Vec::new();
            for arg in &args {
                values.push(eval(g, &env, arg)?);
            }
            return Ok(Some(Ty::Term(inner, values)));
        }
    }
    let value = force(g, eval(g, &env, &term)?)?;
    Ok(match &value {
        Value::Neutral(Head::Def(i), _) if *i == id => None,
        _ => Some(Ty::Value(value)),
    })
}

/// `term` without locations, annotations or a meaningless outer wrapper.
fn strip(term: &Rc<Term>) -> Rc<Term> {
    let mut t = term.clone();
    loop {
        match &*t {
            Term::Loc(_, inner) => t = inner.clone(),
            Term::Ann(inner, _) => t = inner.clone(),
            _ => return t,
        }
    }
}

/// Every head the view goes through, from `ty`: for finding a function's
/// receiver parameter. Stops at the first head with no namespace, or one
/// already seen.
fn heads(g: &Globals, mut ty: Ty) -> Result<Vec<TyHead>> {
    let mut out = Vec::new();
    loop {
        match step(g, ty)? {
            Step::Head(h, at) => {
                if out.contains(&h) {
                    return Ok(out);
                }
                out.push(h);
                match h {
                    TyHead::Def(id) => match unfold(g, id, at)? {
                        Some(next) => ty = next,
                        None => return Ok(out),
                    },
                    _ => return Ok(out),
                }
            }
            Step::Unknown | Step::Nothing(_) => return Ok(out),
        }
    }
}

/// The type `term` (elaborated here) was checked or inferred at, as
/// written, if that's known: an annotation, a variable's declared type, or
/// a function's declared result type, instantiated.
fn written_type(cx: &Ctx, term: &Term) -> Result<Option<Ty>> {
    let g = cx.g();
    let stripped = term.strip_loc();
    if let Term::Ann(_, ty) = stripped {
        return Ok(Some(Ty::Term(ty.clone(), cx.env.clone())));
    }
    let (head, args) = stripped.spine();
    let (mut ty, mut env) = match head {
        Term::Var(ix) => {
            let level = cx.level() - 1 - ix;
            match &cx.written[level] {
                Some(Written::Here(t)) => (t.clone(), cx.env[..level].to_vec()),
                Some(Written::With(t, env)) => (t.clone(), env.clone()),
                None => return Ok(None),
            }
        }
        Term::Def(id) => (Rc::new(g.def(*id).ty.clone()), Vec::new()),
        _ => return Ok(None),
    };
    for arg in args {
        let Term::Pi(_, _, _, cod) = ty.strip_loc() else {
            return Ok(None);
        };
        let cod = cod.clone();
        env.push(cx.eval(arg)?);
        ty = cod;
    }
    Ok(Some(Ty::Term(ty, env)))
}

/// What `term`'s type is as written, to record for a variable bound to it
/// (a `let`), if known.
pub(crate) fn written_of(cx: &Ctx, term: &Term) -> Result<Option<Written>> {
    Ok(match written_type(cx, term)? {
        Some(Ty::Term(t, env)) => Some(Written::With(t, env)),
        _ => None,
    })
}

/// The key of the namespace `h` stands for.
fn namespace(cx: &Ctx, h: TyHead) -> String {
    match h {
        TyHead::Data(d) => cx.e.data_key(d),
        TyHead::Def(id) => {
            let def = cx.g().def(id);
            if def.path.starts_with("Std.") {
                def.path.to_string()
            } else {
                def.name.to_string()
            }
        }
        TyHead::Eq => format!("{}.Eq", scope::STD),
    }
}

/// How to show the receiver in messages.
fn shown(recv: &Expr) -> String {
    match recv {
        Expr::Var(n) if n.text == SECTION => "the section's argument".to_string(),
        Expr::Field(e, f) if matches!(&**e, Expr::Var(n) if n.text == SECTION) => {
            format!("`.{}`", f.text)
        }
        Expr::Var(n) => format!("`{}`", n.text),
        Expr::Field(e, f) => match &**e {
            Expr::Var(n) => format!("`{}.{}`", n.text, f.text),
            _ => "the value".to_string(),
        },
        _ => "the value".to_string(),
    }
}

/// `recv.field args`: dot notation, or a field.
pub(crate) fn infer_dot(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    args: &[Arg],
) -> Result<(Term, Value)> {
    if let Some(id) = helper(cx, recv, field) {
        let head = (Term::Def(id), cx.g().def(id).ty_value.clone());
        return crate::check::apply_args(cx, head, args);
    }
    let (rterm, rty) = infer(cx, recv)?;
    let (rterm, rty) = insert(cx, rterm, rty)?;
    let start = written_type(cx, &rterm)?.unwrap_or_else(|| Ty::Value(rty.clone()));
    let (owner, f, key) = find(cx, recv, field, start)?;
    // The call's implicit arguments are made here, not by `apply_args`, so
    // its dictionaries are found here (`check::found_dictionaries`).
    let (term, ty) = call(cx, recv, field, owner, f, &key, rterm, rty, args)?;
    let own = crate::check::own_dictionaries(&term);
    Ok((term, crate::check::found_dictionaries(cx, &own, ty)?))
}

/// `f.go`, where `f` is a top-level definition (not a local variable) and
/// `go` one of its local definitions: that local definition, lifted
/// (docs/proposals/syntax-conveniences.md §3.6). This comes before dot
/// notation, which never finds a local definition.
pub(crate) fn helper(cx: &Ctx, recv: &Expr, field: &AstName) -> Option<DefId> {
    let key = format!("{}.{}", helper_owner(cx, recv)?, field.text);
    if !cx.e.helper_keys.contains(&key) {
        return None;
    }
    match cx.e.scope.get(&key) {
        Some((Global::Def(id), _)) => Some(id),
        _ => None,
    }
}

/// The key of the definition `recv` names, if it's a top-level definition or
/// a local definition named from outside (`f.go`, for `f.go.inner`).
fn helper_owner(cx: &Ctx, recv: &Expr) -> Option<String> {
    match recv {
        Expr::Var(name) => {
            if cx.lookup(&name.text).is_some() || matches!(cx.local(&name.text), Ok(Some(_))) {
                return None;
            }
            match cx.e.resolve(&name.text) {
                crate::scope::Resolved::Found {
                    global: Global::Def(_),
                    key,
                    rest,
                    ..
                } if rest.is_empty() => Some(key.to_string()),
                _ => None,
            }
        }
        Expr::Field(inner, field) => {
            let key = format!("{}.{}", helper_owner(cx, inner)?, field.text);
            cx.e.helper_keys.contains(&key).then_some(key)
        }
        _ => None,
    }
}

/// Finds `T.f` for the receiver's type `ty`: the first head in the view
/// whose namespace has an `f`.
fn find(cx: &Ctx, recv: &Expr, field: &AstName, mut ty: Ty) -> Result<(TyHead, DefId, String)> {
    let g = cx.g();
    let mut tried: Vec<TyHead> = Vec::new();
    loop {
        match step(g, ty)? {
            Step::Unknown if matches!(recv, Expr::Var(n) if n.text == SECTION) => {
                return Err(section_unknown_name(cx, field));
            }
            Step::Unknown => {
                return Err(cx
                    .error(
                        "E-CANNOT-INFER",
                        format!(
                            "can't tell what {} is, so can't look up `.{}`",
                            shown(recv),
                            field.text
                        ),
                        "its type isn't known yet here",
                    )
                    .with_note(format!(
                        "`.{}` is looked up in the namespace of the value's type, so that type \
                         must be known where it's used: annotate it, as in \
                         `(p: Person) => p.{}`, or write the function's full name",
                        field.text, field.text
                    )));
            }
            Step::Nothing(what) => {
                return Err(cx
                    .error(
                        "E-NO-NAMESPACE",
                        format!(
                            "{} is {what}, which has no namespace to look `.{}` up in",
                            shown(recv),
                            field.text
                        ),
                        format!("`.{}` needs a value of a named type", field.text),
                    )
                    .with_note(
                        "dot notation finds a function by the type of the value before the \
                         `.`: a data type, a record, a definition of a type, or an equality",
                    ));
            }
            Step::Head(h, at) => {
                if tried.contains(&h) {
                    return Err(blocked(cx, recv, field, &tried));
                }
                tried.push(h);
                let ns = namespace(cx, h);
                let key = format!("{ns}.{}", field.text);
                let shown_key = scope::display(&key).to_string();
                // A field of a dictionary is its record's own projection, not
                // the method of that name (docs/proposals/interfaces.md §5.1).
                if let TyHead::Data(d) = h
                    && let Some(info) = cx.e.interfaces.get(&d)
                    && let Some(i) = g.data(d).ctors[0]
                        .fields
                        .iter()
                        .position(|(n, _)| **n == *field.text)
                {
                    return Ok((h, info.projections[i], shown_key));
                }
                // A local definition is never found by dot notation (§3.6).
                let found = match cx.e.helper_keys.contains(&key) {
                    true => None,
                    false => cx.e.scope.get(&key),
                };
                match found {
                    Some((Global::Def(id), _)) => return Ok((h, id, shown_key)),
                    Some((Global::Unchecked(item), _)) => {
                        return Err(cx.e.unchecked(
                            &AstName {
                                text: shown_key,
                                span: field.span,
                            },
                            item,
                        ));
                    }
                    Some((Global::Failed, _)) => {
                        return Err(crate::module::failed_name(&AstName {
                            text: shown_key,
                            span: field.span,
                        }));
                    }
                    Some((Global::Pending(file, _), _)) => {
                        return Err(cx.e.unloaded(
                            &AstName {
                                text: shown_key,
                                span: field.span,
                            },
                            file,
                        ));
                    }
                    Some(_) => {
                        return Err(cx
                            .error(
                                "E-DOT-NO-RECEIVER",
                                format!("`{shown_key}` isn't a function to call with `.`"),
                                format!("`{shown_key}` is a constructor, type or operation"),
                            )
                            .with_note(format!("write it in full, `{shown_key} …`")));
                    }
                    None => {}
                }
                if let TyHead::Data(d) = h
                    && g.data(d).record
                    && g.data(d).ctors[0]
                        .fields
                        .iter()
                        .any(|(n, _)| **n == *field.text)
                {
                    return Err(cx.error(
                        "E-PROP-ELIM",
                        format!("can't take field `{}` out of a proof", field.text),
                        format!(
                            "`{}` is a proposition, and `{}` is data",
                            g.data(d).name,
                            field.text
                        ),
                    ));
                }
                match h {
                    TyHead::Def(id) => match unfold(g, id, at)? {
                        Some(next) => ty = next,
                        None => return Err(blocked(cx, recv, field, &tried)),
                    },
                    _ => return Err(unknown_member(cx, field, &tried)),
                }
            }
        }
    }
}

/// A method section whose argument's type isn't known: `let f := .drop 1`.
pub(crate) fn section_unknown(cx: &Ctx, section: &Expr) -> Diagnostic {
    let name = section.section_name().expect("a section");
    section_unknown_name(cx, name)
}

fn section_unknown_name(cx: &Ctx, field: &AstName) -> Diagnostic {
    cx.error(
        "E-CANNOT-INFER",
        format!("can't tell what `.{}` is applied to", field.text),
        "the type of the value this section takes isn't known here",
    )
    .with_note(format!(
        "`.{f} …` is `x => x.{f} …`, and `{f}` is looked up in the namespace of `x`'s \
         type, so that type must be known: pipe a value into it (`xs |> .{f} …`), pass it \
         where a function of a known type is expected, or annotate it, as in \
         `(.{f} …: List Nat -> List Nat)`",
        f = field.text
    ))
}

/// The namespaces tried, for messages: "`Price` or `Nat`".
fn tried_list(cx: &Ctx, tried: &[TyHead]) -> String {
    let names: Vec<String> = tried
        .iter()
        .map(|h| format!("`{}`", scope::display(&namespace(cx, *h))))
        .collect();
    names.join(" or ")
}

/// The view reached a definition that can't be unfolded further.
fn blocked(cx: &Ctx, recv: &Expr, field: &AstName, tried: &[TyHead]) -> Diagnostic {
    let last = tried.last().expect("a head was tried");
    cx.error(
        "E-NO-NAMESPACE",
        format!(
            "{}'s type has no `{}`, and can't be unfolded any further",
            shown(recv),
            field.text
        ),
        format!("looked in {}", tried_list(cx, tried)),
    )
    .with_note(format!(
        "`{}` is stuck: its definition can't take a step while what it's applied to is unknown",
        scope::display(&namespace(cx, *last))
    ))
}

/// `E-UNKNOWN-FIELD`: the type has no field or function `field`. Lists a
/// record's fields, and near misses among the namespace's functions.
fn unknown_member(cx: &Ctx, field: &AstName, tried: &[TyHead]) -> Diagnostic {
    let g = cx.g();
    let last = *tried.last().expect("a head was tried");
    let ns = namespace(cx, last);
    let mut d = Diagnostic::error(
        "E-UNKNOWN-FIELD",
        format!(
            "`{}` has no field or function `{}`",
            scope::display(&ns),
            field.text
        ),
    )
    .with_label(field.span, format!("looked in {}", tried_list(cx, tried)));
    let prefix = format!("{ns}.");
    let mut near: Vec<(usize, String)> = cx
        .e
        .scope
        .keys()
        .filter_map(|k| {
            let member = k.strip_prefix(&prefix)?;
            if member.contains('.') || member.starts_with('%') {
                return None;
            }
            let distance = scope::edit_distance(member, &field.text);
            (distance <= 2 && distance < field.text.len()).then(|| (distance, member.to_string()))
        })
        .collect();
    near.sort();
    if let Some((_, best)) = near.first() {
        d = d.with_note(format!("did you mean `{best}`?"));
    }
    if let TyHead::Data(dd) = last
        && g.data(dd).record
    {
        let fields: Vec<String> = g.data(dd).ctors[0]
            .fields
            .iter()
            .map(|(f, _)| format!("`{f}`"))
            .collect();
        d = d.with_note(if fields.is_empty() {
            "it has no fields".to_string()
        } else {
            format!("its fields are {}", fields.join(", "))
        });
    }
    d
}

/// A parameter of `T.f`, from its signature as written.
struct Param {
    icit: Icit,
    name: stitchwort_core::Name,
    /// Its type, in the context of the parameters before it.
    ty: Rc<Term>,
}

/// `T.f`'s parameters, as far as its signature as written spells them out.
fn params(g: &Globals, f: DefId) -> Vec<Param> {
    let mut out = Vec::new();
    let mut ty = g.def(f).ty.clone();
    while let Term::Pi(name, icit, dom, cod) = ty.strip_loc() {
        out.push(Param {
            icit: *icit,
            name: name.clone(),
            ty: dom.clone(),
        });
        let next = (**cod).clone();
        ty = next;
    }
    out
}

/// One argument of the call being built.
enum Piece {
    /// An implicit argument, made at this level.
    Implicit(Term, Icit, usize),
    Receiver,
    /// A written argument (its index), checked once the receiver has been.
    Written(usize),
    /// A parameter left out, bound at this level by the function the call
    /// becomes.
    Missing(usize),
}

/// `T.f` applied with the receiver in its place, the written arguments in
/// the other explicit parameters' places in order (§4.8 step 4).
#[allow(clippy::too_many_arguments)]
fn call(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    owner: TyHead,
    f: DefId,
    key: &str,
    rterm: Term,
    rty: Value,
    args: &[Arg],
) -> Result<(Term, Value)> {
    let g = cx.g();
    let mut written: Vec<&Expr> = Vec::new();
    for arg in args {
        match arg {
            Arg::Explicit(e) => written.push(*e),
            // `pipe.rs` applies the call to the value piped in.
            Arg::Piped(_) => unreachable!("not passed to dot notation"),
            Arg::Named(n, _) => {
                return Err(Diagnostic::error(
                    "E-ARITY",
                    "dot notation doesn't take named implicit arguments",
                )
                .with_label(n.span, "given here")
                .with_note(format!(
                    "write the call in full: `{key} … [{} := …]`",
                    n.text
                )));
            }
        }
    }
    // The receiver's place: the first explicit parameter whose type has
    // `owner` as a head.
    let params = params(g, f);
    let level = cx.level();
    let mut receiver = None;
    let mut explicit: usize = 0;
    for (depth, p) in params.iter().enumerate() {
        if p.icit != Icit::Explicit {
            continue;
        }
        let env: Vec<Value> = (0..depth).map(|k| Value::var(level + k)).collect();
        if heads(g, Ty::Term(p.ty.clone(), env))?.contains(&owner) {
            receiver = Some((depth, explicit));
            break;
        }
        explicit += 1;
    }
    let Some((recv_depth, k)) = receiver else {
        let shown_ty = cx.show(&g.def(f).ty_value);
        return Err(cx
            .error(
                "E-DOT-NO-RECEIVER",
                format!(
                    "`{key}` has no parameter of type `{}` to put {} in",
                    scope::display(&namespace(cx, owner)),
                    shown(recv)
                ),
                format!("`{key}: {shown_ty}`"),
            )
            .with_note(format!("call it directly, `{key} …`")));
    };
    // Explicit parameters before the receiver that no argument fills.
    let missing = k.saturating_sub(written.len());
    if missing > 0 {
        let mut explicit = 0;
        for (depth, p) in params[..recv_depth].iter().enumerate() {
            if p.icit != Icit::Explicit {
                continue;
            }
            if explicit >= written.len() && params[recv_depth].ty.mentions(recv_depth - 1 - depth) {
                let shown_ty = cx.show(&g.def(f).ty_value);
                return Err(cx
                    .error(
                        "E-DOT-PARTIAL",
                        format!(
                            "`.{}` leaves out `{}`, which the type of {} depends on",
                            field.text,
                            p.name,
                            shown(recv)
                        ),
                        format!("`{key}: {shown_ty}`"),
                    )
                    .with_note(format!(
                        "give `{}` after `.{}`, or write the call in full, `{key} …`: the function \
                         `.{}` would make can't take `{}` as an argument, since {} has one \
                         particular type",
                        p.name,
                        field.text,
                        field.text,
                        p.name,
                        shown(recv)
                    )));
            }
            explicit += 1;
        }
    }

    let base = cx.mark();
    let base_level = cx.level();
    // With parameters left out, the call becomes a function of them, and
    // the receiver is bound first so it's evaluated once:
    // `(r => x => T.f x r) e`.
    let recv_level = cx.level();
    // Otherwise the receiver's value is computed only if the result type
    // needs it (docs/proposals/checker-evaluation.md).
    let recv_value = if missing > 0 {
        cx.bind_hidden("%recv".into(), rty.clone());
        Some(Value::var(recv_level))
    } else {
        None
    };
    let mut pieces: Vec<Piece> = Vec::new();
    let mut placeholders: Vec<(Value, Value)> = Vec::new();
    let mut missing_doms: Vec<(stitchwort_core::Name, Value, usize)> = Vec::new();
    let mut ty = g.def(f).ty_value.clone();
    let mut seen = 0;
    loop {
        let Value::Pi(x, icit, dom, cod) = force(g, ty.clone())? else {
            unreachable!("the receiver's parameter is in the signature");
        };
        if icit.is_implicit() {
            let meta = implicit_arg(cx, icit, &dom);
            let value = cx.eval(&meta)?;
            pieces.push(Piece::Implicit(meta, icit, cx.level()));
            ty = cod.apply(g, value)?;
            continue;
        }
        if seen == k {
            if !cx.unify(&rty, &dom)? {
                let span = recv.span();
                return Err(Diagnostic::error(
                    "E-TYPE-MISMATCH",
                    format!("{} doesn't fit `{key}`'s parameter", shown(recv)),
                )
                .with_label(
                    span,
                    format!(
                        "`{key}` expects `{}` here, but this has type `{}`",
                        cx.show(&dom),
                        cx.show(&rty)
                    ),
                ));
            }
            pieces.push(Piece::Receiver);
            ty = match &recv_value {
                Some(var) => cod.apply(g, var.clone())?,
                None => cod.apply_lazy(g, || eval(g, &cx.env, &rterm))?,
            };
            break;
        }
        seen += 1;
        if pieces
            .iter()
            .filter(|p| matches!(p, Piece::Written(_)))
            .count()
            < written.len()
        {
            let i = placeholders.len();
            let meta = cx.fresh_meta();
            let value = cx.eval(&meta)?;
            placeholders.push(((*dom).clone(), value.clone()));
            pieces.push(Piece::Written(i));
            ty = cod.apply(g, value)?;
        } else {
            let at = cx.level();
            cx.bind_hidden(x.clone(), (*dom).clone());
            missing_doms.push((x.clone(), (*dom).clone(), at));
            pieces.push(Piece::Missing(at));
            ty = cod.apply(g, Value::var(at))?;
        }
    }
    // The written arguments, in parameter order, now that the receiver has
    // fixed what it can.
    let mut checked = Vec::new();
    for (arg, (dom, placeholder)) in written.iter().zip(&placeholders) {
        let term = check(cx, arg, dom)?;
        let value = cx.eval(&term)?;
        if !cx.unify(&value, placeholder)? {
            return Err(Diagnostic::error(
                "E-TYPE-MISMATCH",
                format!(
                    "this argument doesn't agree with the type of {}",
                    shown(recv)
                ),
            )
            .with_label(
                arg.span(),
                format!(
                    "{}'s type needs `{}` here, but this is `{}`",
                    shown(recv),
                    cx.show(placeholder),
                    cx.show(&value)
                ),
            ));
        }
        checked.push(term);
    }
    let here = cx.level();
    let mut term = Term::Def(f);
    for piece in pieces {
        term = match piece {
            Piece::Implicit(t, icit, at) => Term::app_icit(term, t.shift(g, here - at, 0)?, icit),
            Piece::Receiver if missing > 0 => Term::app(term, Term::Var(here - 1 - recv_level)),
            Piece::Receiver => Term::app(term, rterm.clone()),
            Piece::Written(i) => Term::app(term, checked[i].clone()),
            Piece::Missing(at) => Term::app(term, Term::Var(here - 1 - at)),
        };
    }
    if missing == 0 {
        let rest = &args[placeholders.len()..];
        return apply_args(cx, (term, ty), rest);
    }
    // `(r => x… => call) e`, annotated for the kernel.
    let mut fun_ty = cx.quote(&ty)?;
    for (x, dom, at) in missing_doms.iter().rev() {
        let dom = stitchwort_core::value::quote(g, *at, dom)?;
        fun_ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(dom), Rc::new(fun_ty));
        term = Term::Lam(x.clone(), Icit::Explicit, Rc::new(term));
    }
    cx.reset(base);
    debug_assert_eq!(cx.level(), base_level);
    let rty_term = cx.quote(&rty)?;
    let lam = Term::Lam("%recv".into(), Icit::Explicit, Rc::new(term));
    let lam_ty = Term::Pi(
        "%recv".into(),
        Icit::Explicit,
        Rc::new(rty_term),
        Rc::new(fun_ty.clone()),
    );
    let mut env = cx.env.clone();
    env.push(if fun_ty.mentions(0) {
        cx.eval(&rterm)?
    } else {
        stitchwort_core::value::unused()
    });
    let result_ty = eval(g, &env, &fun_ty)?;
    Ok((
        Term::app(Term::Ann(Rc::new(lam), Rc::new(lam_ty)), rterm),
        result_ty,
    ))
}

/// What `recv.field` calls, if that can be found without elaborating `recv`
/// (a variable, or a definition without implicit parameters): for deciding
/// whether a call performs operations before elaborating it.
pub(crate) fn target(cx: &Ctx, recv: &Expr, field: &AstName) -> Result<Option<DefId>> {
    let g = cx.g();
    let Expr::Var(name) = recv else {
        return Ok(None);
    };
    if helper(cx, recv, field).is_some() {
        return Ok(None);
    }
    if cx.local(&name.text)?.is_some() {
        return Ok(None);
    }
    let ty = if let Some(level) = cx.lookup(&name.text) {
        match &cx.written[level] {
            Some(Written::Here(t)) => Ty::Term(t.clone(), cx.env[..level].to_vec()),
            Some(Written::With(t, env)) => Ty::Term(t.clone(), env.clone()),
            None => Ty::Value(cx.types[level].clone()),
        }
    } else {
        match cx.e.named(&name.text) {
            Some((Global::Def(id), _)) if !matches!(&g.def(*id).ty_value, Value::Pi(_, i, _, _) if i.is_implicit()) => {
                Ty::Term(Rc::new(g.def(*id).ty.clone()), Vec::new())
            }
            _ => return Ok(None),
        }
    };
    Ok(find(cx, recv, field, ty).ok().map(|(_, id, _)| id))
}
