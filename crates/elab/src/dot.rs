//! Dot notation by type (docs/proposals/namespaces.md §4.8): `e.f a` is
//! `T.f e a`, with `e` as `T.f`'s first explicit argument (D303, "the value
//! goes first"), where `T` is found from `e`'s type. If that parameter isn't
//! a `T`, it's an error (D306), not a search for a later one. A record's field is the special case
//! where `T.f` is its generated projection.
//!
//! The namespace comes from the **type-head view** of `e`'s type *as
//! written* (a term), not of its value, since evaluation unfolds nicknames
//! like `Price = Nat` at once: `p : Price` tries `Price.show` and then
//! `Nat.show`. An inferred type keeps the nickname where it came from one
//! (a glued call), so `codes.map (code => code.f)` with `codes: List Code`
//! tries `Code.f` too.

use std::rc::Rc;

use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, eval, force, force_solved};
use stitchwort_core::{DataId, DefId, Globals, Icit, Term, Value};
use stitchwort_syntax::ast::{Bracket, Expr, Name as AstName, SECTION};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Arg, Ctx, Result, apply_args, implicit_arg, infer, insert};
use crate::named::Slot;
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
    /// An unsolved metavariable, at the type's head.
    Unknown(usize),
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
    // A glued call is a definition as written (`Code`, kept while gluing),
    // say an inferred type that came from one: try its namespace before
    // unfolding it.
    let value = force_solved(g, value)?;
    if let Value::Call(id, ..) = &value {
        return Ok(Step::Head(TyHead::Def(*id), Some(Ty::Value(value))));
    }
    Ok(match force(g, value)? {
        Value::Data(d, _) => Step::Head(TyHead::Data(d), None),
        Value::Eq(..) => Step::Head(TyHead::Eq, None),
        Value::Neutral(Head::Def(id), _) => Step::Head(TyHead::Def(id), None),
        Value::Neutral(Head::Meta(m), _) => Step::Unknown(m),
        Value::Neutral(Head::Var(_, _), _) => Step::Nothing("a type variable"),
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
        // A glued call unfolds by forcing.
        Some(Ty::Value(value @ Value::Call(..))) => return Ok(Some(Ty::Value(force(g, value)?))),
        // A value is already as unfolded as evaluation could make it.
        None | Some(Ty::Value(_)) => return Ok(None),
        Some(Ty::Term(term, env)) => (term, env),
    };
    let stripped = strip(&term);
    let (_, args) = stripped.spine();
    let def = g.def(id);
    // Not an opaque definition's hidden body
    // (docs/proposals/opaque-definitions.md §6.4).
    if let Some(body) = stitchwort_core::value::body_seen(g, id)
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
            Step::Unknown(_) | Step::Nothing(_) => return Ok(out),
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
        // An argument the rest of the type doesn't mention isn't evaluated:
        // evaluating a long chain of calls at every level is exponential.
        env.push(if cod.mentions(0) {
            cx.eval(arg)?
        } else {
            stitchwort_core::value::unused()
        });
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
        Expr::Var(n) if written(n) => format!("`{}`", n.text),
        Expr::Field(e, f) => match &**e {
            Expr::Var(n) if written(n) => format!("`{}.{}`", n.text, f.text),
            _ => "the value".to_string(),
        },
        _ => "the value".to_string(),
    }
}

/// Whether a variable is one the program wrote, not one elaboration made up
/// (`%N`, a value `|>` or an effect's stage bound, or a section's argument),
/// so that a message can show it.
fn written(name: &AstName) -> bool {
    !name.text.starts_with('%')
}

/// `recv.field args`: dot notation, or a field. Where the receiver's type
/// view meets an unknown before a namespace with `field`, the call waits
/// for it (K2).
pub(crate) fn infer_dot(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    args: &[Arg],
) -> Result<(Term, Value)> {
    match dot_or_block(cx, recv, field, args)? {
        Dotted::Done(term, ty) => Ok((term, ty)),
        Dotted::Blocked(blocked) => queue_call(cx, recv, field, args, Route::Dot, blocked),
    }
}

/// A dot call elaborated, or stopped where its receiver's type view met an
/// unknown.
enum Dotted {
    Done(Term, Value),
    Blocked(Box<Blocked>),
}

/// A dot call stopped at an unknown.
struct Blocked {
    /// The state before its receiver was elaborated.
    before: crate::undo::Snapshot,
    /// The unknown the view met.
    blocker: usize,
    /// The receiver, elaborated, with its implicit arguments inserted.
    receiver: (Term, Value),
    /// The error the call gives if it can't wait.
    error: Diagnostic,
}

/// [`infer_dot`], with a stop at an unknown left to the caller.
fn dot_or_block(cx: &mut Ctx, recv: &Expr, field: &AstName, args: &[Arg]) -> Result<Dotted> {
    if let Some(id) = helper(cx, recv, field) {
        cx.e.note_dot(field, id);
        let head = (Term::Def(id), crate::kernel::def_ty(cx.g(), id)?);
        let (term, ty) = crate::check::apply_args(cx, head, args)?;
        return Ok(Dotted::Done(term, ty));
    }
    let before = crate::undo::Snapshot::take(cx);
    let (rterm, rty) = infer_receiver(cx, recv, field)?;
    let (rterm, rty) = insert(cx, rterm, rty)?;
    Ok(
        match dot_on(cx, recv, field, args, rterm.clone(), rty.clone())? {
            Ok((term, ty)) => Dotted::Done(term, ty),
            Err((blocker, error)) => Dotted::Blocked(Box::new(Blocked {
                before,
                blocker,
                receiver: (rterm, rty),
                error,
            })),
        },
    )
}

/// The dot call once its receiver is elaborated: its term and type, or the
/// unknown its type view met and the error that is.
fn dot_on(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    args: &[Arg],
    rterm: Term,
    rty: Value,
) -> Result<std::result::Result<(Term, Value), (usize, Diagnostic)>> {
    let start = written_type(cx, &rterm)?.unwrap_or_else(|| Ty::Value(rty.clone()));
    let (owner, f, key) = match find_or_block(cx, recv, field, start)? {
        Lookup::Found(owner, f, key) => (owner, f, key),
        Lookup::Blocked(blocker, error) => return Ok(Err((blocker, error))),
    };
    cx.e.note_dot(field, f);
    note_left_out(cx, field, f, args)?;
    // A recursive call of a definition with `decreasing` passes its proof
    // by name, which only the prefix form takes.
    if cx.decreasing_rec(Some(f)).is_some() {
        return Err(cx.error(
            "E-DECREASING",
            format!(
                "write this recursive call as `{} …`, not with a dot",
                cx.g().def(f).name
            ),
            "a recursive call with `[decreasing := …]` is written in prefix form",
        ));
    }
    // The call's implicit arguments are made here, not by `apply_args`, so
    // its dictionaries are found here (`check::found_dictionaries`).
    let (term, ty) = call(cx, recv, field, owner, f, &key, rterm, rty, args)?;
    let own = crate::check::own_dictionaries(&term);
    Ok(Ok((term, crate::check::found_dictionaries(cx, &own, ty)?)))
}

/// Which entry a queued dot call came in by, so that it is resumed by the
/// same one: an elaboration without postponement would have taken it.
#[derive(Clone, Copy)]
enum Route {
    /// [`infer_call`]: the prefix form where it stands for the call.
    Call,
    /// [`infer_dot`] directly (a `|>` or an effectful call's head).
    Dot,
}

/// An argument of a queued dot call, as written.
#[derive(Clone)]
enum OwnedArg {
    Explicit(Expr),
    Named(AstName, Expr),
    NamedExplicit(AstName, Expr),
}

impl OwnedArg {
    fn of(arg: &Arg) -> Option<OwnedArg> {
        Some(match arg {
            Arg::Explicit(e) => OwnedArg::Explicit((*e).clone()),
            Arg::Named(n, e) => OwnedArg::Named((*n).clone(), (*e).clone()),
            Arg::NamedExplicit(n, e) => OwnedArg::NamedExplicit((*n).clone(), (*e).clone()),
            // Elaborated already: not syntax to keep.
            Arg::Piped(_) | Arg::Default(_) => return None,
        })
    }

    fn arg(&self) -> Arg<'_> {
        match self {
            OwnedArg::Explicit(e) => Arg::Explicit(e),
            OwnedArg::Named(n, e) => Arg::Named(n, e),
            OwnedArg::NamedExplicit(n, e) => Arg::NamedExplicit(n, e),
        }
    }
}

/// K2 (docs/proposals/postponement.md §5.2, §5.5): `recv.field args` whose
/// receiver's type view met an unknown, the blocker, queued until that is
/// solved. Its receiver is kept by the rule of §5.5 (invariant 6):
/// - the blocker was made before the receiver was elaborated (a lambda's
///   parameter, a `let`): the receiver is undone and kept as syntax, and
///   the call is resumed from the start, by the entry it came in by, so the
///   prefix form or the dot form is chosen then, as it would be without
///   postponement;
/// - the receiver made the blocker (a chained `.field`, a record literal
///   waiting, an application): undoing it would leave nothing to solve the
///   blocker, so its term is kept. It was inferred with no expected type, so
///   it is what it would be at resume; what reads its type (implicit
///   arguments, the view, the call) is done again at resume.
///
/// Resumed, it may meet another unknown further along its view: it waits
/// again, on that one (§5.7, T4's second measure).
struct DotCall {
    recv: Expr,
    field: AstName,
    args: Vec<OwnedArg>,
    route: Route,
    /// The receiver's term and type, if kept.
    kept: Option<(Term, Value)>,
    /// The call's type, as the placeholder has it.
    result: Value,
}

/// An unknown, to wait on.
fn on(blocker: usize) -> Value {
    Value::Neutral(Head::Meta(blocker), Default::default())
}

/// Queues the dot call `blocked` stopped (K2), by the receiver rule of
/// [`DotCall`]: the placeholder for it and its type. A call with an
/// argument elaborated already (piped in, or a default) doesn't wait: it is
/// the error it was.
fn queue_call(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    args: &[Arg],
    route: Route,
    blocked: Box<Blocked>,
) -> Result<(Term, Value)> {
    let Some(args) = args.iter().map(OwnedArg::of).collect::<Option<Vec<_>>>() else {
        return Err(blocked.error);
    };
    let kept = keep_receiver(cx, blocked.before, blocked.blocker, blocked.receiver);
    let meta = cx.fresh_meta();
    let result = cx.eval(&meta)?;
    let call = DotCall {
        recv: recv.clone(),
        field: field.clone(),
        args,
        route,
        kept,
        result: result.clone(),
    };
    let needs = on(blocked.blocker);
    let term = crate::queue::queue(cx, Rc::new(call), needs, result.clone(), blocked.error)?;
    Ok((term, result))
}

/// The receiver rule (§5.5): `None`, with the receiver undone, where the
/// blocker predates it; otherwise the receiver, kept.
fn keep_receiver(
    cx: &mut Ctx,
    before: crate::undo::Snapshot,
    blocker: usize,
    receiver: (Term, Value),
) -> Option<(Term, Value)> {
    if blocker < before.metas() {
        before.restore(cx);
        None
    } else {
        crate::queue::kept_receiver(cx, &before);
        Some(receiver)
    }
}

impl crate::queue::Check for DotCall {
    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let args: Vec<Arg> = self.args.iter().map(OwnedArg::arg).collect();
        let (recv, field) = (&self.recv, &self.field);
        let dotted = match &self.kept {
            None => match self.route {
                Route::Call => call_or_block(cx, recv, field, &args)?,
                Route::Dot => dot_or_block(cx, recv, field, &args)?,
            },
            Some((rterm, rty)) => {
                let before = crate::undo::Snapshot::take(cx);
                let (rterm, rty) = insert(cx, rterm.clone(), rty.clone())?;
                match dot_on(cx, recv, field, &args, rterm.clone(), rty.clone())? {
                    Ok((term, ty)) => Dotted::Done(term, ty),
                    Err((blocker, error)) => Dotted::Blocked(Box::new(Blocked {
                        before,
                        blocker,
                        receiver: (rterm, rty),
                        error,
                    })),
                }
            }
        };
        let (term, ty) = match dotted {
            Dotted::Done(term, ty) => (term, ty),
            // Further along the view, another unknown: wait on it, keeping
            // the receiver by the same rule. One that made this unknown now
            // (elaborated again from syntax, or given implicit arguments
            // here) is kept from now on, by a check that holds it.
            Dotted::Blocked(blocked) => {
                let needs = on(blocked.blocker);
                return Ok(
                    match keep_receiver(cx, blocked.before, blocked.blocker, blocked.receiver) {
                        None => crate::queue::Resumed::Waiting(needs),
                        Some(kept) => {
                            let call = DotCall {
                                recv: self.recv.clone(),
                                field: self.field.clone(),
                                args: self.args.clone(),
                                route: self.route,
                                kept: Some(kept),
                                result: self.result.clone(),
                            };
                            crate::queue::Resumed::WaitingAs(needs, Rc::new(call))
                        }
                    },
                );
            }
        };
        // Its implicit arguments, as an inferred term's are before it is
        // compared with what is expected of it, unless that takes them.
        let (term, ty) = match force(cx.g(), self.result.clone())? {
            Value::Neutral(Head::Meta(_), _) => (term, ty),
            Value::Pi(_, icit, ..) if icit.is_implicit() => (term, ty),
            _ => {
                let (term, ty) = insert(cx, term, ty)?;
                // None were inserted at the placeholder, so the item's own
                // term has them (invariant 8, §5.10's implicit arguments).
                debug_assert!(
                    !matches!(force(cx.g(), ty.clone()), Ok(Value::Pi(_, icit, ..)) if icit.is_implicit()),
                    "a resumed call kept an implicit parameter its place doesn't take (invariant 8)"
                );
                (term, ty)
            }
        };
        if !cx.unify(&ty, &self.result)? {
            return Err(cx.mismatch(&self.result, &ty));
        }
        Ok(crate::queue::Resumed::Done(term))
    }
}

/// For hover on `field`, a dot call of `f` with `args`: the defaults it
/// used.
fn note_left_out(cx: &Ctx, field: &AstName, f: DefId, args: &[Arg]) -> Result<()> {
    if cx.e.nav.is_some() && cx.g().def(f).param_defaults.is_some() {
        let head = (Term::Def(f), crate::kernel::def_ty(cx.g(), f)?);
        crate::defaults::note_left_out(cx, field.span, &head, args);
    }
    Ok(())
}

/// The receiver `recv` of `recv.field`, inferred: as a computation that's
/// passed, not run, when it goes to a parameter of computation type
/// (stage 0 of docs/proposals/effect-polymorphism.md).
fn infer_receiver(cx: &mut Ctx, recv: &Expr, field: &AstName) -> Result<(Term, Value)> {
    if crate::effects::receiver_passed(cx, recv, field)? {
        crate::check::infer_unrun(cx, recv)
    } else {
        infer(cx, recv)
    }
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

/// `T.f.update.g` where there's no such lemma: `T.f` is a definition (key
/// `owner`), so `.update` is part of a name, not dot notation.
fn no_update_lemma(cx: &Ctx, recv: &Expr, field: &AstName, owner: &str) -> Diagnostic {
    let shown_owner = scope::display(owner);
    let prefix = format!("{owner}.update.");
    let mut lemmas: Vec<String> =
        cx.e.helper_keys
            .iter()
            .filter(|k| k.starts_with(&prefix))
            .map(|k| format!("`{}`", scope::display(k)))
            .collect();
    lemmas.sort();
    let note = if lemmas.is_empty() {
        format!(
            "update lemmas `T.f.update.g` exist for each shared field `f` of a data type \
             that isn't a record, and `{shown_owner}` isn't one"
        )
    } else {
        format!(
            "the update lemmas for `{shown_owner}` are {}, one for each shared field holding \
             data whose type mentions no other field",
            lemmas.join(", ")
        )
    };
    let span = match recv {
        Expr::Var(n) => n.span.to(field.span),
        _ => field.span,
    };
    Diagnostic::error(
        "E-UNKNOWN-NAME",
        format!("unknown name `{shown_owner}.update…`"),
    )
    .with_label(span, "no such update lemma")
    .with_note(note)
}

/// What looking `.f` up in the type-head view found.
enum Lookup {
    /// `T.f`: the head, the function, and its name as shown.
    Found(TyHead, DefId, String),
    /// The view met an unknown at a type's head, the *blocker*, before any
    /// namespace with an `f`: the `.f` can wait on it (K2,
    /// docs/proposals/postponement.md §5.2), or else this is its error.
    Blocked(usize, Diagnostic),
}

/// Finds `T.f` for the receiver's type `ty`: the first head in the view
/// whose namespace has an `f`.
fn find(cx: &Ctx, recv: &Expr, field: &AstName, ty: Ty) -> Result<(TyHead, DefId, String)> {
    match find_or_block(cx, recv, field, ty)? {
        Lookup::Found(h, f, key) => Ok((h, f, key)),
        Lookup::Blocked(_, error) => Err(error),
    }
}

/// [`find`], or where the view met an unknown first, that unknown.
fn find_or_block(cx: &Ctx, recv: &Expr, field: &AstName, ty: Ty) -> Result<Lookup> {
    // `f.unfold` for an opaque `f` that has none, read as a field of `f`
    // (docs/proposals/opaque-definitions.md §6.3).
    if let Expr::Var(owner) = recv {
        let name = AstName {
            text: format!("{}.{}", owner.text, field.text),
            span: owner.span.to(field.span),
        };
        if let Some(d) = crate::opaque::no_unfold_equation(cx.e, &name) {
            return Err(d);
        }
    }
    let result = find_in_view(cx, recv, field, ty);
    if matches!(result, Ok(Lookup::Blocked(..)) | Err(_))
        && let Some(failed) = failed_receiver(cx, recv)
    {
        return Err(failed);
    }
    result
}

/// For `f.x` with `f` a definition that failed, which has no `.unfold` or
/// other helpers: the error that `f` has errors, which goes without saying
/// beside them.
fn failed_receiver(cx: &Ctx, recv: &Expr) -> Option<Diagnostic> {
    let Expr::Var(owner) = recv else {
        return None;
    };
    if cx.lookup(&owner.text).is_some() || matches!(cx.local(&owner.text), Ok(Some(_))) {
        return None;
    }
    match cx.e.resolve(&owner.text) {
        crate::scope::Resolved::Found {
            global: Global::Def(id),
            rest,
            ..
        } if rest.is_empty()
            && cx.g().def(id).state() == stitchwort_core::globals::State::Failed =>
        {
            Some(crate::module::failed_name(owner))
        }
        _ => None,
    }
}

/// [`find_or_block`], once `recv` isn't an opaque definition's missing
/// `.unfold`.
fn find_in_view(cx: &Ctx, recv: &Expr, field: &AstName, mut ty: Ty) -> Result<Lookup> {
    let g = cx.g();
    let receiver_ty = ty.clone();
    let mut tried: Vec<TyHead> = Vec::new();
    loop {
        match step(g, ty)? {
            // A section's argument whose type meets an unknown further along
            // its view (K3's sections wait before that, on the argument's
            // type itself): the `.field` waits, with the section's message.
            Step::Unknown(blocker) if matches!(recv, Expr::Var(n) if n.text == SECTION) => {
                return Ok(Lookup::Blocked(blocker, section_unknown(cx, field)));
            }
            Step::Unknown(blocker) => {
                let error = cx
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
                    ));
                return Ok(Lookup::Blocked(blocker, error));
            }
            Step::Nothing(_) if field.text == "update" && helper_owner(cx, recv).is_some() => {
                let owner = helper_owner(cx, recv).expect("just checked");
                return Err(no_update_lemma(cx, recv, field, &owner));
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
                    return Ok(Lookup::Found(h, info.projections[i], shown_key));
                }
                // A local definition is never found by dot notation (§3.6).
                let mut found = match cx.e.helper_keys.contains(&key) {
                    true => None,
                    false => cx.e.scope.get(&key),
                };
                let mut shown_key = shown_key;
                if found.is_none() {
                    match cx.e.visible_extension(&key) {
                        scope::Extension::Found(ext) => {
                            found = cx.e.scope.get(&ext);
                            shown_key = scope::display(&ext).to_string();
                        }
                        scope::Extension::Ambiguous(keys) => {
                            return Err(ambiguous_extension(cx, recv, field, &keys));
                        }
                        scope::Extension::Missing => {}
                    }
                }
                match found {
                    Some((Global::Def(id), _)) => return Ok(Lookup::Found(h, id, shown_key)),
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
                // A field some constructors have, that isn't shared
                // (docs/proposals/variant-fields.md §5.3).
                if let TyHead::Data(d) = h
                    && !g.data(d).record
                    && let Some((message, note)) =
                        cx.e.unshared_member(d, &field.text, &shown(recv))
                {
                    return Err(Diagnostic::error("E-UNKNOWN-FIELD", message)
                        .with_label(field.span, format!("looked in {}", tried_list(cx, &tried)))
                        .with_note(note));
                }
                match h {
                    TyHead::Def(id) => match unfold(g, id, at)? {
                        Some(next) => ty = next,
                        None => return Err(blocked(cx, recv, field, &tried)),
                    },
                    _ => return Err(unknown_member(cx, recv, field, &tried, receiver_ty)),
                }
            }
        }
    }
}

/// A method section `.f` checked against `dom -> cod`, where `T.f` takes one
/// explicit parameter (so the receiver, which goes first, is also last): the
/// function `T.f` itself, not the lambda `x => T.f x` (docs/proposals/
/// method-sections.md §5, D506), so `xs.any .snd` and `xs.any Pair.snd` are
/// the same term and a proof restating one with the other still matches.
/// `None` where the section stays a lambda: it has arguments, the
/// section has chained fields, its argument's type isn't known yet, or the
/// partial application doesn't fit the expected type.
pub(crate) fn section_partial(
    cx: &mut Ctx,
    section: &Expr,
    dom: &Value,
    expected: &Value,
) -> Result<Option<Term>> {
    let Expr::Lam(names, body, _) = section else {
        return Ok(None);
    };
    let Some(field) = section.section_name() else {
        return Ok(None);
    };
    // `.f a b`: the section's field applied to explicit arguments, nothing
    // else (not a chain such as `.name.length`).
    let (head, written) = crate::check::spine(body);
    let recv = Expr::Var(names[0].clone());
    let Expr::Field(r, name) = head else {
        return Ok(None);
    };
    if !matches!(&**r, Expr::Var(v) if v.text == SECTION) || name.text != field.text {
        return Ok(None);
    }
    let Ok((owner, f, _)) = find(cx, &recv, field, Ty::Value(dom.clone())) else {
        return Ok(None);
    };
    let g = cx.g();
    let all = params(g, f);
    let Some((depth, k)) = receiver_place(cx, &all, owner)? else {
        return Ok(None);
    };
    if all[depth + 1..].iter().any(|p| p.icit == Icit::Explicit) {
        return Ok(None);
    }
    // The arguments in their places, the receiver's last (named-arguments.md
    // §4.4): every explicit parameter before it must be given.
    let sig = crate::named::signature(cx, &g.def(f).ty_value)?;
    let Ok(slots) = crate::named::plan(cx, &sig, &written, Some(k)) else {
        return Ok(None);
    };
    if !matches!(slots.last(), Some(Slot::Receiver)) {
        return Ok(None);
    }
    let mut args: Vec<Arg> = Vec::new();
    for slot in &slots[..slots.len() - 1] {
        match slot {
            Slot::Given(arg) => args.push(*arg),
            _ => return Ok(None),
        }
    }
    let head = (Term::Def(f), crate::kernel::def_ty(g, f)?);
    let snapshot = crate::undo::Snapshot::take(cx);
    let attempt = (|| -> Result<Option<Term>> {
        let (term, ty) = apply_args(cx, head, &args)?;
        let (term, ty) = insert(cx, term, ty)?;
        Ok(cx.unify(&ty, expected)?.then_some(term))
    })();
    match attempt {
        Ok(Some(term)) => {
            cx.e.note_dot(field, f);
            Ok(Some(term))
        }
        Ok(None) => {
            snapshot.restore(cx);
            Ok(None)
        }
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => {
            snapshot.restore(cx);
            Ok(None)
        }
    }
}

/// K3 (docs/proposals/postponement.md §5.2, §5.4): a method section `.f …`
/// checked against `dom -> cod` with `dom` still an unknown, as in `let g :=
/// .drop 1` or `List.map .position ds`, waits on `dom` and is checked against
/// the function type once `dom`'s head is known, from its syntax. The
/// section is nothing but a dot call on its argument, so it has nothing to
/// elaborate before `dom` is known: like a record literal (K1), it keeps
/// nothing elaborated (invariant 6). Checked whole rather than as the lambda
/// `x => x.f …` with a `.f` waiting inside (the note's first reading of K3),
/// so that it is what it is when `dom` is known from the start: the partial
/// application `T.f a…` where the receiver comes last (D506), not the lambda
/// around it. A section whose argument's type is known but whose view meets
/// an unknown further on is a lambda with a `.f` waiting inside (K2),
/// carrying the section's message ([`find_in_view`]).
struct Section {
    section: Expr,
    /// The function type it is checked against, as the placeholder has it.
    expected: Value,
}

impl crate::queue::Check for Section {
    fn resume(&self, cx: &mut Ctx) -> Result<crate::queue::Resumed> {
        let term = crate::check::check(cx, &self.section, &self.expected)?;
        Ok(crate::queue::Resumed::Done(term))
    }
}

/// [`Section`]: `section` checked against `expected`, `dom -> cod`, queued
/// if `dom`'s head is an unknown, giving its placeholder; `None` otherwise.
pub(crate) fn queue_section(
    cx: &mut Ctx,
    section: &Expr,
    dom: &Value,
    expected: &Value,
) -> Result<Option<Term>> {
    let Value::Neutral(Head::Meta(blocker), _) = force(cx.g(), dom.clone())? else {
        return Ok(None);
    };
    let field = section.section_name().expect("a section");
    let check = Section {
        section: section.clone(),
        expected: expected.clone(),
    };
    let error = section_unknown(cx, field);
    let term = crate::queue::queue(cx, Rc::new(check), on(blocker), expected.clone(), error)?;
    Ok(Some(term))
}

/// A method section whose argument's type isn't known: `let f := .drop 1`
/// with nothing to say what `f` is applied to.
fn section_unknown(cx: &Ctx, field: &AstName) -> Diagnostic {
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

/// The namespaces tried, for messages: "`Price` or `Nat`". The types the
/// compiler writes for a computation's result (`CompD d e t` for `{e} t`)
/// are left out, unless nothing else was tried.
fn tried_list(cx: &Ctx, tried: &[TyHead]) -> String {
    let shown: Vec<TyHead> = tried
        .iter()
        .copied()
        .filter(|h| !is_computation_head(cx, *h))
        .collect();
    let shown = if shown.is_empty() { tried } else { &shown };
    let names: Vec<String> = shown
        .iter()
        .map(|h| format!("`{}`", scope::display(&namespace(cx, *h))))
        .collect();
    names.join(" or ")
}

/// Whether `h` is one of the definitions a computation's type is written
/// with: `CompIn`, `CompD` or `Delay`.
fn is_computation_head(cx: &Ctx, h: TyHead) -> bool {
    let TyHead::Def(id) = h else {
        return false;
    };
    let g = cx.g();
    [
        g.registry.def(Builtin::CompIn),
        g.registry.def(Builtin::CompD),
        g.builtins.primitive_id(Primitive::Delay),
    ]
    .contains(&Some(id))
}

/// `E-AMBIGUOUS`: two namespaces this file imports with `(..)` each add
/// `.field` to the receiver's type.
fn ambiguous_extension(cx: &Ctx, recv: &Expr, field: &AstName, keys: &[String]) -> Diagnostic {
    let shown_keys: Vec<String> = keys
        .iter()
        .map(|k| format!("`{}`", scope::display(k)))
        .collect();
    let call = match recv {
        Expr::Var(n) if written(n) => format!("`{}.{}`", n.text, field.text),
        _ => format!("`.{}`", field.text),
    };
    let example = match recv {
        Expr::Var(n) if written(n) => format!("`{} {} …`", scope::display(&keys[0]), n.text),
        _ => format!("`|> {} …`", scope::display(&keys[0])),
    };
    cx.error(
        "E-AMBIGUOUS",
        format!("{call} could mean {}", shown_keys.join(" or ")),
        "two imported namespaces add this function",
    )
    .with_note(format!(
        "both come in through `(..)` imports; write the one you mean in full, e.g. {example}"
    ))
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
fn unknown_member(
    cx: &Ctx,
    recv: &Expr,
    field: &AstName,
    tried: &[TyHead],
    receiver_ty: Ty,
) -> Diagnostic {
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
    // An extension in a namespace this file doesn't import.
    let hidden: Vec<String> = tried
        .iter()
        .flat_map(|h| {
            let target = format!("{}.{}", namespace(cx, *h), field.text);
            cx.e.hidden_extenders(&target)
                .into_iter()
                .map(move |ns| (ns, target.clone()))
        })
        .map(|(ns, target)| {
            let ty = target.rsplit_once('.').map_or(target.as_str(), |(t, _)| t);
            let owner = scope::short(ty);
            format!(
                "`{ns}` adds `{owner}.{}`; import it with `import {ns} (..)`",
                field.text
            )
        })
        .collect();
    if let Some(first) = hidden.first() {
        return d.with_note(first.clone());
    }
    if let Some((full, param_heads)) = elsewhere_taking(cx, field, tried) {
        let call = match recv {
            Expr::Var(n) if written(n) => format!("`{full} {} …`", n.text),
            _ => format!("`|> {full} …`"),
        };
        let alias = unmentioned_alias(cx, &param_heads, tried, receiver_ty);
        d = d.with_note(match alias {
            Some((alias, ty)) => format!(
                "{} has type `{ty}` here, which doesn't mention `{alias}`, so `.{}` was \
                 looked up in {}; `{full}` takes a `{alias}`: write {call}, or annotate \
                 the value as `{alias}` where it's made",
                shown(recv),
                field.text,
                tried_list(cx, tried)
            ),
            None => {
                let owner = scope::display(&ns);
                let owner = owner.rsplit('.').next().unwrap_or(owner);
                format!("`{full}` takes a `{owner}` first: write {call}")
            }
        });
    }
    if let Some(place) = in_scope_taking(cx, field, tried) {
        let owner = scope::display(&ns);
        let owner = owner.rsplit('.').next().unwrap_or(owner);
        let argument = match recv {
            Expr::Var(n) if written(n) => n.text.to_string(),
            _ => "…".to_string(),
        };
        let call = match place {
            None => format!("`{} {argument}`", field.text),
            Some(name) => format!("`{} …` with `{argument}` as its `{name}`", field.text),
        };
        d = d.with_note(format!(
            "`{}` is in scope but isn't in `{owner}`'s namespace: write {call}",
            field.text
        ));
    }
    d
}

/// A definition `U.field` in another namespace whose first explicit
/// parameter's type has one of `tried` as a head, so `x |> U.field` would
/// take the receiver: `Text.joinWith` for `.joinWith` on a `List`. The
/// first such name in order, as written in messages, with the heads of that
/// parameter's type.
fn elsewhere_taking(cx: &Ctx, field: &AstName, tried: &[TyHead]) -> Option<(String, Vec<TyHead>)> {
    let suffix = format!(".{}", field.text);
    let tried_namespaces: Vec<String> = tried.iter().map(|h| namespace(cx, *h)).collect();
    let g = cx.g();
    let level = cx.level();
    let mut found: Vec<(String, Vec<TyHead>)> =
        cx.e.scope
            .keys()
            .filter_map(|key| {
                let owner = key.strip_suffix(&suffix)?;
                if owner.contains('%')
                    || tried_namespaces.iter().any(|ns| ns == owner)
                    || cx.e.helper_keys.contains(key)
                {
                    return None;
                }
                let Some((Global::Def(f), _)) = cx.e.scope.get(key) else {
                    return None;
                };
                let all = params(g, f);
                let depth = all.iter().position(|p| p.icit == Icit::Explicit)?;
                let env: Vec<Value> = (0..depth).map(|j| Value::var(level + j)).collect();
                let hs = heads(g, Ty::Term(all[depth].ty.clone(), env)).ok()?;
                hs.iter()
                    .any(|h| tried.contains(h))
                    .then(|| (scope::display(key).to_string(), hs))
            })
            .collect();
    found.sort_by(|a, b| a.0.cmp(&b.0));
    found.dedup_by(|a, b| a.0 == b.0);
    found.into_iter().next()
}

/// When the function found elsewhere takes an alias (the first of
/// `param_heads` is a definition that unfolds to one of `tried`) and the
/// receiver's type doesn't mention it anywhere: the alias's name, and the
/// receiver's type as shown.
fn unmentioned_alias(
    cx: &Ctx,
    param_heads: &[TyHead],
    tried: &[TyHead],
    receiver_ty: Ty,
) -> Option<(String, String)> {
    let Some(&TyHead::Def(alias)) = param_heads.first() else {
        return None;
    };
    if tried.contains(&TyHead::Def(alias)) {
        return None;
    }
    let g = cx.g();
    let value = match receiver_ty {
        Ty::Value(value) => value,
        Ty::Term(term, env) => eval(g, &env, &term).ok()?,
    };
    let term = stitchwort_core::value::quote_folded(g, cx.level(), &value).ok()?;
    if term
        .subterms()
        .any(|(t, _)| matches!(t, Term::Def(id) if *id == alias))
    {
        return None;
    }
    let name = scope::display(&namespace(cx, TyHead::Def(alias))).to_string();
    let name = name.rsplit('.').next().unwrap_or(&name).to_string();
    Some((name, cx.show(&value)))
}

/// Whether the bare name `field` is a definition in scope (not a local
/// variable) with an explicit parameter whose type has one of `tried` as a
/// head, so that the plain call could take the receiver: `Some(None)` if
/// that's its first explicit parameter, else `Some` of the parameter's name.
fn in_scope_taking(cx: &Ctx, field: &AstName, tried: &[TyHead]) -> Option<Option<String>> {
    if cx.lookup(&field.text).is_some() {
        return None;
    }
    let scope::Resolved::Found {
        global: Global::Def(f),
        rest,
        ..
    } = cx.e.resolve(&field.text)
    else {
        return None;
    };
    // Not the definition being checked: the plain call would be recursion.
    let module = &cx.e.module;
    if !rest.is_empty()
        || (module.item.is_some() && module.def_items.get(&f) == module.item.as_ref())
    {
        return None;
    }
    let g = cx.g();
    let level = cx.level();
    let all = params(g, f);
    let explicit = all
        .iter()
        .enumerate()
        .filter(|(_, p)| p.icit == Icit::Explicit);
    for (k, (depth, p)) in explicit.enumerate() {
        let env: Vec<Value> = (0..depth).map(|j| Value::var(level + j)).collect();
        let takes = heads(g, Ty::Term(p.ty.clone(), env))
            .is_ok_and(|hs| hs.iter().any(|h| tried.contains(h)));
        if takes {
            return Some((k > 0).then(|| p.name.to_string()));
        }
    }
    None
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

/// The receiver's place among `params`: the first explicit parameter, as its
/// depth and its index among the explicit parameters (always 0), if its type
/// has `owner` as a head (D303, D306). Nothing searches for a later one.
fn receiver_place(cx: &Ctx, params: &[Param], owner: TyHead) -> Result<Option<(usize, usize)>> {
    let Some(depth) = params.iter().position(|p| p.icit == Icit::Explicit) else {
        return Ok(None);
    };
    let level = cx.level();
    let env: Vec<Value> = (0..depth).map(|k| Value::var(level + k)).collect();
    let fits = heads(cx.g(), Ty::Term(params[depth].ty.clone(), env))?.contains(&owner);
    Ok(fits.then_some((depth, 0)))
}

/// `W-RECEIVER-NOT-FIRST` (D307): the definition `f`, in the namespace of a
/// type `T`, takes an explicit `T`, but not as its first explicit
/// parameter, so neither `x.f` nor `x |> T.f` can pass it one. `None` if
/// it's not in a type's namespace, takes no `T`, or takes one first.
pub(crate) fn receiver_not_first(cx: &Ctx, f: DefId, span: Span) -> Result<Option<Diagnostic>> {
    let g = cx.g();
    // The key the namespace lookup uses, as `namespace` gives it: the path
    // in the library, the scope key elsewhere (`Meter.scale`, not
    // `Main.Meter.scale`).
    let def = g.def(f);
    let path = if def.path.starts_with("Std.") {
        def.path.to_string()
    } else {
        def.name.to_string()
    };
    // An extension is looked up in the namespace of the type it extends.
    let target = cx.e.scope.extended(&path).unwrap_or(&path);
    let Some((owner_key, name)) = target.rsplit_once('.') else {
        return Ok(None);
    };
    // A generated definition (`IO.%elim`) isn't written by anyone.
    if name.starts_with('%') {
        return Ok(None);
    }
    let params = params(g, f);
    let level = cx.level();
    let mut first = true;
    for (depth, p) in params.iter().enumerate() {
        if p.icit != Icit::Explicit {
            continue;
        }
        let env: Vec<Value> = (0..depth).map(|k| Value::var(level + k)).collect();
        let found = heads(g, Ty::Term(p.ty.clone(), env))?
            .into_iter()
            .any(|h| scope::display(&namespace(cx, h)) == scope::display(owner_key));
        if found && first {
            return Ok(None);
        }
        if found {
            let ns = scope::display(owner_key)
                .rsplit('.')
                .next()
                .unwrap_or(owner_key)
                .to_string();
            let shown = scope::display(&path).to_string();
            let var = ns
                .chars()
                .next()
                .map(|c| c.to_lowercase().to_string())
                .unwrap_or_default();
            return Ok(Some(
                Diagnostic::warning(
                    "W-RECEIVER-NOT-FIRST",
                    format!(
                        "`{shown}` takes a `{ns}` but not as its first parameter, so \
                         `{var}.{name}` and `{var} |> {shown}` won't work"
                    ),
                )
                .with_label(
                    span,
                    match &*p.name {
                        "_" | "" => format!("its `{ns}` comes after another parameter"),
                        name => format!("`{name}: {ns}` comes after another parameter"),
                    },
                )
                .with_note(format!(
                    "put the main value first{}, then the other arguments, then any \
                     functions; or, for a helper not meant to be called with `.` or `|>`, \
                     mark it `@[noReceiver]`",
                    match &*p.name {
                        "_" | "" => String::new(),
                        name => format!(" (`{name}`)"),
                    }
                )),
            ));
        }
        first = false;
    }
    Ok(None)
}

/// A function and the arguments it is applied to.
type PrefixForm<'a> = ((Term, Value), Vec<Arg<'a>>);

/// `recv.field args` checked against an expected type (SW-129): the call as
/// the prefix form `T.field recv a…`, so it's elaborated exactly as that
/// is, with the result compared with the expected type before `recv` is
/// checked in its parameter's place. Dot notation needs `recv`'s type only
/// for the head that names the namespace, so `recv` is inferred once here to
/// find it, and that is undone. `None` where the prefix form can't stand for
/// the call: a local definition's helper, named or piped arguments, or a
/// function whose first explicit parameter isn't the receiver's (an error
/// `call` reports).
pub(crate) fn prefix_form<'a>(
    cx: &mut Ctx,
    recv: &'a Expr,
    field: &AstName,
    args: &[Arg<'a>],
) -> Result<Option<PrefixForm<'a>>> {
    if helper(cx, recv, field).is_some() {
        return Ok(None);
    }
    let mut written: Vec<&'a Expr> = Vec::new();
    for arg in args {
        match arg {
            Arg::Explicit(e) => written.push(*e),
            // Put in place below, once the function is known.
            Arg::Named(..) | Arg::NamedExplicit(..) => {}
            Arg::Piped(_) | Arg::Default(_) => return Ok(None),
        }
    }
    let key = call_key(cx, recv, field);
    let cached = cx.e.dot_heads.borrow().get(&key).copied();
    let (owner, f) = if let Some(found) = cached {
        found
    } else {
        let snapshot = crate::undo::Snapshot::take(cx);
        let found = (|| -> Result<(TyHead, DefId)> {
            let (rterm, rty) = infer_receiver(cx, recv, field)?;
            let (rterm, rty) = insert(cx, rterm, rty)?;
            let start = written_type(cx, &rterm)?.unwrap_or_else(|| Ty::Value(rty.clone()));
            let (owner, f, _) = find(cx, recv, field, start)?;
            Ok((owner, f))
        })();
        snapshot.restore(cx);
        match found {
            Ok(found) => {
                cx.e.dot_heads.borrow_mut().insert(key, found);
                found
            }
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(_) => {
                mark_failed(cx, key);
                return Ok(None);
            }
        }
    };
    let g = cx.g();
    if receiver_place(cx, &params(g, f), owner)?.is_none() {
        return Ok(None);
    }
    // A recursive call of a definition with `decreasing`: its stand-in
    // takes the proof by name, `[decreasing := …]`, as the prefix call does.
    if args
        .iter()
        .all(|a| matches!(a, Arg::Explicit(_) | Arg::Named(..)))
        && let Some(rec) = cx.decreasing_rec(Some(f))
    {
        cx.e.note_dot(field, f);
        let full: Vec<Arg<'a>> = std::iter::once(Arg::Explicit(recv))
            .chain(args.iter().copied())
            .collect();
        return Ok(Some((rec, full)));
    }
    let mut full: Vec<Arg<'a>> = Vec::new();
    let defaults = crate::defaults::of_head(cx, &Term::Def(f));
    if crate::named::any(args) || defaults.is_some() {
        // Named arguments in their places, the receiver first in its
        // (named-arguments.md §4.4), and defaults in theirs; only if that's
        // a positional call.
        let mut sig = crate::named::signature(cx, &g.def(f).ty_value)?;
        if let Some(defaults) = defaults {
            sig = sig.with_defaults(defaults);
        }
        let Ok(slots) = crate::named::plan(cx, &sig, args, Some(0)) else {
            return Ok(None);
        };
        for slot in slots {
            match slot {
                Slot::Receiver => full.push(Arg::Explicit(recv)),
                Slot::Given(arg @ (Arg::Explicit(_) | Arg::Default(_))) => full.push(arg),
                _ => return Ok(None),
            }
        }
    } else {
        full.push(Arg::Explicit(recv));
        full.extend(written.iter().map(|e| Arg::Explicit(e)));
    }
    cx.e.note_dot(field, f);
    note_left_out(cx, field, f, args)?;
    // A recursive call of a definition with `decreasing` (`decreasing.rs`).
    if let Some(rec) = cx.decreasing_rec(Some(f)) {
        return Ok(Some((rec, full)));
    }
    Ok(Some(((Term::Def(f), crate::kernel::def_ty(g, f)?), full)))
}

/// `T.f` applied with the receiver as its first explicit argument, and the
/// written arguments after it (D303).
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
    let params = params(g, f);
    if receiver_place(cx, &params, owner)?.is_none() {
        return Err(no_receiver(cx, recv, field, owner, f, key, &params));
    }
    let rterm = crate::check::without_inferred_annotation(recv, rterm);
    // Named arguments (docs/proposals/named-arguments.md §4.4): the receiver
    // fills the first explicit parameter, then the arguments fill theirs. If
    // that leaves nothing out before the last one given and names no
    // implicit parameter, it is the positional call with the arguments in
    // their places; otherwise the call is applied as any other, with the
    // receiver as an argument already elaborated.
    let ordered;
    let defaults = crate::defaults::of_head(cx, &Term::Def(f));
    let args = if crate::named::any(args) || defaults.is_some() {
        let mut sig = crate::named::signature(cx, &g.def(f).ty_value)?;
        if let Some(defaults) = defaults {
            sig = sig.with_defaults(defaults);
        }
        let slots = crate::named::plan(cx, &sig, args, Some(0))?;
        let simple = slots.iter().all(|s| {
            matches!(
                s,
                Slot::Receiver | Slot::Given(Arg::Explicit(_) | Arg::Piped(_) | Arg::Default(_))
            )
        });
        if !simple {
            let piped = crate::check::Piped {
                term: rterm,
                ty: rty,
                span: recv.span(),
                dot: true,
            };
            let slots: Vec<Slot> = (slots.into_iter())
                .map(|s| match s {
                    Slot::Receiver => Slot::Given(Arg::Piped(&piped)),
                    other => other,
                })
                .collect();
            let head = (Term::Def(f), crate::kernel::def_ty(g, f)?);
            return crate::named::apply_slots(cx, head, &slots);
        }
        ordered = (slots.into_iter())
            .filter_map(|s| match s {
                Slot::Given(arg) => Some(arg),
                _ => None,
            })
            .collect::<Vec<_>>();
        &ordered[..]
    } else {
        args
    };
    // The implicit arguments before the receiver, then the receiver,
    // compared with its parameter before the written arguments are checked.
    let mut term = Term::Def(f);
    let mut ty = crate::kernel::def_ty(g, f)?;
    loop {
        let Value::Pi(_, icit, dom, cod) = force(g, ty.clone())? else {
            unreachable!("the receiver's parameter is in the signature");
        };
        if icit.is_implicit() {
            let meta = implicit_arg(cx, icit, &dom);
            let value = cx.eval(&meta)?;
            term = Term::app_icit(term, meta, icit);
            ty = cod.apply(g, value)?;
            continue;
        }
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
        // The receiver's value is computed only if the result type needs it
        // (docs/proposals/checker-evaluation.md).
        ty = cod.apply_lazy(g, || eval(g, &cx.env, &rterm))?;
        term = Term::app(term, rterm);
        break;
    }
    apply_args(cx, (term, ty), args)
}

/// `E-DOT-NO-RECEIVER`: `T.f`'s first explicit parameter isn't a `T`, so
/// dot notation has nowhere to put the receiver (D306). Nothing searches
/// for a later parameter.
fn no_receiver(
    cx: &Ctx,
    recv: &Expr,
    field: &AstName,
    owner: TyHead,
    f: DefId,
    key: &str,
    params: &[Param],
) -> Diagnostic {
    let g = cx.g();
    let ns = scope::display(&namespace(cx, owner)).to_string();
    let shown_ty = cx.show(&g.def(f).ty_value);
    let (call, value) = match recv {
        Expr::Var(n) if written(n) => (
            format!("`{}.{}`", n.text, field.text),
            Some(n.text.to_string()),
        ),
        _ => (format!("`.{}`", field.text), None),
    };
    let there = match &value {
        Some(v) => format!("`{v}` there"),
        None => "the value there".to_string(),
    };
    // The call written in full, with the value in the first parameter of
    // the receiver's type, if there is one.
    let mut placed = false;
    let mut names: Vec<String> = Vec::new();
    let level = cx.level();
    for (depth, p) in params.iter().enumerate() {
        if p.icit != Icit::Explicit {
            continue;
        }
        let env: Vec<Value> = (0..depth).map(|k| Value::var(level + k)).collect();
        let fits = !placed
            && value.is_some()
            && heads(g, Ty::Term(p.ty.clone(), env)).is_ok_and(|h| h.contains(&owner));
        if fits {
            placed = true;
            names.push(value.clone().expect("checked above"));
        } else {
            names.push(p.name.to_string());
        }
    }
    let direct = if names.is_empty() {
        format!("`{key}`")
    } else {
        format!("`{key} {}`", names.join(" "))
    };
    cx.error(
        "E-DOT-NO-RECEIVER",
        format!("`{key}` doesn't take a `{ns}` first, so {call} can't put {there}"),
        format!("`{key}: {shown_ty}`"),
    )
    .with_note(format!(
        "dot notation passes the value as the first argument; call it directly: {direct}"
    ))
}

/// What `recv.field` calls, if that can be found without elaborating `recv`
/// (a variable, a definition without implicit parameters, a literal, or a
/// call whose result type is known from the function's type, such as
/// `w.toNat` in `w.toNat.orAbort`; [`receiver_type`]): for deciding whether
/// a call performs operations before elaborating it.
pub(crate) fn target(cx: &Ctx, recv: &Expr, field: &AstName) -> Result<Option<DefId>> {
    target_within(cx, recv, field, 8)
}

/// The function `recv.field` calls, as [`target`] finds it, and the
/// receiver's place among its explicit parameters (`None` for a local
/// definition named from outside, whose receiver isn't an argument): for
/// telling whether the receiver and the arguments go to parameters of
/// computation type (`effects::passed_args`).
pub(crate) fn target_place(
    cx: &Ctx,
    recv: &Expr,
    field: &AstName,
) -> Result<Option<(DefId, Option<usize>)>> {
    if let Some(f) = helper(cx, recv, field) {
        return Ok(Some((f, None)));
    }
    let Some(ty) = receiver_type(cx, recv, 8)? else {
        return Ok(None);
    };
    let Ok((owner, f, _)) = find(cx, recv, field, ty) else {
        return Ok(None);
    };
    let place = receiver_place(cx, &params(cx.g(), f), owner)?;
    Ok(Some((f, place.map(|(_, k)| k))))
}

fn target_within(cx: &Ctx, recv: &Expr, field: &AstName, depth: usize) -> Result<Option<DefId>> {
    if helper(cx, recv, field).is_some() {
        return Ok(None);
    }
    Ok(match receiver_type(cx, recv, depth)? {
        Some(ty) => find(cx, recv, field, ty).ok().map(|(_, id, _)| id),
        None => None,
    })
}

/// The type of the receiver `recv`, when it can be read off without
/// elaborating it: a variable's, a literal's (`" 4".toNatOrFail`), that of
/// either side of `a ++ b` (`(s ++ "").toNatOrFail`), an annotation's
/// ([`annotation_type`]), or a call's result
/// ([`call_result`]). A literal's is the type `infer` gives it with nothing
/// expected, so the call found is the one dot notation makes.
fn receiver_type(cx: &Ctx, recv: &Expr, depth: usize) -> Result<Option<Ty>> {
    use stitchwort_core::registry::Builtin;
    let g = cx.g();
    let data = |d: DataId| Some(Ty::Value(Value::Data(d, Vec::new())));
    let name = match recv {
        Expr::Var(name) => name,
        Expr::Str(..) | Expr::Include(..) | Expr::Interpolated(..) => {
            return Ok(data(crate::check::builtin_data(cx, Builtin::Text)?));
        }
        Expr::Char(..) => return Ok(data(crate::check::builtin_data(cx, Builtin::Char)?)),
        Expr::Num(..) => return Ok(data(crate::check::nat(cx)?)),
        // A list literal is a `List` (its element type doesn't matter for
        // finding the namespace), as `infer` makes it.
        Expr::List(..) => return Ok(data(crate::check::builtin_data(cx, Builtin::List)?)),
        Expr::Ann(_, ty, _) => return annotation_type(cx, ty),
        Expr::Binary(stitchwort_syntax::ast::BinOp::Append, a, b) if depth > 0 => {
            return match receiver_type(cx, a, depth - 1)? {
                Some(ty) => Ok(Some(ty)),
                None => receiver_type(cx, b, depth - 1),
            };
        }
        _ => return call_result(cx, recv, depth),
    };
    if cx.local(&name.text)?.is_some() {
        return Ok(None);
    }
    Ok(Some(if let Some(level) = cx.lookup(&name.text) {
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
    }))
}

/// The type written in the annotation `(e: T)`, when its head is a global
/// name: a data type (applied to anything), or a definition without
/// parameters (a nickname such as `type Grid := …`). The same head dot
/// notation finds from the elaborated annotation.
fn annotation_type(cx: &Ctx, ty: &Expr) -> Result<Option<Ty>> {
    let mut head = ty;
    let mut applied = false;
    while let Expr::App(f, _) = head {
        head = f;
        applied = true;
    }
    let Expr::Var(name) = head else {
        return Ok(None);
    };
    if cx.lookup(&name.text).is_some() || cx.local(&name.text)?.is_some() {
        return Ok(None);
    }
    let g = cx.g();
    Ok(match cx.e.named(&name.text) {
        Some((Global::Data(d), _)) => Some(Ty::Value(Value::Data(*d, Vec::new()))),
        Some((Global::Def(id), _))
            if !applied && !matches!(&g.def(*id).ty_value, Value::Pi(..)) =>
        {
            Some(Ty::Term(Rc::new(Term::Def(*id)), Vec::new()))
        }
        _ => None,
    })
}

/// The result type of the call `expr` (`f x`, `x.f`, `x.f y`), when it can be
/// read off the function's type without elaborating the call: only its head
/// matters, for finding a namespace. `None` if it can't (a lambda, a local
/// function, a result that's still a function, or too deep a chain).
fn call_result(cx: &Ctx, expr: &Expr, depth: usize) -> Result<Option<Ty>> {
    if depth == 0 {
        return Ok(None);
    }
    let mut explicit = 0;
    let mut head = expr;
    while let Expr::App(f, a) = head {
        if !matches!(**a, Expr::NamedArg(.., Bracket::Square)) {
            explicit += 1;
        }
        head = f;
    }
    let id = match head {
        Expr::Field(inner, f) if helper(cx, inner, f).is_none() => {
            explicit += 1;
            match target_within(cx, inner, f, depth - 1)? {
                Some(id) => id,
                None => return Ok(None),
            }
        }
        Expr::Var(name) if cx.lookup(&name.text).is_none() && cx.local(&name.text)?.is_none() => {
            match cx.e.named(&name.text) {
                Some((Global::Def(id), _)) => *id,
                _ => return Ok(None),
            }
        }
        _ => return Ok(None),
    };
    if explicit == 0 {
        return Ok(None);
    }
    let g = cx.g();
    // The result type as the function's declaration writes it, so that a
    // nickname (`Thunk`) is tried before what it stands for. The bound
    // variables are stand-ins: only the head matters.
    {
        let mut term = Rc::new(g.def(id).ty.clone());
        let mut env: Vec<Value> = Vec::new();
        let mut left = explicit;
        let mut level = cx.level();
        while let Term::Pi(_, icit, _, cod) = term.strip_loc() {
            if !icit.is_implicit() {
                if left == 0 {
                    break;
                }
                left -= 1;
            }
            env.push(Value::var(level));
            level += 1;
            let cod = cod.clone();
            term = cod;
        }
        if left == 0 && !matches!(term.strip_loc(), Term::Pi(..)) {
            // A call that performs operations: the receiver is what it returns.
            let term = crate::effects::comp_result_term(cx, &term).unwrap_or(term);
            return Ok(Some(Ty::Term(term, env)));
        }
    }
    let mut ty = crate::kernel::def_ty(g, id)?;
    let mut level = cx.level();
    loop {
        match force(g, ty)? {
            Value::Pi(_, icit, _, cod) => {
                if !icit.is_implicit() {
                    if explicit == 0 {
                        return Ok(None);
                    }
                    explicit -= 1;
                }
                ty = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            other if explicit == 0 => {
                let value = match crate::effects::comp_parts_at(cx, level, &other)? {
                    Some((_, value)) => value,
                    None => other,
                };
                return Ok(Some(Ty::Value(value)));
            }
            _ => return Ok(None),
        }
    }
}

/// `recv.field args` inferred as its prefix form where that stands for it
/// (`prefix_form`), so the call is elaborated as the prefix call is
/// (SW-129); otherwise as dot notation makes it, [`infer_dot`].
pub(crate) fn infer_call(
    cx: &mut Ctx,
    recv: &Expr,
    field: &AstName,
    args: &[Arg],
) -> Result<(Term, Value)> {
    match call_or_block(cx, recv, field, args)? {
        Dotted::Done(term, ty) => Ok((term, ty)),
        Dotted::Blocked(blocked) => queue_call(cx, recv, field, args, Route::Call, blocked),
    }
}

/// [`infer_call`], with a stop at an unknown left to the caller.
fn call_or_block(cx: &mut Ctx, recv: &Expr, field: &AstName, args: &[Arg]) -> Result<Dotted> {
    if has_failed(cx, call_key(cx, recv, field)) {
        return dot_or_block(cx, recv, field, args);
    }
    let Some((head, full)) = prefix_form(cx, recv, field, args)? else {
        return dot_or_block(cx, recv, field, args);
    };
    // A recursive call of a definition with `decreasing` (its stand-in, a
    // variable) is wrong as its prefix form is: dot notation can't say more.
    let recursive = matches!(head.0, Term::Var(_));
    let snapshot = crate::undo::Snapshot::take(cx);
    match crate::check::apply_args(cx, head, &full) {
        Err(e) if !crate::undo::fatal(&e) && !recursive => {
            mark_failed(cx, call_key(cx, recv, field));
            // The call is wrong either way: say so as dot notation does
            // (it names the receiver's parameter).
            snapshot.restore(cx);
            dot_or_block(cx, recv, field, args)
        }
        result => result.map(|(term, ty)| Dotted::Done(term, ty)),
    }
}

/// Which dot call: the receiver expression (by address and span), the
/// field's span, and the generated-source epoch the address belongs to
/// (`Elaborator::source_epoch`).
pub(crate) type CallKey = (usize, Span, Span, usize);

fn call_key(cx: &Ctx, recv: &Expr, field: &AstName) -> CallKey {
    (
        std::ptr::from_ref(recv) as usize,
        recv.span(),
        field.span,
        cx.e.source_epoch.get(),
    )
}

/// The metavariable state, which a failure is only valid in.
fn state(cx: &Ctx) -> (usize, usize) {
    let g = cx.g();
    (g.metas.borrow().len(), g.meta_trail.borrow().len())
}

fn mark_failed(cx: &Ctx, key: CallKey) {
    let (m, t) = state(cx);
    cx.e.dot_failed.borrow_mut().insert((key, m, t));
}

fn has_failed(cx: &Ctx, key: CallKey) -> bool {
    let (m, t) = state(cx);
    cx.e.dot_failed.borrow().contains(&(key, m, t))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Elaborator;
    use stitchwort_syntax::SourceMap;

    /// A receiver at the same address and spans is a different call once
    /// the generated source before it has ended.
    #[test]
    fn call_key_differs_across_generated_source() {
        let mut sources = SourceMap::new();
        let file = sources.add("test", "x");
        let recv = stitchwort_syntax::parse_expression(file, "x").expect("parses");
        let field = AstName {
            text: "f".into(),
            span: recv.span(),
        };
        let e = Elaborator::new();
        let cx = Ctx::from_parts(&e, vec![], vec![], vec![], recv.span());
        let before = call_key(&cx, &recv, &field);
        assert_eq!(before, call_key(&cx, &recv, &field));
        e.source_epoch.set(e.source_epoch.get() + 1);
        assert_ne!(before, call_key(&cx, &recv, &field));
    }
}
