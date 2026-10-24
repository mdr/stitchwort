//! Named arguments (docs/proposals/named-arguments.md §4): `f (x := e)` for
//! an explicit parameter, `f [x := e]` for an implicit or `auto` one, in any
//! order and mixed with positional arguments.
//!
//! A call's arguments are matched to the parameters of its head's signature
//! (§4.3, D1115), filling slots in written order (§4.2 rule 1, D1112): a
//! positional argument takes the first explicit parameter still free, a
//! named one the parameter it names. The result is the list of arguments in
//! parameter order, which the rest of the elaborator applies as it does a
//! positional call: so a pure named call is the same term as the positional
//! one (§4.2 rule 6). An explicit parameter left free before the last one
//! given makes the call a function of it (§4.2 rule 3, D1095), whose
//! parameter is a variable, never an unknown (§4.2 rule 5).

use std::rc::Rc;

use stitchwort_core::value::{Head, force, quote};
use stitchwort_core::{Icit, Name, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::Expr;

use crate::check::{Arg, Ctx, Piped, Result};

/// One parameter of a signature: its name and kind.
#[derive(Clone, Debug)]
pub(crate) struct Param {
    pub name: Name,
    pub icit: Icit,
    /// The type of the parameter, where the signature was read from a
    /// function type (for the language server's hover over a name).
    pub ty: Option<Value>,
}

/// The parameters a call may name (§4.3).
#[derive(Clone, Debug)]
pub(crate) struct Signature {
    pub params: Vec<Param>,
    /// The walk stopped at an unknown: the names of what follows (if
    /// anything) would come from unification, so they aren't known here.
    pub open: bool,
}

impl Signature {
    /// Whether nothing at all is known: the head's type is an unknown.
    fn unknown(&self) -> bool {
        self.params.is_empty() && self.open
    }
}

/// The signature of a function of type `ty`: its parameters, through
/// computation types (the stages of a curried effectful function), until
/// something that isn't a function type. A type synonym or a type computed
/// by a definition is unfolded; an unknown, even a solved one, ends the
/// walk, since its names would depend on unification order (D1115).
pub(crate) fn signature(cx: &Ctx, ty: &Value) -> Result<Signature> {
    let g = cx.g();
    let mut level = cx.level();
    let mut ty = ty.clone();
    let mut params = Vec::new();
    loop {
        if let Value::Neutral(Head::Meta(_), _) = ty {
            return Ok(Signature { params, open: true });
        }
        if let Some((_, value)) = crate::effects::comp_parts(cx, &ty)? {
            ty = value;
            continue;
        }
        match force(g, ty.clone())? {
            Value::Pi(x, icit, dom, cod) => {
                params.push(Param {
                    name: x,
                    icit,
                    ty: Some((*dom).clone()),
                });
                ty = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            Value::Neutral(Head::Meta(_), _) => return Ok(Signature { params, open: true }),
            _ => {
                return Ok(Signature {
                    params,
                    open: false,
                });
            }
        }
    }
}

/// The signature of a list of fields or parameters written in a
/// declaration (a constructor's fields, a data type's parameters).
pub(crate) fn declared(params: impl IntoIterator<Item = (Name, Icit)>) -> Signature {
    Signature {
        params: params
            .into_iter()
            .map(|(name, icit)| Param {
                name,
                icit,
                ty: None,
            })
            .collect(),
        open: false,
    }
}

/// Whether any of `args` is named.
pub(crate) fn any(args: &[Arg]) -> bool {
    args.iter()
        .any(|a| matches!(a, Arg::Named(..) | Arg::NamedExplicit(..)))
}

/// One parameter's place in a call, in parameter order.
#[derive(Clone)]
pub(crate) enum Slot<'a> {
    /// An argument: positional (`Arg::Explicit`, `Arg::Piped`) for an
    /// explicit parameter, `Arg::Named` for an implicit one.
    Given(Arg<'a>),
    /// An explicit parameter no argument gives, before the last one given:
    /// the call is a function of it.
    Missing(Name),
    /// The parameter dot notation's receiver fills.
    Receiver,
}

/// What fills a parameter while matching.
#[derive(Clone, Copy)]
enum Fill<'a> {
    Arg(Arg<'a>),
    Receiver,
}

/// Matches `args`, in written order, to the parameters of `sig` (§4.2 rule
/// 1): a dot receiver fills the explicit parameter `receiver` (its index
/// among the explicit parameters) first; then a positional argument fills
/// the first explicit parameter still free, and a named one the parameter
/// it names. Positional arguments past the end of the signature follow in
/// order. The result is in parameter order, up to the last parameter given:
/// implicit parameters not named are left out (they're inserted as
/// unknowns, as in a positional call), explicit ones are
/// [`Slot::Missing`].
pub(crate) fn plan<'a>(
    cx: &Ctx,
    sig: &Signature,
    args: &[Arg<'a>],
    receiver: Option<usize>,
) -> Result<Vec<Slot<'a>>> {
    let params = &sig.params;
    let (filled, overflow) = fill(cx, sig, args, receiver)?;
    let last = filled.iter().rposition(Option::is_some);
    let mut slots = Vec::new();
    if let Some(last) = last {
        for (i, fill) in filled.iter().enumerate().take(last + 1) {
            match fill {
                Some(Fill::Arg(arg)) => slots.push(Slot::Given(placed(*arg))),
                Some(Fill::Receiver) => slots.push(Slot::Receiver),
                None if params[i].icit == Icit::Explicit => {
                    slots.push(Slot::Missing(params[i].name.clone()))
                }
                None => {}
            }
        }
    }
    slots.extend(overflow.into_iter().map(Slot::Given));
    Ok(slots)
}

/// What [`plan`] matches each parameter of `sig` with (`Arg::Explicit` for
/// an explicit one, `Arg::Named` for an implicit one), and the positional
/// arguments past the end: for a constructor, whose fields are elaborated
/// by their own code.
#[allow(clippy::type_complexity)]
pub(crate) fn assign<'a>(
    cx: &Ctx,
    sig: &Signature,
    args: &[Arg<'a>],
) -> Result<(Vec<Option<Arg<'a>>>, Vec<Arg<'a>>)> {
    let (filled, overflow) = fill(cx, sig, args, None)?;
    let assigned = (filled.into_iter())
        .map(|f| match f {
            Some(Fill::Arg(arg)) => Some(placed(arg)),
            _ => None,
        })
        .collect();
    Ok((assigned, overflow))
}

/// The matching of [`plan`]: what fills each parameter, and the positional
/// arguments past the end of the signature.
#[allow(clippy::type_complexity)]
fn fill<'a>(
    cx: &Ctx,
    sig: &Signature,
    args: &[Arg<'a>],
    receiver: Option<usize>,
) -> Result<(Vec<Option<Fill<'a>>>, Vec<Arg<'a>>)> {
    let params = &sig.params;
    let mut filled: Vec<Option<Fill<'a>>> = vec![None; params.len()];
    let explicit: Vec<usize> = (0..params.len())
        .filter(|&i| params[i].icit == Icit::Explicit)
        .collect();
    if let Some(k) = receiver
        && let Some(&i) = explicit.get(k)
    {
        filled[i] = Some(Fill::Receiver);
    }
    let mut overflow: Vec<Arg<'a>> = Vec::new();
    for arg in args {
        match arg {
            Arg::Explicit(_) | Arg::Piped(_) => {
                match explicit.iter().find(|&&i| filled[i].is_none()) {
                    Some(&i) if overflow.is_empty() => filled[i] = Some(Fill::Arg(*arg)),
                    _ => overflow.push(*arg),
                }
            }
            Arg::Named(name, _) | Arg::NamedExplicit(name, _) => {
                let wants_explicit = matches!(arg, Arg::NamedExplicit(..));
                let i = find(cx, sig, name, wants_explicit)?;
                if let Some(ty) = &params[i].ty {
                    let mut names = cx.names.clone();
                    names.extend(params[..i].iter().map(|p| p.name.clone()));
                    cx.e.note_parameter(name, ty, names);
                }
                if let Some(earlier) = filled[i] {
                    return Err(duplicate(name, earlier));
                }
                filled[i] = Some(Fill::Arg(*arg));
            }
        }
    }
    Ok((filled, overflow))
}

/// The arguments of `slots` as a positional call's, if no parameter is
/// missing and there's no receiver.
pub(crate) fn positional<'a>(slots: &[Slot<'a>]) -> Option<Vec<Arg<'a>>> {
    slots
        .iter()
        .map(|s| match s {
            Slot::Given(arg) => Some(*arg),
            Slot::Missing(_) | Slot::Receiver => None,
        })
        .collect()
}

/// The index of the parameter `name` names, with the bracket written.
fn find(
    cx: &Ctx,
    sig: &Signature,
    name: &stitchwort_syntax::ast::Name,
    explicit: bool,
) -> Result<usize> {
    let params = &sig.params;
    let matching: Vec<usize> = (0..params.len())
        .filter(|&i| *params[i].name == *name.text)
        .collect();
    let right_kind: Vec<usize> = matching
        .iter()
        .copied()
        .filter(|&i| (params[i].icit == Icit::Explicit) == explicit)
        .collect();
    match right_kind[..] {
        [i] => Ok(i),
        [] if !matching.is_empty() => Err(wrong_bracket(name, explicit)),
        [] => Err(unknown(cx, sig, name)),
        _ => Err(Diagnostic::error(
            "E-AMBIGUOUS",
            format!("`{}` names {} parameters here", name.text, right_kind.len()),
        )
        .with_label(name.span, "which one is meant can't be told by name")
        .with_note("pass them by position")),
    }
}

/// `(x := e)` for an implicit parameter, or `[x := e]` for an explicit one
/// (D1093).
fn wrong_bracket(name: &stitchwort_syntax::ast::Name, written_explicit: bool) -> Diagnostic {
    let x = &name.text;
    let (kind, fix) = if written_explicit {
        ("an implicit", format!("[{x} := …]"))
    } else {
        ("an explicit", format!("({x} := …)"))
    };
    Diagnostic::error(
        "E-NAMED-BRACKET",
        format!("`{x}` is {kind} parameter: write `{fix}`"),
    )
    .with_label(name.span, format!("`{x}` is {kind} parameter"))
    .with_note(
        "round brackets name an explicit parameter and square brackets an implicit or `auto` \
         one, as in declarations",
    )
}

/// A name the signature doesn't have, or a call whose signature isn't known.
fn unknown(cx: &Ctx, sig: &Signature, name: &stitchwort_syntax::ast::Name) -> Diagnostic {
    let _ = cx;
    if sig.unknown() {
        return Diagnostic::error(
            "E-UNKNOWN-NAME",
            "the parameter names of this function aren't known here",
        )
        .with_label(name.span, format!("`{}` can't be found by name", name.text))
        .with_note(
            "names come from a declared signature or a type annotation; add one, as in \
             `let g: (low: Nat) -> (high: Nat) -> Nat := …`",
        );
    }
    let mut d = Diagnostic::error(
        "E-UNKNOWN-NAME",
        format!("this function has no parameter named `{}`", name.text),
    )
    .with_label(name.span, "not a parameter of this function");
    let shown: Vec<String> = (sig.params.iter())
        .filter(|p| !p.name.is_empty() && &*p.name != "_" && !p.name.starts_with('%'))
        .map(|p| match p.icit {
            Icit::Explicit => format!("`({})`", p.name),
            Icit::Implicit => format!("`[{}]`", p.name),
            Icit::Auto => format!("`[auto {}]`", p.name),
        })
        .collect();
    d = if shown.is_empty() {
        d.with_note("its parameters have no names")
    } else {
        d.with_note(format!(
            "its parameters are {} (round brackets: explicit, square: implicit)",
            list(shown)
        ))
    };
    if sig.open {
        d = d.with_note(
            "the names of what its result takes aren't known here; add a type annotation to \
             name them",
        );
    }
    d
}

fn duplicate(name: &stitchwort_syntax::ast::Name, earlier: Fill) -> Diagnostic {
    let d = Diagnostic::error(
        "E-DUPLICATE-ARGUMENT",
        format!("`{}` is given twice", name.text),
    )
    .with_label(name.span, "given again here");
    match earlier {
        Fill::Arg(arg) => d.with_label(arg_span(&arg), "already given here"),
        Fill::Receiver => d.with_note(format!(
            "`{}` is the parameter the value before the `.` fills",
            name.text
        )),
    }
}

/// An argument as it's applied in its place: `(x := e)` as `e`.
fn placed(arg: Arg) -> Arg {
    match arg {
        Arg::NamedExplicit(_, value) => Arg::Explicit(value),
        other => other,
    }
}

/// Where an argument is written.
fn arg_span(arg: &Arg) -> stitchwort_syntax::Span {
    match arg {
        Arg::Explicit(e) => e.span(),
        Arg::Named(n, e) | Arg::NamedExplicit(n, e) => n.span.to(e.span()),
        Arg::Piped(p) => p.span,
    }
}

/// How many explicit parameters a call reaches before it becomes a function
/// of a missing one (or all it reaches, if none is missing): for deciding
/// whether the call performs operations (`effects::call_performs`). `None`
/// if the arguments can't be matched.
pub(crate) fn reached(
    cx: &Ctx,
    ty: &Value,
    call: &Expr,
    args: &[&Expr],
    extra: usize,
) -> Option<usize> {
    let sig = signature(cx, ty).ok()?;
    let mut written: Vec<Arg> = args.iter().map(|a| crate::check::arg_of(a)).collect();
    // The value piped in: a positional argument (any expression stands for it).
    for _ in 0..extra {
        written.push(Arg::Explicit(call));
    }
    let slots = plan(cx, &sig, &written, None).ok()?;
    let mut count = 0;
    for slot in &slots {
        match slot {
            Slot::Missing(_) => return Some(count),
            Slot::Given(Arg::Named(..)) => {}
            _ => count += 1,
        }
    }
    Some(count)
}

/// Applies `head` to `slots` (a [`plan`] without a receiver), as
/// `check::apply_args` does, with each missing parameter bound by a lambda
/// around the call (§4.2 rule 3): `clampTo (high := 10)` is
/// `low value => clampTo low 10 value`. The arguments after a missing
/// parameter are elaborated inside the lambda (§4.5 R4).
pub(crate) fn apply_slots(
    cx: &mut Ctx,
    head: (Term, Value),
    slots: &[Slot],
) -> Result<(Term, Value)> {
    if !slots.iter().any(|s| matches!(s, Slot::Missing(_))) {
        let args = positional(slots).expect("no receiver here");
        return crate::check::apply_args(cx, head, &args);
    }
    match apply_missing(cx, head.clone(), slots, false) {
        Ok((result, _)) => Ok(result),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(e) if e.code == "E-TYPE-MISMATCH" => Err(rigid_note(cx, head, slots, e)),
        Err(e) => Err(e),
    }
}

/// A term and its type.
type Typed = (Term, Value);

/// [`apply_slots`] with missing parameters: bound as variables, or with
/// `inferring`, given unknowns (for the note of [`rigid_note`], which reads
/// what unification makes of them: the second result).
fn apply_missing(
    cx: &mut Ctx,
    head: Typed,
    slots: &[Slot],
    inferring: bool,
) -> Result<(Typed, Vec<(Name, Value)>)> {
    let g = cx.g();
    let mark = cx.mark();
    // A value piped in was elaborated outside: under the lambda's binders
    // its term is shifted past them.
    let mut shifted: Vec<Piped> = Vec::new();
    let mut depth = 0;
    for slot in slots {
        match slot {
            Slot::Missing(_) if !inferring => depth += 1,
            Slot::Given(Arg::Piped(p)) if depth > 0 => shifted.push(Piped {
                term: p.term.shift(g, depth, 0)?,
                ty: p.ty.clone(),
                span: p.span,
            }),
            _ => {}
        }
    }
    let mut binders: Vec<(Name, Value, usize)> = Vec::new();
    let mut unknowns: Vec<(Name, Value)> = Vec::new();
    let result = (|| -> Result<(Term, Value)> {
        let (mut term, mut ty) = head;
        let mut chunk: Vec<Arg> = Vec::new();
        let mut next_shifted = shifted.iter();
        for slot in slots {
            match slot {
                Slot::Given(Arg::Piped(_)) if !binders.is_empty() => {
                    chunk.push(Arg::Piped(next_shifted.next().expect("shifted above")));
                }
                Slot::Given(arg) => chunk.push(*arg),
                Slot::Receiver => unreachable!("dot notation passes its receiver as an argument"),
                Slot::Missing(name) => {
                    (term, ty) = crate::check::apply_args(cx, (term, ty), &chunk)?;
                    chunk.clear();
                    (term, ty) = crate::check::insert(cx, term, ty)?;
                    let (dom, cod) = crate::check::function_parts(cx, &ty)?;
                    if inferring {
                        let meta = cx.fresh_meta();
                        let value = cx.eval(&meta)?;
                        unknowns.push(((*name).clone(), value.clone()));
                        term = Term::app(term, meta);
                        ty = cod.apply(g, value)?;
                        continue;
                    }
                    let at = cx.level();
                    cx.bind_hidden((*name).clone(), dom.clone());
                    term = Term::app(term.shift(g, 1, 0)?, Term::Var(0));
                    ty = cod.apply(g, Value::var(at))?;
                    binders.push(((*name).clone(), dom, at));
                }
            }
        }
        crate::check::apply_args(cx, (term, ty), &chunk)
    })();
    let (mut term, ty) = match result {
        Ok(found) => found,
        Err(e) => {
            cx.reset(mark);
            return Err(e);
        }
    };
    if inferring {
        return Ok(((term, ty), unknowns));
    }
    // `x… => call`, annotated for the kernel, which doesn't infer a
    // lambda's type.
    let mut fun_ty = match cx.quote(&ty) {
        Ok(t) => t,
        Err(e) => {
            cx.reset(mark);
            return Err(e);
        }
    };
    for (x, dom, at) in binders.iter().rev() {
        let dom = quote(g, *at, dom)?;
        fun_ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(dom), Rc::new(fun_ty));
        term = Term::Lam(x.clone(), Icit::Explicit, Rc::new(term));
    }
    cx.reset(mark);
    let value = cx.eval(&fun_ty)?;
    Ok((
        (Term::Ann(Rc::new(term), Rc::new(fun_ty)), value),
        Vec::new(),
    ))
}

/// A type mismatch in a call with missing parameters: they're variables,
/// so the call must work for every value of them (§4.2 rule 5). If giving
/// them unknowns instead would have worked, the note says what to write.
fn rigid_note(cx: &mut Ctx, head: (Term, Value), slots: &[Slot], e: Diagnostic) -> Diagnostic {
    let missing: Vec<&Name> = (slots.iter())
        .filter_map(|s| match s {
            Slot::Missing(name) => Some(name),
            _ => None,
        })
        .collect();
    let snapshot = crate::undo::Snapshot::take(cx);
    let solved: Vec<String> = match apply_missing(cx, head, slots, true) {
        Ok((_, unknowns)) => unknowns
            .iter()
            .filter_map(|(x, value)| {
                let forced = force(cx.g(), value.clone()).ok()?;
                if matches!(forced, Value::Neutral(Head::Meta(_), _)) {
                    return None;
                }
                Some(format!("`({x} := {})`", cx.show(&forced)))
            })
            .collect(),
        Err(_) => Vec::new(),
    };
    snapshot.restore(cx);
    let names = list(missing.iter().map(|x| format!("`{x}`")).collect());
    let mut e = e.with_note(format!(
        "this call leaves out {names}, so it must work for every value of {}",
        if missing.len() == 1 { "it" } else { "them" }
    ));
    if !solved.is_empty() {
        e = e.with_note(format!(
            "to give a particular value, write {}",
            list(solved)
        ));
    }
    e
}

/// For each parameter of a function of type `ty`, as [`signature`] walks
/// it, the earlier parameters its type mentions.
pub(crate) fn dependencies(cx: &Ctx, ty: &Value) -> Result<Vec<Vec<usize>>> {
    let g = cx.g();
    let base = cx.level();
    let mut ty = ty.clone();
    let mut out: Vec<Vec<usize>> = Vec::new();
    loop {
        if let Value::Neutral(Head::Meta(_), _) = ty {
            return Ok(out);
        }
        if let Some((_, value)) = crate::effects::comp_parts(cx, &ty)? {
            ty = value;
            continue;
        }
        let Value::Pi(_, _, dom, cod) = force(g, ty.clone())? else {
            return Ok(out);
        };
        let i = out.len();
        let dom = quote(g, base + i, &dom)?;
        out.push((0..i).filter(|j| dom.mentions(i - 1 - j)).collect());
        ty = cod.apply(g, Value::var(base + i))?;
    }
}

/// Which of `args` (by index) fills each parameter of `sig`, as [`plan`]
/// matches them; `None` if they don't match.
pub(crate) fn filled_by(cx: &Ctx, sig: &Signature, args: &[Arg]) -> Option<Vec<Option<usize>>> {
    let (filled, _) = fill(cx, sig, args, None).ok()?;
    let value = |arg: &Arg| -> Option<*const Expr> {
        match arg {
            Arg::Explicit(e) | Arg::Named(_, e) | Arg::NamedExplicit(_, e) => {
                Some(*e as *const Expr)
            }
            Arg::Piped(_) => None,
        }
    };
    Some(
        filled
            .iter()
            .map(|f| match f {
                Some(Fill::Arg(arg)) => {
                    let target = value(arg)?;
                    args.iter().position(|a| value(a) == Some(target))
                }
                _ => None,
            })
            .collect(),
    )
}

/// `a`, `a and b`, `a, b and c`.
pub(crate) fn list(items: Vec<String>) -> String {
    match items.len() {
        0 => String::new(),
        1 => items[0].clone(),
        n => format!("{} and {}", items[..n - 1].join(", "), items[n - 1]),
    }
}
