//! `auto` parameters on data types (docs/proposals/interfaces.md §7.5,
//! stage 4): `type Map (k: Type) (v: Type) [auto ord: Ord k] = …`.
//!
//! The kernel sees an ordinary parameter. The elaborator fills it in
//! wherever the type is written, as for a function's `auto` argument:
//! `Map Text Nat` is `Map Text Nat [ord := ?ord]` with an obligation for
//! `?ord: Ord Text`, which unification may solve first (an existing map's
//! type fixes it) or instance search solves after (§5.5). It can be given by
//! name, `Map k v [ord := Nat.descending]`, and in an instance head is
//! written as a variable, `Show (Map k v [ord := o])`, which matching fixes.

use stitchwort_core::value::{conv, force};
use stitchwort_core::{DataId, Icit, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Binder, Decl};

use crate::Elaborator;
use crate::check::{Arg, Ctx, apply_args, check, implicit_arg};

type Result<T> = std::result::Result<T, Diagnostic>;

impl Elaborator {
    /// An `auto` parameter of a data type must ask for an interface:
    /// nothing else is found by instance search (`E-DATA-AUTO`).
    pub(crate) fn check_data_auto(&self, cx: &mut Ctx, binder: &Binder, ty: &Term) -> Result<()> {
        let value = cx.eval(ty)?;
        if let Value::Data(i, _) = force(cx.g(), value.clone())?
            && self.is_interface(i)
        {
            return Ok(());
        }
        Err(Diagnostic::error(
            "E-DATA-AUTO",
            format!(
                "a type's `auto` parameter must ask for an interface, but `{}` isn't one",
                cx.show(&value)
            ),
        )
        .with_label(binder.ty.span(), "not an interface")
        .with_note(
            "a type's `auto` parameter is found by instance search wherever the type is written, \
             like `[auto ord: Ord k]`; a parameter that's always given is written `(x: T)`",
        ))
    }

    /// For each of data type `decl`'s parameters (one per name), whether it's
    /// `auto`.
    pub(crate) fn data_auto_params(decl: &Decl) -> Vec<bool> {
        let Decl::Data {
            params,
            auto_params,
            ..
        } = decl
        else {
            unreachable!()
        };
        params
            .iter()
            .zip(auto_params)
            .flat_map(|(b, auto)| std::iter::repeat_n(*auto, b.names.len()))
            .collect()
    }

    /// Data types defined together share their parameters, so the same ones
    /// must be `auto` (`E-MUTUAL-PARAMETERS`).
    pub(crate) fn same_auto_params(first: &Decl, decl: &Decl) -> Result<()> {
        if Self::data_auto_params(first) == Self::data_auto_params(decl) {
            return Ok(());
        }
        let (Decl::Data { name: a, .. }, Decl::Data { name: b, .. }) = (first, decl) else {
            unreachable!()
        };
        Err(Diagnostic::error(
            "E-MUTUAL-PARAMETERS",
            format!(
                "`{}` and `{}` are defined together, so the same parameters must be `auto`",
                a.text, b.text
            ),
        )
        .with_label(b.span, format!("`{}` is declared here", b.text))
        .with_label(a.span, format!("`{}` is declared here", a.text)))
    }
}

/// `D args`, a data type applied to its parameters and indices: an `auto`
/// parameter takes a named argument written in its place, `[ord := e]`, or
/// is found like a function's `auto` argument.
pub(crate) fn data_app(cx: &mut Ctx, d: DataId, args: &[Arg]) -> Result<(Term, Value)> {
    let g = cx.g();
    let data = g.data(d);
    let auto = |k: usize| data.auto_params.get(k).copied().unwrap_or(false);
    if let Some(Arg::NamedExplicit(name, _)) = args.iter().find(|a| matches!(a, Arg::NamedExplicit(..))) {
        return Err(Diagnostic::error(
            "E-UNKNOWN-NAME",
            format!("`{}`'s parameters are given by position", data.name),
        )
        .with_label(name.span, "a type's parameters can't be given by name"));
    }
    let all = data.params.len() + data.indices.len();
    let needed = (0..all).filter(|k| !auto(*k)).count();
    let given = args
        .iter()
        .take_while(|a| matches!(a, Arg::Explicit(_) | Arg::Named(..)))
        .filter(|a| matches!(a, Arg::Explicit(_)))
        .count();
    if given < needed {
        return Err(cx.error(
            "E-ARITY",
            format!("`{}` needs {needed} argument(s)", data.name),
            "here",
        ));
    }
    let mut env = Vec::new();
    let mut terms = Vec::new();
    let mut next = 0;
    for (k, (x, param_ty)) in data.params.iter().chain(&data.indices).enumerate() {
        let ty = stitchwort_core::value::eval(g, &env, param_ty)?;
        let term = if auto(k) {
            match args.get(next) {
                Some(Arg::Named(name, value)) if *name.text == **x => {
                    next += 1;
                    check(cx, value, &ty)?
                }
                _ if cx.e.in_instance_signature.get() => {
                    return Err(unwritten_in_head(cx, d, x));
                }
                _ => implicit_arg(cx, Icit::Auto, &ty),
            }
        } else {
            match args.get(next) {
                Some(Arg::Explicit(value)) => {
                    next += 1;
                    check(cx, value, &ty)?
                }
                Some(Arg::Named(name, _)) => return Err(misplaced_named(cx, d, name)),
                _ => return Err(cx.error("E-ARITY", "data type parameters are explicit", "here")),
            }
        };
        env.push(cx.eval(&term)?);
        terms.push(term);
    }
    let head = (Term::data(d, terms), Value::Sort(data.sort));
    match args.get(next) {
        Some(Arg::Named(name, _)) => Err(misplaced_named(cx, d, name)),
        _ => apply_args(cx, head, &args[next..]),
    }
}

/// `E-INSTANCE-HEAD`: in an instance's type, a data type's `auto` parameter
/// is a head variable, written `[ord := o]`, never found (§7.5).
fn unwritten_in_head(cx: &Ctx, d: DataId, x: &stitchwort_core::Name) -> Diagnostic {
    let name = &cx.g().data(d).name;
    cx.error(
        "E-INSTANCE-HEAD",
        format!(
            "in an instance's type, `{name}`'s `auto` parameter `{x}` is written as a variable"
        ),
        format!("write `[{x} := o]` among `{name}`'s parameters here"),
    )
    .with_note(format!(
        "the instance is then for every `{x}`; where it's used, `o` is the one in the type it's \
         used at, not found again"
    ))
}

/// A named argument to a data type that isn't one of its `auto` parameters
/// in its place.
fn misplaced_named(cx: &Ctx, d: DataId, name: &stitchwort_syntax::ast::Name) -> Diagnostic {
    let data = cx.g().data(d);
    let is_auto = data
        .params
        .iter()
        .zip(&data.auto_params)
        .any(|((x, _), a)| *a && **x == *name.text);
    let message = if is_auto {
        format!(
            "`[{} := …]` goes in its place among `{}`'s parameters, as declared",
            name.text, data.name
        )
    } else {
        format!(
            "`{}` has no `auto` parameter named `{}`",
            data.name, name.text
        )
    };
    Diagnostic::error("E-UNKNOWN-NAME", message).with_label(name.span, "here")
}

/// A note for a type mismatch between two applications of the same data
/// type that differ only in its `auto` parameters: `Map Nat Nat [ord := a]`
/// and `Map Nat Nat [ord := b]` are different types (§7.5).
pub(crate) fn auto_mismatch_note(cx: &Ctx, expected: &Value, found: &Value) -> Option<String> {
    let g = cx.g();
    let (Value::Data(d, a), Value::Data(e, b)) = (
        force(g, expected.clone()).ok()?,
        force(g, found.clone()).ok()?,
    ) else {
        return None;
    };
    let data = g.data(d);
    if d != e || !data.auto_params.contains(&true) || a.len() != b.len() {
        return None;
    }
    let level = cx.level();
    let mut differing = Vec::new();
    for (k, (x, y)) in a.iter().zip(&b).enumerate() {
        if conv(g, level, x, y).ok()? {
            continue;
        }
        if data.auto_params.get(k) != Some(&true) {
            return None;
        }
        differing.push(data.params[k].0.clone());
    }
    let x = differing.first()?;
    Some(format!(
        "the `{x}` dictionaries differ: `{}`'s `{x}` is part of its type, so a value built with \
         one is a different type from one built with another (they're compared as whole \
         dictionaries, not just their functions)",
        data.name
    ))
}
