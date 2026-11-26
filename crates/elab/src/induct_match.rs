//! `match induct (f args) with | eqK … => …` (docs/proposals/function-equations.md
//! §5.3, stage 2b; D2182): functional induction written as a `match`.
//!
//! ```text
//! match induct (countAbove k xs) with
//!   | eq1 => …
//!   | eq2IfTrue x rest h ih => …
//!   | eq2IfFalse x rest h ih => …
//! ```
//!
//! is the application of `countAbove.induct` (stage 2a, `equations/induct.rs`)
//! with the motive worked out from the goal and one case for each
//! alternative:
//!
//! - the call's arguments in the motive's places (after the fixed prefix) are
//!   distinct variables of the context; the **motive** is the goal with the
//!   call replaced by the motive's result parameter and those variables by the
//!   motive's other parameters;
//! - the variables in scope whose types mention the call or one of those
//!   variables (and, in turn, those whose types mention one of them) are
//!   **generalised** as a `match` on an expression generalises
//!   (`matching.rs`): the motive takes them as premises, so each case is given
//!   them refined (under their own names, not bound by the alternative) and
//!   each `ih` takes them as premises;
//! - an alternative is named after its case and binds the case's variables,
//!   hypotheses and induction hypotheses by position (`_` ignores one); the
//!   alternatives may come in any order and all are required.
//!
//! The term it writes is `f.induct` applied to the fixed prefix, the motive,
//! the cases, the variables and the generalised ones; the kernel checks it.

use std::rc::Rc;
use stitchwort_core::Ev;
use stitchwort_core::ProofMark;

use stitchwort_core::collections::HashMap;
use stitchwort_core::value::{DUMMY_LEVEL, force};
use stitchwort_core::{Icit, Name, Term, Value};
use stitchwort_syntax::ast::{Expr, InductAlt};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Result, check, infer, insert, quote_unfolded};
use crate::lift;
use crate::matching::{free_levels, is_var, occurs, same_shifted};

/// `match induct …` where no type is expected: its type is a new unknown,
/// which the motive then can't be worked out from.
pub(crate) fn infer_induct(_cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    Err(
        Diagnostic::error("E-MATCH-MOTIVE", "`match induct` needs a goal to work from")
            .with_label(expr.span(), "no type is expected here")
            .with_note(
                "the motive is the goal with the call abstracted: use `match induct` as the body \
                 of a theorem, or where a proposition is expected",
            ),
    )
}

fn motive_error(span: Span, message: impl Into<String>) -> Diagnostic {
    Diagnostic::error("E-MATCH-MOTIVE", message)
        .with_label(span, "this `match induct`")
        .with_note(
            "the explicit `f.induct`, with the motive written out, is the fallback \
             (docs/proposals/function-equations.md §5.3)",
        )
}

/// The binders of a telescope of function types, by name and mode.
fn telescope(cx: &Ctx, ty: &Value) -> Result<Vec<(Name, Icit)>> {
    let g = cx.g();
    let mut out = Vec::new();
    let mut cur = ty.clone();
    while let Value::Pi(name, icit, _, cod, _) = force(&g, cur.clone())? {
        out.push((name, icit));
        cur = cod.apply(&g, Value::dummy_var())?;
    }
    Ok(out)
}

/// The call as `f a b …`: the function's name and the arguments written.
/// `xs.f a` (dot form) reads as `f xs a`, as an ordinary call does, with
/// `f`'s full name for the dot's namespace lookup.
fn spine(cx: &mut Ctx, call: &Expr) -> Result<Option<(stitchwort_syntax::ast::Name, Vec<Expr>)>> {
    let mut args = Vec::new();
    let mut e = call;
    loop {
        match e {
            Expr::App(f, a) => {
                args.push((**a).clone());
                e = f;
            }
            Expr::Bracketed(inner, _) => e = inner,
            Expr::Var(name) => {
                args.reverse();
                return Ok(Some((name.clone(), args)));
            }
            Expr::Field(recv, field, id) => {
                args.reverse();
                let written: Vec<crate::check::Arg<'_>> =
                    args.iter().map(crate::check::Arg::Explicit).collect();
                let Some(((Term::Def(f), _), full)) =
                    crate::dot::prefix_form(cx, recv, field, id, &written)?
                else {
                    return Ok(None);
                };
                let mut all = Vec::new();
                for arg in full {
                    let crate::check::Arg::Explicit(e) = arg else {
                        return Ok(None);
                    };
                    all.push(e.clone());
                }
                let name = stitchwort_syntax::ast::Name {
                    text: cx.g().def(f).name().to_string(),
                    span: field.span,
                };
                return Ok(Some((name, all)));
            }
            _ => return Ok(None),
        }
    }
}

fn list(names: impl IntoIterator<Item = impl AsRef<str>>) -> String {
    let names: Vec<String> = names
        .into_iter()
        .map(|n| format!("`{}`", n.as_ref()))
        .collect();
    names.join(", ")
}

/// Maps the context's variables and the call to the motive's: a term in the
/// `base` variables of the `match induct`, to one in `depth`.
struct Abstract<'a> {
    base: usize,
    depth: usize,
    call: &'a Term,
    /// The level of the motive's result parameter.
    result: usize,
    /// Where each variable that is replaced goes.
    map: &'a HashMap<usize, usize>,
}

impl Abstract<'_> {
    fn apply(&self, g: &Ev, term: &Term) -> Result<Term> {
        let hook = |t: &Term, under: usize| {
            same_shifted(self.call, t, under, 0)
                .then(|| Term::Var(self.depth + under - 1 - self.result))
        };
        lift::replace_with(
            g,
            term,
            self.base,
            &|l| {
                let new = self.map.get(&l).copied().unwrap_or(l);
                Ok(Term::Var(self.depth - 1 - new))
            },
            &hook,
        )
    }
}

/// `match induct …` checked against `goal`.
pub(crate) fn check_induct(cx: &mut Ctx, expr: &Expr, goal: &Value) -> Result<Term> {
    let Expr::Induct { call, alts, span } = expr else {
        unreachable!("only called on `match induct`")
    };
    let outer = *span;
    let written = Span::new(span.file, span.start, call.span().end);
    let span = written;
    let g = cx.g();
    let base = cx.level();
    if !crate::patlet::proposition(cx, goal)? {
        return Err(Diagnostic::error(
            "E-MATCH-MOTIVE",
            "`match induct` proves a proposition, and this isn't one",
        )
        .with_label(span, "the goal here isn't a proposition")
        .with_note(
            "the motive of `f.induct` is a proposition; for a definition that computes data, \
             state what it should satisfy as a theorem and use `match induct` there",
        ));
    }
    let Some((head, owned_args)) = spine(cx, call)? else {
        return Err(motive_error(
            call.span(),
            "`match induct` takes a call of a function written as `f a b …`",
        )
        .with_label(call.span(), "this isn't a function applied to arguments"));
    };
    let args: Vec<&Expr> = owned_args.iter().collect();
    // The call, as the goal says it, for the occurrence test.
    let (call_term, call_ty) = infer(cx, call)?;
    let (call_term, _) = insert(cx, call_term, call_ty)?;
    let call_normal = quote_unfolded(&g, base, &cx.eval(&call_term)?)?;
    // `f.induct`.
    let induct_name = stitchwort_syntax::ast::Name {
        text: format!("{}.induct", head.text),
        span: head.span,
    };
    // `f.induct` is the compiler's, at the span of the `f` the call (inferred
    // above) already noted: noting it too would replace that reference.
    let looked_up =
        crate::Elaborator::unnoted_in(cx, |cx| infer(cx, &Expr::Var(induct_name.clone())));
    let (_, induct_ty) = match looked_up {
        Ok(found) => insert(cx, found.0, found.1)?,
        Err(d) => return Err(no_induct(d, &head.text, call.span())),
    };
    // The fixed prefix: the explicit parameters before the motive.
    let mut prefix = 0;
    for (name, icit) in telescope(cx, &induct_ty)? {
        if &*name == "motive" {
            break;
        }
        if icit == Icit::Explicit {
            prefix += 1;
        }
    }
    if args.len() < prefix {
        return Err(motive_error(
            call.span(),
            format!(
                "`{}` is given {} argument{}, but the fixed prefix of `{}` takes {prefix}",
                head.text,
                args.len(),
                if args.len() == 1 { "" } else { "s" },
                induct_name.text
            ),
        ));
    }
    let mut applied = Expr::Var(induct_name.clone());
    for a in &args[..prefix] {
        applied = Expr::App(Box::new(applied), Box::new((*a).clone()));
    }
    let (with_prefix, ty) = crate::Elaborator::unnoted_in(cx, |cx| infer(cx, &applied))?;
    let (with_prefix, ty) = insert(cx, with_prefix, ty)?;
    let Value::Pi(_, _, motive_ty, rest, _) = force(&g, ty)? else {
        return Err(motive_error(span, "`f.induct` has no motive"));
    };
    // The motive's parameters: the targets, then the result.
    let params = telescope(cx, &motive_ty)?;
    let k = params.len().saturating_sub(1);
    // The cases, and the targets after them, with the cases' own binders.
    let rest_dummy = rest.apply(&g, Value::dummy_var())?;
    let after = telescope(cx, &rest_dummy)?;
    let ncases = after.len().saturating_sub(k);
    let mut cases: Vec<(Name, Vec<Name>)> = Vec::new();
    {
        let mut cur = rest_dummy.clone();
        for _ in 0..ncases {
            let Value::Pi(name, _, dom, cod, _) = force(&g, cur)? else {
                unreachable!("counted")
            };
            let own = telescope(cx, &dom)?;
            cases.push((name, own.into_iter().map(|(n, _)| n).collect()));
            cur = cod.apply(&g, Value::dummy_var())?;
        }
    }
    // The targets are distinct variables.
    let written = &args[prefix..];
    if written.len() != k {
        return Err(motive_error(
            call.span(),
            format!(
                "`{}` is given {} argument{} after the fixed prefix, but it takes {k}",
                head.text,
                written.len(),
                if written.len() == 1 { "" } else { "s" },
            ),
        ));
    }
    let mut targets: Vec<usize> = Vec::new();
    for a in written {
        let level = match a {
            Expr::Var(name) => cx.lookup(&name.text).filter(|&l| is_var(&cx.env[l], l)),
            _ => None,
        };
        match level {
            Some(l) if !targets.contains(&l) => targets.push(l),
            Some(_) => {
                return Err(motive_error(
                    span,
                    "the arguments of the call in the motive's places must be distinct variables",
                )
                .with_label(a.span(), "this variable is already one of them")
                .with_note(
                    "generalise them first: state the theorem for a fresh variable and apply it",
                ));
            }
            None => {
                return Err(motive_error(
                    span,
                    "the arguments of the call in the motive's places must be distinct variables",
                )
                .with_label(a.span(), "this isn't a variable of the context")
                .with_note(
                    "the motive abstracts them, which a term can't be; generalise them first \
                     (a fixed prefix may be any terms)",
                ));
            }
        }
    }
    // `with ?`: an alternative for every case, naming its binders, whose
    // body is a hole, so each case's goal is listed.
    let listing = alts.is_empty();
    let hole_at = Span::new(outer.file, outer.end.saturating_sub(1), outer.end);
    let synthesized: Vec<InductAlt> = cases
        .iter()
        .enumerate()
        .map(|(arm, (case, own))| {
            let at = |text: &str| stitchwort_syntax::ast::Name {
                text: text.to_string(),
                span: hole_at,
            };
            InductAlt {
                case: at(case),
                binders: own
                    .iter()
                    .map(|n| at(if n.starts_with('%') { "_" } else { n }))
                    .collect(),
                body: Expr::Goal(hole_at),
                span: hole_at,
                arm,
                of: 1,
            }
        })
        .collect();
    let alts: &[InductAlt] = if listing { &synthesized } else { alts };
    same_names_in_each_case(alts)?;
    // The cases of the alternatives.
    let expected: Vec<String> = cases.iter().map(|(n, _)| n.to_string()).collect();
    let mut chosen: Vec<Option<&InductAlt>> = vec![None; cases.len()];
    for alt in alts {
        match cases.iter().position(|(n, _)| **n == *alt.case.text) {
            None => {
                return Err(Diagnostic::error(
                    "E-INDUCT-CASE",
                    format!("`{}` isn't a case of `{}`", alt.case.text, induct_name.text),
                )
                .with_label(alt.case.span, "no case has this name")
                .with_note(format!("the cases are {}", list(&expected))));
            }
            Some(i) => {
                if let Some(first) = chosen[i] {
                    return Err(Diagnostic::error(
                        "E-INDUCT-CASE",
                        format!("the case `{}` has two alternatives", alt.case.text),
                    )
                    .with_label(alt.case.span, "this one")
                    .with_label(first.case.span, "and this one"));
                }
                chosen[i] = Some(alt);
            }
        }
    }
    let missing: Vec<&str> = chosen
        .iter()
        .zip(&expected)
        .filter(|(c, _)| c.is_none())
        .map(|(_, n)| n.as_str())
        .collect();
    if !missing.is_empty() {
        return Err(Diagnostic::error(
            "E-NONEXHAUSTIVE",
            format!(
                "this `match induct` has no alternative for {}",
                list(&missing)
            ),
        )
        .with_label(span, "every case of `f.induct` needs one")
        .with_note(format!("the cases are {}", list(&expected))));
    }
    // The motive.
    let goal_term = quote_unfolded(&g, base, goal)?;
    let type_terms: Vec<Term> = (0..base)
        .map(|l| quote_unfolded(&g, base, &cx.types[l]))
        .collect::<std::result::Result<_, _>>()?;
    // The variables to generalise: those whose types mention the call or a
    // target, and those whose types mention one generalised.
    let mut copied: Vec<usize> = Vec::new();
    for (l, ty) in type_terms.iter().enumerate() {
        if targets.contains(&l) {
            continue;
        }
        let free = free_levels(ty, base);
        let unrefined = is_var(&cx.env[l], l) || cx.lets[l].is_some();
        if unrefined
            && (occurs(&call_normal, ty)
                || free
                    .iter()
                    .any(|f| targets.contains(f) || copied.contains(f)))
        {
            copied.push(l);
        }
    }
    let mark = cx.mark();
    // The statement as written, where the goal is it ([`Ctx::statement`]).
    let stated = (cx.statement.as_ref())
        .filter(|s| s.at == expr.span() && s.level == base)
        .map(|s| s.term.clone());
    let built = (|| -> Result<(Term, Value, Option<Term>)> {
        // The motive's parameters, bound; the targets map onto them.
        let mut cur = (*motive_ty).clone();
        let mut names: Vec<Name> = Vec::new();
        for _ in 0..params.len() {
            let Value::Pi(name, _, dom, cod, _) = force(&g, cur)? else {
                unreachable!("counted")
            };
            cx.bind_hidden(name.clone(), (*dom).clone());
            names.push(name);
            cur = cod.apply(&g, Value::var(cx.level() - 1))?;
        }
        let mut map: HashMap<usize, usize> = HashMap::default();
        for (i, &l) in targets.iter().enumerate() {
            map.insert(l, base + i);
        }
        let result = base + k;
        let mut copy_types: Vec<(Name, Term)> = Vec::new();
        for &l in &copied {
            let depth = cx.level();
            let abs = Abstract {
                base,
                depth,
                call: &call_normal,
                result,
                map: &map,
            };
            let ty = abs.apply(&g, &type_terms[l])?;
            let value = cx.eval(&ty)?;
            cx.bind_hidden(cx.names[l].clone(), value);
            map.insert(l, depth);
            copy_types.push((cx.names[l].clone(), ty));
        }
        let depth = cx.level();
        let abs = Abstract {
            base,
            depth,
            call: &call_normal,
            result,
            map: &map,
        };
        let mut body = abs.apply(&g, &goal_term)?;
        // Only the targets and the premises are replaced: the call stays,
        // with the case's targets in it (`countAbove k [x, ..xs]`).
        let stated_body = stated.as_ref().and_then(|t| {
            let to = |l: usize| Ok(Term::Var(depth - 1 - map.get(&l).copied().unwrap_or(l)));
            lift::replace_with(&g, t, base, &to, &|_, _| None).ok()
        });
        for (name, ty) in copy_types.into_iter().rev() {
            body = Term::Pi(
                name,
                Icit::Explicit,
                Rc::new(ty),
                Rc::new(body),
                ProofMark::Unknown,
            );
        }
        for name in names.into_iter().rev() {
            body = Term::Lam(name, Icit::Explicit, Rc::new(body), ProofMark::Unknown);
        }
        Ok((body, cur, stated_body))
    })();
    cx.reset(mark);
    let (motive_term, _, stated_body) = built?;
    let shape = Shape {
        stated: stated_body,
        base,
        k,
    };
    let motive = cx.eval(&motive_term)?;
    // `f.induct` with the motive; its cases are the alternatives.
    let ty = rest.apply(&g, motive.clone())?;
    let mut term = Term::app(with_prefix, motive_term);
    let mut cur = ty;
    let mut cur_shape = rest_dummy.clone();
    for (i, alt) in chosen.iter().enumerate() {
        let alt = alt.expect("none missing");
        let Value::Pi(_, _, dom, cod, _) = force(&g, cur)? else {
            unreachable!("counted")
        };
        // The same case with an unknown motive: its conclusion keeps the
        // targets the case is for.
        let Value::Pi(_, _, dom_shape, cod_shape, _) = force(&g, cur_shape)? else {
            unreachable!("counted")
        };
        cur_shape = cod_shape.apply(&g, Value::dummy_var())?;
        let shown = (listing || alt.of > 1).then(|| shown_alternative(alt));
        let saved = std::mem::replace(
            &mut cx.e.goals.borrow_mut().alternative,
            shown.as_deref().map(Into::into),
        );
        let case = alternative(
            cx,
            alt,
            &cases[i],
            &induct_name.text,
            (&dom, &dom_shape),
            &copied,
            &shape,
        );
        cx.e.goals.borrow_mut().alternative = saved;
        let case = case.map_err(|e| match &shown {
            Some(shown) if !listing => in_alternative(e, shown, alt),
            _ => e,
        })?;
        cur = cod.apply(&g, cx.eval(&case)?)?;
        term = Term::app(term, case);
    }
    for &l in &targets {
        let Value::Pi(_, _, _, cod, _) = force(&g, cur)? else {
            unreachable!("counted")
        };
        cur = cod.apply(&g, Value::var(l))?;
        term = Term::app(term, Term::Var(base - 1 - l));
    }
    // Applied to the variables the motive took as premises.
    for &l in &copied {
        let Value::Pi(_, _, _, cod, _) = force(&g, cur)? else {
            return Err(motive_error(
                span,
                "the motive's premises aren't as expected",
            ));
        };
        cur = cod.apply(&g, Value::var(l))?;
        term = Term::app(term, Term::Var(base - 1 - l));
    }
    if !cx.unify(&cur, goal)? {
        let shown = crate::pretty::term_for_message_in(
            &g,
            cx.e,
            &cx.shown_names(false),
            &cx.quote_unfolded(&cur)?,
        );
        return Err(motive_error(
            span,
            "the motive worked out from the goal doesn't give the goal back",
        )
        .with_label(call.span(), format!("this call gives `{shown}`"))
        .with_note(
            "the goal mentions the call or its variables where abstracting them isn't \
             type-correct, as `match` on an expression can't generalise either",
        ));
    }
    Ok(term)
}

/// An alternative as written, `` `eq3 _ ih` ``.
fn shown_alternative(alt: &InductAlt) -> String {
    let mut shown = format!("`{}", alt.case.text);
    for b in &alt.binders {
        shown.push(' ');
        shown.push_str(&b.text);
    }
    shown.push('`');
    shown
}

/// `error`, from the body of an arm with several cases, with a note naming
/// the alternative it is in: the body is checked once per case, as an
/// or-pattern's is (D3694).
fn in_alternative(mut error: Diagnostic, shown: &str, alt: &InductAlt) -> Diagnostic {
    if error.code == crate::goals::UNFINISHED
        || crate::undo::fatal(&error)
        || error
            .detail
            .as_ref()
            .is_some_and(|d| d.alternative.is_some())
    {
        return error;
    }
    let note = format!("this error is in the alternative {shown}");
    error.notes.push(note.clone());
    error.detail_mut().alternative = Some(stitchwort_syntax::AlternativeError {
        arm: alt.span,
        shown: vec![shown.to_string()],
        cases: alt.of,
        note,
    });
    error
}

/// Every alternative of an arm with several cases binds the same names
/// (D3694); `_` binds none.
fn bound(alt: &InductAlt) -> Vec<&str> {
    (alt.binders.iter())
        .map(|b| b.text.as_str())
        .filter(|t| *t != "_")
        .collect()
}

fn same_names_in_each_case(alts: &[InductAlt]) -> Result<()> {
    for alt in alts.iter().filter(|a| a.of > 1) {
        let mine = bound(alt);
        for other in alts.iter().filter(|o| o.arm == alt.arm && o.of > 1) {
            if let Some(name) = mine.iter().find(|n| !bound(other).contains(n)) {
                return Err(Diagnostic::error(
                    "E-OR-PATTERN-BINDS",
                    format!(
                        "`{name}` is bound in {} but not in {}",
                        shown_alternative(alt),
                        shown_alternative(other)
                    ),
                )
                .with_label(alt.case.span, format!("`{name}` is bound here"))
                .with_label(other.case.span, "this alternative doesn't bind it")
                .with_note(
                    "every alternative of an arm binds the same names; use `_` in the \
                     alternatives that don't use one",
                ));
            }
        }
    }
    Ok(())
}

/// The statement of a `match induct` as written, with the call and the
/// targets abstracted, to show a case's goal as written.
struct Shape {
    /// In the context of `base` variables, then the motive's parameters
    /// (`k` targets and the result) and the premises it takes.
    stated: Option<Term>,
    base: usize,
    k: usize,
}

impl Shape {
    /// The statement for one case: its targets put in place of the motive's
    /// parameters. `shape` is the case's conclusion for an unknown motive,
    /// `premises` the levels of the premises bound for `copied`. Display only,
    /// so a case it can't be made for has none.
    fn for_case(
        &self,
        cx: &Ctx,
        shape: &Value,
        copied: &[usize],
        premises: &[usize],
        at: Span,
    ) -> Option<crate::check::Statement> {
        let g = cx.g();
        let stated = self.stated.as_ref()?;
        let Value::Neutral(stitchwort_core::value::Head::Var(DUMMY_LEVEL, _, _), spine) =
            force(&g, shape.clone()).ok()?
        else {
            return None;
        };
        let args: Vec<Term> = spine
            .into_vec()
            .into_iter()
            .map(|e| match e {
                stitchwort_core::value::Elim::App(v, _) => cx.quote_folded(&v).ok(),
                _ => None,
            })
            .collect::<Option<_>>()?;
        if args.len() != self.k + 1 {
            return None;
        }
        let depth = cx.level();
        let params = self.base + self.k + 1;
        let term = lift::replace_with(
            &g,
            stated,
            params + copied.len(),
            &|l| {
                let level = if l < self.base {
                    match copied.iter().position(|&c| c == l) {
                        Some(j) => premises[j],
                        None => l,
                    }
                } else if l < params {
                    return Ok(args[l - self.base].clone());
                } else {
                    premises[l - params]
                };
                Ok(Term::Var(depth - 1 - level))
            },
            &|_, _| None,
        )
        .ok()?;
        Some(crate::check::Statement {
            term: Rc::new(term),
            level: depth,
            at,
            outer: None,
        })
    }
}

/// One alternative: its binders, the generalised variables refined, and the
/// body, as a function of both, against the case's type `ty`.
fn alternative(
    cx: &mut Ctx,
    alt: &InductAlt,
    case: &(Name, Vec<Name>),
    induct: &str,
    (ty, shape_ty): (&Value, &Value),
    copied: &[usize],
    shape: &Shape,
) -> Result<Term> {
    let (_, own) = case;
    if alt.binders.len() != own.len() {
        let n = own.len();
        return Err(Diagnostic::error(
            "E-INDUCT-CASE",
            format!(
                "the case `{}` of `{induct}` binds {n} name{}, but this alternative has {}",
                alt.case.text,
                if n == 1 { "" } else { "s" },
                alt.binders.len()
            ),
        )
        .with_label(alt.case.span, format!("binds {}", list(own)))
        .with_note(
            "an alternative names the case's variables, then its hypotheses, then its \
             induction hypotheses, in order; `_` ignores one",
        ));
    }
    let g = cx.g();
    let mark = cx.mark();
    let result = (|| -> Result<Term> {
        let mut lams: Vec<Name> = Vec::new();
        let mut cur = ty.clone();
        let mut cur_shape = shape_ty.clone();
        for b in &alt.binders {
            let Value::Pi(name, _, dom, cod, _) = force(&g, cur)? else {
                unreachable!("counted")
            };
            let shown: Name = if b.text == "_" {
                name
            } else {
                b.text.as_str().into()
            };
            if b.text == "_" {
                cx.bind_hidden(shown.clone(), (*dom).clone());
            } else {
                cx.bind(&b.text, (*dom).clone());
            }
            lams.push(shown);
            cur = cod.apply(&g, Value::var(cx.level() - 1))?;
            if let Value::Pi(_, _, _, cod, _) = force(&g, cur_shape.clone())? {
                cur_shape = cod.apply(&g, Value::var(cx.level() - 1))?;
            }
        }
        let mut premises = Vec::new();
        for &l in copied {
            let Value::Pi(name, _, dom, cod, _) = force(&g, cur)? else {
                return Err(motive_error(
                    alt.span,
                    "the case's premises aren't as the motive made them",
                ));
            };
            cx.bind_hidden(name.clone(), (*dom).clone());
            let level = cx.level() - 1;
            cx.rebind(l, level);
            premises.push(level);
            lams.push(name);
            cur = cod.apply(&g, Value::var(level))?;
        }
        let for_case =
            (shape.for_case(cx, &cur_shape, copied, &premises, alt.body.span())).map(Rc::new);
        let saved = std::mem::replace(&mut cx.statement, for_case);
        let checked = check(cx, &alt.body, &cur);
        cx.statement = saved;
        let mut body = checked?;
        for name in lams.into_iter().rev() {
            body = Term::Lam(name, Icit::Explicit, Rc::new(body), ProofMark::Unknown);
        }
        Ok(body)
    })();
    cx.reset(mark);
    result
}

/// The error for a function without `f.induct`: the reason `E-NO-EQUATION`
/// gives, or that the function isn't recursive.
fn no_induct(d: Diagnostic, function: &str, call: Span) -> Diagnostic {
    let reason = d.labels.first().map(|l| l.message.clone());
    let mut out = Diagnostic::error(
        "E-NO-INDUCT",
        format!("`match induct` needs `{function}.induct`, and `{function}` has none"),
    )
    .with_label(call, "this call");
    out = match (d.code, reason) {
        ("E-NO-EQUATION", Some(why)) => out.with_note(format!("why: {why}")),
        _ => out,
    };
    for note in d.notes {
        out = out.with_note(note);
    }
    out
}
