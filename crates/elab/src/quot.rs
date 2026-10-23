//! The quotient forms' surface names (docs/proposals/map-equality.md §7.1):
//!
//! ```text
//! Quot a r
//! Quot.mk    [a] [r] value
//! Quot.lift  [a] [r] [b] f respects q
//! Quot.ind   [a] [r] [p] h q
//! Quot.sound [a] [r] [x] [y] related
//! ```
//!
//! (The note's `A`, `R`, `B` and `P`, named in lower case as every implicit
//! parameter is: a named argument is written `[a := Nat]`.)
//!
//! Built in, like `J`: each elaborates to the kernel's term former
//! (`Term::Quot`) applied to all its arguments, so each is written applied
//! to all its explicit ones. The bracketed arguments are implicit: given by
//! name (`Quot.ind [p := q => …] h q`), or found by unification, from the
//! expected type and the explicit arguments. They're elaborated in an order
//! that lets each be found from what's already known: a lift's quotient
//! before its function (whose parameter type it gives), and a `sound` against
//! the equation it's expected to prove. Nothing here is trusted: the kernel
//! checks every form (checks C1–C6).

use std::rc::Rc;

use stitchwort_core::term::QuotForm;
use stitchwort_core::{Icit, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::Expr;

use crate::check::{Arg, Ctx, check, check_type};

type Result<T> = std::result::Result<T, Diagnostic>;

/// The names of a form's implicit parameters, in order (§7.1).
fn implicit_names(form: QuotForm) -> &'static [&'static str] {
    match form {
        QuotForm::Type => &[],
        QuotForm::Mk => &["a", "r"],
        QuotForm::Lift => &["a", "r", "b"],
        QuotForm::Ind => &["a", "r", "p"],
        QuotForm::Sound => &["a", "r", "x", "y"],
    }
}

/// What a form's explicit arguments are, for messages.
fn explicit_description(form: QuotForm) -> &'static str {
    match form {
        QuotForm::Type => "2 arguments: a type and a relation on it",
        QuotForm::Mk => "1 argument: the value it represents",
        QuotForm::Lift => {
            "3 arguments: a function, a proof that it respects the relation, and a quotient"
        }
        QuotForm::Ind => "2 arguments: a proof for every `Quot.mk x`, and a quotient",
        QuotForm::Sound => "1 argument: a proof that the two values are related",
    }
}

/// The quotient form `name` stands for, unless a variable in scope or a
/// local definition is called `Quot`.
fn form_named(cx: &Ctx, name: &str) -> Option<QuotForm> {
    let form = QuotForm::from_name(name)?;
    let first = name.split('.').next()?;
    (cx.lookup(first).is_none() && !cx.has_local(first)).then_some(form)
}

/// If `expr` is a quotient form applied to arguments: the form and the
/// arguments, as written.
pub(crate) fn applied<'e>(cx: &Ctx, expr: &'e Expr) -> Option<(QuotForm, Vec<Arg<'e>>)> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(match a.as_ref() {
            Expr::NamedArg(name, value, _) => Arg::Named(name, value),
            other => Arg::Explicit(other),
        });
        head = f;
    }
    let Expr::Var(name) = head else {
        return None;
    };
    let form = form_named(cx, &name.text)?;
    args.reverse();
    Some((form, args))
}

/// The form `name` is, if it's one (for `infer_app`).
pub(crate) fn head_form(cx: &Ctx, name: &str) -> Option<QuotForm> {
    form_named(cx, name)
}

/// Elaborates quotient form `form` applied to `args`; `expected` is the type
/// it's checked against, if any (then only a hint: the caller compares).
pub(crate) fn elaborate(
    cx: &mut Ctx,
    form: QuotForm,
    args: &[Arg],
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let names = implicit_names(form);
    let mut named: Vec<Option<&Expr>> = vec![None; names.len()];
    let mut explicit = Vec::new();
    for arg in args {
        match arg {
            Arg::Explicit(e) => explicit.push(*e),
            Arg::Named(name, e) => match names.iter().position(|n| **n == *name.text) {
                Some(i) if named[i].is_none() => named[i] = Some(e),
                Some(_) => {
                    return Err(Diagnostic::error(
                        "E-ARITY",
                        format!("`[{} := …]` is given twice", name.text),
                    )
                    .with_label(name.span, "given again here"));
                }
                None => {
                    let listed: Vec<String> = names.iter().map(|n| format!("[{n}]")).collect();
                    return Err(Diagnostic::error(
                        "E-UNKNOWN-NAME",
                        format!("no implicit parameter named `{}` here", name.text),
                    )
                    .with_label(name.span, "not an implicit parameter of this function")
                    .with_note(if listed.is_empty() {
                        format!("`{}` has no implicit parameters", form.name())
                    } else {
                        format!(
                            "`{}`'s implicit parameters are {}",
                            form.name(),
                            listed.join(" ")
                        )
                    }));
                }
            },
            Arg::Piped(_) => {
                return Err(cx.error(
                    "E-ARITY",
                    format!("`{}` can't take a piped argument", form.name()),
                    "write its arguments after it",
                ));
            }
        }
    }
    if explicit.len() != form.arity() - form.implicit() {
        return Err(cx.error(
            "E-ARITY",
            format!("`{}` takes {}", form.name(), explicit_description(form)),
            format!("here it has {}", explicit.len()),
        ));
    }
    let g = cx.g();
    let shift = |t: &Term, by: usize| t.shift(g, by, 0);
    let pi = |x: &str, dom: Term, cod: Term| {
        Term::Pi(x.into(), Icit::Explicit, Rc::new(dom), Rc::new(cod))
    };
    let rc = Rc::new;
    // The carrier and the relation: given (as implicit or, for `Quot A R`,
    // explicit arguments), or unknowns.
    let (carrier_expr, relation_expr) = match form {
        QuotForm::Type => (Some(explicit[0]), Some(explicit[1])),
        _ => (named[0], named[1]),
    };
    let (carrier, sort) = match carrier_expr {
        Some(e) => {
            let (t, sort) = check_type(cx, e)?;
            if sort == Sort::Prop {
                let shown = cx.show(&cx.eval(&t)?);
                return Err(cx.error(
                    "E-UNIVERSE",
                    "a quotient of a proposition",
                    format!(
                        "the carrier of a quotient must be a type in `Type`, but `{shown}` is a \
                         proposition"
                    ),
                ));
            }
            (t, Some(sort))
        }
        None => (cx.fresh_meta(), None),
    };
    let relation = match relation_expr {
        Some(e) => {
            let ty = pi(
                "x",
                carrier.clone(),
                pi("y", shift(&carrier, 1)?, Term::Sort(Sort::Prop)),
            );
            let ty = cx.eval(&ty)?;
            check(cx, e, &ty)?
        }
        None => cx.fresh_meta(),
    };
    let quot_ty = Term::Quot(
        QuotForm::Type,
        vec![rc(carrier.clone()), rc(relation.clone())],
        false,
    );
    let quot_ty_value = cx.eval(&quot_ty)?;
    let hint = |cx: &mut Ctx, found: &Value| -> Result<()> {
        if let Some(expected) = expected {
            crate::undo::unify(cx, found, expected)?;
        }
        Ok(())
    };
    let quot = |args: Vec<Term>| {
        Term::Quot(
            form,
            [carrier.clone(), relation.clone()]
                .into_iter()
                .chain(args)
                .map(Rc::new)
                .collect(),
            false,
        )
    };
    match form {
        QuotForm::Type => {
            let sort = sort.expect("`Quot A R`'s carrier is given");
            Ok((quot(vec![]), Value::Sort(sort)))
        }
        QuotForm::Mk => {
            hint(cx, &quot_ty_value)?;
            let a = check(cx, explicit[0], &cx.eval(&carrier)?)?;
            Ok((quot(vec![a]), quot_ty_value))
        }
        QuotForm::Lift => {
            let result = match named[2] {
                Some(e) => check_type(cx, e)?.0,
                None => cx.fresh_meta(),
            };
            let result_value = cx.eval(&result)?;
            hint(cx, &result_value)?;
            // The quotient first: its type says what the function takes.
            let q = check(cx, explicit[2], &quot_ty_value)?;
            let f_ty = pi("x", carrier.clone(), shift(&result, 1)?);
            let f_ty = cx.eval(&f_ty)?;
            let f = check(cx, explicit[0], &f_ty)?;
            // (x: A) -> (y: A) -> R x y -> f x = f y
            let f3 = shift(&f, 3)?;
            let respects = pi(
                "x",
                carrier.clone(),
                pi(
                    "y",
                    shift(&carrier, 1)?,
                    pi(
                        "related",
                        Term::app(Term::app(shift(&relation, 2)?, Term::Var(1)), Term::Var(0)),
                        Term::Eq(
                            Some(rc(shift(&result, 3)?)),
                            rc(Term::app(f3.clone(), Term::Var(2))),
                            rc(Term::app(f3, Term::Var(1))),
                        ),
                    ),
                ),
            );
            let respects = cx.eval(&respects)?;
            let h = check(cx, explicit[1], &respects)?;
            Ok((quot(vec![result, f, h, q]), result_value))
        }
        QuotForm::Ind => {
            // The quotient first, which settles the carrier and relation.
            let q = check(cx, explicit[1], &quot_ty_value)?;
            let Some(motive) = named[2] else {
                return Err(cx
                    .error(
                        "E-CANNOT-INFER",
                        "can't work out what `Quot.ind` proves",
                        "give its motive: `Quot.ind [p := q => …] h q`",
                    )
                    .with_note("`p q` is the proposition proved about the quotient `q`"));
            };
            let motive_ty = pi("q", quot_ty.clone(), Term::Sort(Sort::Prop));
            let motive_ty = cx.eval(&motive_ty)?;
            let motive = check(cx, motive, &motive_ty)?;
            // (x: A) -> P (Quot.mk x)
            let mk = Term::Quot(
                QuotForm::Mk,
                vec![
                    rc(shift(&carrier, 1)?),
                    rc(shift(&relation, 1)?),
                    rc(Term::Var(0)),
                ],
                false,
            );
            let case_ty = pi("x", carrier.clone(), Term::app(shift(&motive, 1)?, mk));
            let case_ty = cx.eval(&case_ty)?;
            let h = check(cx, explicit[0], &case_ty)?;
            let ty = cx.eval(&Term::app(motive.clone(), q.clone()))?;
            Ok((quot(vec![motive, h, q]), ty))
        }
        QuotForm::Sound => {
            let carrier_value = cx.eval(&carrier)?;
            let end = |cx: &mut Ctx, e: Option<&Expr>| -> Result<Term> {
                match e {
                    Some(e) => check(cx, e, &carrier_value),
                    None => Ok(cx.fresh_meta()),
                }
            };
            let x = end(cx, named[2])?;
            let y = end(cx, named[3])?;
            let mk = |v: &Term| {
                rc(Term::Quot(
                    QuotForm::Mk,
                    vec![rc(carrier.clone()), rc(relation.clone()), rc(v.clone())],
                    false,
                ))
            };
            let equation = Term::Eq(Some(rc(quot_ty.clone())), mk(&x), mk(&y));
            let equation = cx.eval(&equation)?;
            hint(cx, &equation)?;
            let related = Term::app(Term::app(relation.clone(), x.clone()), y.clone());
            let related = cx.eval(&related)?;
            let r = check(cx, explicit[0], &related)?;
            Ok((quot(vec![x, y, r]), equation))
        }
    }
}
