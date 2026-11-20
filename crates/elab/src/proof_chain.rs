//! `W-PROOF-CHAIN` (D3656, docs/research/readable-proofs.md R1): a proof
//! that chains equalities by nesting `trans`, `Eq.trans a (Eq.trans b c)`
//! or `(a.trans b).trans c`, where a `calc` would state each intermediate
//! term.
//!
//! It is found in the written syntax of a declaration's body, so the
//! `Eq.trans` a `calc` or a `rewrite` produces never counts. Only the
//! outermost call of a nest is reported, once. The shape counts, not the
//! layout: a nest that fits on one line warns too (SW-3697).

use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Decl, Expr, Guard};

use crate::check::{Arg, spine};

pub(crate) const CODE: &str = "W-PROOF-CHAIN";

/// The operands of `e` if it is a call of `trans`: the proofs it joins.
fn trans_operands(e: &Expr) -> Option<Vec<&Expr>> {
    let mut e = e;
    while let Expr::Bracketed(inner, _) = e {
        e = inner;
    }
    let (head, args) = match e {
        Expr::Pipe(left, right) => {
            let (head, mut args) = spine(right);
            args.insert(0, Arg::Explicit(left));
            (head, args)
        }
        _ => spine(e),
    };
    let mut operands: Vec<&Expr> = args
        .iter()
        .filter_map(|a| match a {
            Arg::Explicit(x) | Arg::NamedExplicit(_, x) => Some(*x),
            _ => None,
        })
        .collect();
    match head {
        Expr::Var(name) if name.text == "Eq.trans" || name.text.ends_with(".trans") => {}
        Expr::Field(receiver, name) if name.text == "trans" => operands.insert(0, receiver),
        _ => return None,
    }
    Some(operands)
}

/// Whether `e`, however it is bracketed or ascribed, is a call of `trans`.
fn is_trans(e: &Expr) -> bool {
    match e {
        Expr::Bracketed(inner, _) | Expr::Ann(inner, _, _) => is_trans(inner),
        _ => trans_operands(e).is_some_and(|ops| !ops.is_empty()),
    }
}

/// The warnings for the bodies of `equations`.
pub(crate) fn warnings(equations: &[Decl]) -> Vec<Diagnostic> {
    let mut out = Vec::new();
    // Each expression with whether it is inside a `trans` call already
    // reported (or about to be).
    let mut stack: Vec<(&Expr, bool)> = Vec::new();
    for equation in equations {
        if let Decl::Equation { guard, rhs, .. } = equation {
            if let Some(Guard { cond, .. }) = guard {
                stack.push((cond, false));
            }
            if let Some(rhs) = rhs {
                stack.push((rhs, false));
            }
        }
    }
    let mut children: Vec<&Expr> = Vec::new();
    while let Some((e, inside)) = stack.pop() {
        let trans = is_trans(e) && !matches!(e, Expr::Bracketed(..) | Expr::Ann(..));
        if trans && !inside {
            let nested = trans_operands(e).is_some_and(|ops| ops.iter().any(|o| is_trans(o)));
            if nested {
                out.push(diagnostic(e));
            }
        }
        children.clear();
        sub_expressions(e, &mut children);
        stack.extend(children.iter().map(|c| (*c, trans && is_trans(c))));
    }
    out.sort_by_key(|d| d.labels.first().map_or(0, |l| l.span.start));
    out
}

fn diagnostic(e: &Expr) -> Diagnostic {
    Diagnostic::warning(
        CODE,
        "a chain of equalities is written with `trans` nested; a `calc` states each step",
    )
    .with_label(e.span(), "write this chain as a `calc`")
    .with_note(
        "`calc a` followed by one line `_ = b := proof` per step names every intermediate term, \
         so a broken step is reported on its own line, and the goal at each step can be read \
         (docs/proving-guide.md, \"State, don't chain\")",
    )
}

/// The expressions directly inside `e`.
pub(crate) fn sub_expressions<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match e {
        Expr::Var(_)
        | Expr::Num(..)
        | Expr::Float(..)
        | Expr::Str(..)
        | Expr::Include(..)
        | Expr::Char(..)
        | Expr::Type(..)
        | Expr::Prop(_)
        | Expr::Hole(_)
        | Expr::Goal(_)
        | Expr::Missing(_)
        | Expr::Unit(_) => {}
        Expr::App(a, b)
        | Expr::Arrow(a, b)
        | Expr::Pipe(a, b)
        | Expr::Seq(a, b)
        | Expr::Binary(_, a, b)
        | Expr::Ann(a, b, _)
        | Expr::Tuple(a, b, _) => out.extend([&**a, &**b]),
        Expr::Bracketed(a, _)
        | Expr::Lam(_, a, _)
        | Expr::Neg(a, _, _)
        | Expr::Interpolated(a, _)
        | Expr::Spread(a, _)
        | Expr::NamedArg(_, a, _, _)
        | Expr::Field(a, _) => out.push(a),
        Expr::TypedLam(_, _, ty, body, _) => out.extend([&**ty, &**body]),
        Expr::Pi { dom, cod, .. } => out.extend([&**dom, &**cod]),
        Expr::Effect(row, body) => {
            out.extend(row.abilities.iter());
            out.push(body);
        }
        Expr::If {
            cond,
            then,
            otherwise,
            ..
        } => out.extend([&**cond, &**then, &**otherwise]),
        Expr::List(items, _) => out.extend(items.iter()),
        Expr::Let {
            ty, value, body, ..
        } => {
            out.extend(ty.as_deref());
            out.extend([&**value, &**body]);
        }
        Expr::LocalDefs { defs, body, .. } => {
            for def in defs {
                for decl in std::iter::once(&def.signature).chain(&def.equations) {
                    if let Decl::Equation { guard, rhs, .. } = decl {
                        out.extend(guard.iter().map(|g| &g.cond));
                        out.extend(rhs.iter());
                    }
                }
            }
            out.push(body);
        }
        Expr::Handle { body, clauses, .. } => {
            out.push(body);
            clause_bodies(clauses, out);
        }
        Expr::Reify { thunk, clauses, .. } => {
            out.push(thunk);
            clause_bodies(clauses, out);
        }
        Expr::Induct { call, alts, .. } => {
            out.push(call);
            out.extend(alts.iter().map(|a| &a.body));
        }
        Expr::Match {
            scrutinees, alts, ..
        } => {
            out.extend(scrutinees.iter().map(|s| &s.expr));
            for alt in alts {
                out.extend(alt.guard.iter().map(|g| &g.cond));
                out.extend(alt.body.iter());
            }
        }
        Expr::Record { base, fields, .. } => {
            out.extend(base.as_deref());
            out.extend(fields.iter().map(|(_, v)| v));
        }
        Expr::CtorFields { fields, .. } => out.extend(fields.iter().map(|(_, v)| v)),
        Expr::Calc { first, steps, .. } => {
            out.push(first);
            for step in steps {
                out.push(&step.rhs);
                out.extend(step.proof.iter());
            }
        }
        Expr::Rewrite {
            rules,
            target,
            body,
            ..
        } => {
            out.extend(rules.iter().map(|r| &r.proof));
            out.extend(target.as_deref());
            out.extend(body.as_deref());
        }
        Expr::Omega { facts, .. } | Expr::Ring { facts, .. } => out.extend(facts.iter()),
        Expr::Cases { body, .. } => out.extend(body.as_deref()),
        Expr::Walk(w) => out.extend(w.items.iter().chain(&w.body)),
    }
}

fn clause_bodies<'a>(clauses: &'a [stitchwort_syntax::ast::Clause], out: &mut Vec<&'a Expr>) {
    use stitchwort_syntax::ast::Clause;
    for clause in clauses {
        match clause {
            Clause::Return { body, .. } | Clause::Op { body, .. } => out.push(body),
        }
    }
}
