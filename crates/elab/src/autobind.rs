//! Implicitly bound type variables (DESIGN.md §4, §16).
//!
//! An unknown lowercase name in a signature is bound automatically, as an
//! implicit parameter at the front, if *every* use of it is in a position where
//! a type is expected:
//!
//! - the domain or result of a function type (`a -> b`, `(x : a) -> …`);
//! - a binder's type, `[x : a]`;
//! - an argument of a data type whose parameter is a type (`List a`, `Or p q`).
//!
//! Anywhere else (e.g. `length xs` with `xs` unbound) it stays an unknown name,
//! so a misspelt value doesn't silently become a new parameter.

use stitchwort_core::Term;
use stitchwort_syntax::ast::{Expr, Name};

use crate::{Elaborator, Global, RESERVED};

pub fn auto_bound(e: &Elaborator, ty: &Expr) -> Vec<Name> {
    let mut uses = Vec::new();
    walk(e, ty, &mut Vec::new(), true, &mut uses);
    let mut names: Vec<Name> = Vec::new();
    for (name, _) in &uses {
        let all_types = uses
            .iter()
            .filter(|(n, _)| n.text == name.text)
            .all(|(_, type_position)| *type_position);
        if all_types && !names.iter().any(|n| n.text == name.text) {
            names.push(name.clone());
        }
    }
    names
}

fn walk(
    e: &Elaborator,
    expr: &Expr,
    bound: &mut Vec<String>,
    is_type: bool,
    uses: &mut Vec<(Name, bool)>,
) {
    match expr {
        Expr::Var(name) => {
            let candidate = name.text.starts_with(|c: char| c.is_ascii_lowercase())
                && !bound.contains(&name.text)
                && !e.names.contains_key(&name.text)
                && !RESERVED.contains(&name.text.as_str());
            if candidate {
                uses.push((name.clone(), is_type));
            }
        }
        Expr::App(..) => {
            let mut args = Vec::new();
            let mut head = expr;
            while let Expr::App(f, a) = head {
                args.push(a.as_ref());
                head = f;
            }
            args.reverse();
            let data = match head {
                Expr::Var(name) if !bound.contains(&name.text) => match e.names.get(&name.text) {
                    Some((Global::Data(d), _)) => Some(e.globals.data(*d)),
                    // An ability's parameters are those of its operations' type.
                    Some((Global::Ability(a), _)) => Some(e.globals.data(e.abilities[*a].op_data)),
                    _ => None,
                },
                _ => None,
            };
            if data.is_none() {
                walk(e, head, bound, false, uses);
            }
            for (i, arg) in args.iter().enumerate() {
                let type_param = data.is_some_and(|d| {
                    d.params
                        .get(i)
                        .is_some_and(|(_, ty)| matches!(ty.strip_loc(), Term::Sort(_)))
                });
                walk(e, arg, bound, type_param, uses);
            }
        }
        Expr::Pi {
            names, dom, cod, ..
        } => {
            walk(e, dom, bound, true, uses);
            let before = bound.len();
            bound.extend(names.iter().map(|n| n.text.clone()));
            walk(e, cod, bound, true, uses);
            bound.truncate(before);
        }
        Expr::Arrow(a, b) => {
            walk(e, a, bound, true, uses);
            walk(e, b, bound, true, uses);
        }
        Expr::Lam(names, body, _) => {
            let before = bound.len();
            bound.extend(names.iter().map(|n| n.text.clone()));
            walk(e, body, bound, false, uses);
            bound.truncate(before);
        }
        Expr::Binary(_, a, b) => {
            walk(e, a, bound, false, uses);
            walk(e, b, bound, false, uses);
        }
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            // With a binder, the condition is a proposition: a type position.
            walk(e, cond, bound, binder.is_some(), uses);
            let before = bound.len();
            bound.extend(binder.iter().map(|n| n.text.clone()));
            walk(e, then, bound, false, uses);
            walk(e, otherwise, bound, false, uses);
            bound.truncate(before);
        }
        Expr::Ann(x, ty, _) => {
            walk(e, x, bound, false, uses);
            walk(e, ty, bound, true, uses);
        }
        Expr::List(items, _) => {
            for item in items {
                walk(e, item, bound, false, uses);
            }
        }
        Expr::NamedArg(_, value, _) => walk(e, value, bound, false, uses),
        Expr::Num(..)
        | Expr::Char(..)
        | Expr::Type(..)
        | Expr::Prop(_)
        | Expr::Hole(_)
        | Expr::Unit(_) => {}
        // `{State s | e} b`: `e` is a row variable, bound like a type.
        Expr::Effect(row, ty) => {
            for ability in &row.abilities {
                walk(e, ability, bound, true, uses);
            }
            if let Some(tail) = &row.tail {
                walk(e, &Expr::Var(tail.clone()), bound, true, uses);
            }
            walk(e, ty, bound, true, uses);
        }
        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            if let Some(ty) = ty {
                walk(e, ty, bound, true, uses);
            }
            walk(e, value, bound, false, uses);
            bound.push(name.text.clone());
            walk(e, body, bound, false, uses);
            bound.pop();
        }
        Expr::Seq(a, b) => {
            walk(e, a, bound, false, uses);
            walk(e, b, bound, false, uses);
        }
        Expr::Handle { body, clauses, .. } => {
            walk(e, body, bound, false, uses);
            for clause in clauses {
                let before = bound.len();
                let body = match clause {
                    stitchwort_syntax::ast::Clause::Return { var, body } => {
                        bound.push(var.text.clone());
                        body
                    }
                    stitchwort_syntax::ast::Clause::Op { arg, k, body, .. } => {
                        if let stitchwort_syntax::ast::Pattern::Var(x) = arg {
                            bound.push(x.text.clone());
                        }
                        bound.push(k.text.clone());
                        body
                    }
                };
                walk(e, body, bound, false, uses);
                bound.truncate(before);
            }
        }
    }
}
