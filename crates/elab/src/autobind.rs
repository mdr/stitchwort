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
//!
//! A name declared anywhere in the module isn't unknown, wherever it's
//! declared: it means that declaration. Such names that would otherwise have
//! been bound are reported, so the elaborator can warn
//! (docs/proposals/mutual-recursion.md §8.1), and so are imported names
//! (docs/proposals/namespaces.md §4.11).

use stitchwort_core::Term;
use stitchwort_syntax::ast::{Expr, Name};

use stitchwort_core::ResourceError;

use crate::scope::{Level, Resolved};
use crate::{Elaborator, Global, RESERVED};

type Result<T> = std::result::Result<T, ResourceError>;

/// The implicitly bound names of a signature, and the names of this module
/// that would have been bound if they weren't declared by it.
pub struct AutoBound {
    pub names: Vec<Name>,
    /// The first use of each.
    pub shadowing: Vec<Name>,
}

pub fn auto_bound(e: &Elaborator, ty: &Expr) -> Result<AutoBound> {
    auto_bound_in(e, ty, Vec::new())
}

/// [`auto_bound`] for a signature where the names `bound` are already in
/// scope (a local definition's): those mean what they already mean
/// (docs/proposals/syntax-conveniences.md §3.1).
pub fn auto_bound_in(e: &Elaborator, ty: &Expr, mut bound: Vec<String>) -> Result<AutoBound> {
    let mut uses = Vec::new();
    walk(e, ty, &mut bound, true, &mut uses)?;
    let mut names: Vec<Name> = Vec::new();
    let mut shadowing: Vec<Name> = Vec::new();
    for use_ in &uses {
        let name = &use_.name;
        let all_types = uses
            .iter()
            .filter(|u| u.name.text == name.text)
            .all(|u| u.type_position);
        let found = if use_.module {
            &mut shadowing
        } else {
            &mut names
        };
        if all_types && !found.iter().any(|n| n.text == name.text) {
            found.push(name.clone());
        }
    }
    Ok(AutoBound { names, shadowing })
}

/// A use of a name that's a candidate for binding.
struct Use {
    name: Name,
    type_position: bool,
    /// The name is declared by the module being elaborated.
    module: bool,
}

fn walk(
    e: &Elaborator,
    expr: &Expr,
    bound: &mut Vec<String>,
    is_type: bool,
    uses: &mut Vec<Use>,
) -> Result<()> {
    e.globals.budget.nesting(crate::check::PASS)?;
    match expr {
        Expr::Var(name) => {
            let candidate = name.text.starts_with(|c: char| c.is_ascii_lowercase())
                && !bound.contains(&name.text)
                && !RESERVED.contains(&name.text.as_str());
            // A name of this module's, or an imported one, means that
            // declaration, which is worth a warning; a default name just
            // means it.
            let (module, unknown) = match e.resolve(&name.text) {
                Resolved::Found {
                    level: Level::Import,
                    ..
                } => (true, false),
                Resolved::Found {
                    level: Level::Module,
                    key,
                    ..
                } => (e.module.names.contains(key), false),
                Resolved::Missing => (false, true),
                _ => (false, false),
            };
            if candidate && (module || unknown) {
                uses.push(Use {
                    name: name.clone(),
                    type_position: is_type,
                    module,
                });
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
                Expr::Var(name) if !bound.contains(&name.text) => match e.named(&name.text) {
                    Some((Global::Data(d), _)) => Some(e.globals.data(*d)),
                    // An ability's parameters are those of its operations' type.
                    Some((Global::Ability(a), _)) => Some(e.globals.data(e.abilities[*a].op_data)),
                    _ => None,
                },
                _ => None,
            };
            if data.is_none() {
                walk(e, head, bound, false, uses)?;
            }
            for (i, arg) in args.iter().enumerate() {
                let type_param = data.is_some_and(|d| {
                    d.params
                        .get(i)
                        .is_some_and(|(_, ty)| matches!(ty.strip_loc(), Term::Sort(_)))
                });
                walk(e, arg, bound, type_param, uses)?;
            }
        }
        Expr::Pi {
            names, dom, cod, ..
        } => {
            walk(e, dom, bound, true, uses)?;
            let before = bound.len();
            bound.extend(names.iter().map(|n| n.text.clone()));
            walk(e, cod, bound, true, uses)?;
            bound.truncate(before);
        }
        Expr::Arrow(a, b) => {
            walk(e, a, bound, true, uses)?;
            walk(e, b, bound, true, uses)?;
        }
        Expr::Lam(names, body, _) => {
            let before = bound.len();
            bound.extend(names.iter().map(|n| n.text.clone()));
            walk(e, body, bound, false, uses)?;
            bound.truncate(before);
        }
        Expr::Binary(_, a, b) => {
            walk(e, a, bound, false, uses)?;
            walk(e, b, bound, false, uses)?;
        }
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            // With a binder, the condition is a proposition: a type position.
            walk(e, cond, bound, binder.is_some(), uses)?;
            let before = bound.len();
            bound.extend(binder.iter().map(|n| n.text.clone()));
            walk(e, then, bound, false, uses)?;
            walk(e, otherwise, bound, false, uses)?;
            bound.truncate(before);
        }
        Expr::Ann(x, ty, _) => {
            walk(e, x, bound, false, uses)?;
            walk(e, ty, bound, true, uses)?;
        }
        // The components are types or values, as the tuple is; auto-bound
        // names are only sought where it is a type.
        Expr::Tuple(a, b, _) => {
            walk(e, a, bound, is_type, uses)?;
            walk(e, b, bound, is_type, uses)?;
        }
        Expr::List(items, _) => {
            for item in items {
                walk(e, item, bound, false, uses)?;
            }
        }
        Expr::Record { base, fields, .. } => {
            if let Some(base) = base {
                walk(e, base, bound, false, uses)?;
            }
            for (_, value) in fields {
                walk(e, value, bound, false, uses)?;
            }
        }
        Expr::Field(x, _) => walk(e, x, bound, false, uses)?,
        Expr::NamedArg(_, value, _) => walk(e, value, bound, false, uses)?,
        Expr::Neg(x, _) => walk(e, x, bound, false, uses)?,
        Expr::Num(..)
        | Expr::Char(..)
        | Expr::Str(..)
        | Expr::Type(..)
        | Expr::Prop(_)
        | Expr::Hole(_)
        | Expr::Unit(_) => {}
        // `{State s | e} b`: `e` is a row variable, bound like a type.
        Expr::Effect(row, ty) => {
            for ability in &row.abilities {
                walk(e, ability, bound, true, uses)?;
            }
            if let Some(tail) = &row.tail {
                walk(e, &Expr::Var(tail.clone()), bound, true, uses)?;
            }
            walk(e, ty, bound, true, uses)?;
        }
        Expr::Let {
            name,
            ty,
            value,
            body,
            ..
        } => {
            if let Some(ty) = ty {
                walk(e, ty, bound, true, uses)?;
            }
            walk(e, value, bound, false, uses)?;
            bound.push(name.text.clone());
            walk(e, body, bound, false, uses)?;
            bound.pop();
        }
        Expr::LocalDefs { defs, body, .. } => {
            let before = bound.len();
            for def in defs {
                if let stitchwort_syntax::ast::Decl::Signature { name, .. } = &def.signature {
                    bound.push(name.text.clone());
                }
            }
            walk(e, body, bound, false, uses)?;
            bound.truncate(before);
        }
        Expr::Seq(a, b) | Expr::Pipe(a, b) => {
            walk(e, a, bound, false, uses)?;
            walk(e, b, bound, false, uses)?;
        }
        Expr::Match {
            scrutinees, alts, ..
        } => {
            for s in scrutinees {
                walk(e, &s.expr, bound, false, uses)?;
            }
            for alt in alts {
                let before = bound.len();
                for p in &alt.patterns {
                    pattern_vars(p, bound);
                }
                walk(e, &alt.body, bound, false, uses)?;
                bound.truncate(before);
            }
        }
        Expr::Handle { body, clauses, .. } => {
            walk(e, body, bound, false, uses)?;
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
                walk(e, body, bound, false, uses)?;
                bound.truncate(before);
            }
        }
    }
    Ok(())
}

/// The variables a pattern binds, pushed onto `out`.
fn pattern_vars(pattern: &stitchwort_syntax::ast::Pattern, out: &mut Vec<String>) {
    use stitchwort_syntax::ast::Pattern;
    match pattern {
        Pattern::Var(x) => out.push(x.text.clone()),
        Pattern::Ctor(_, args, _) => args.iter().for_each(|p| pattern_vars(p, out)),
        Pattern::Tuple(a, b, _) => {
            pattern_vars(a, out);
            pattern_vars(b, out);
        }
        Pattern::Cons(a, b, _) => {
            pattern_vars(a, out);
            pattern_vars(b, out);
        }
        Pattern::Record { fields, .. } => fields.iter().for_each(|(_, p)| pattern_vars(p, out)),
        Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Nil(_) => {}
    }
}
