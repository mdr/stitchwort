//! Implicitly bound variables (DESIGN.md §4, §16).
//!
//! An unknown lowercase name in a signature is bound automatically, as an
//! implicit parameter at the front, if *every* use of it is in a position where
//! a type is expected:
//!
//! - the domain or result of a function type (`a -> b`, `(x : a) -> …`);
//! - a binder's type, `[x : a]`;
//! - an argument of a data type (or a definition whose result is a type)
//!   whose parameter is a type (`List a`, `Or p q`);
//!
//! or is the whole argument of a data type, or of a definition whose result
//! is a type, for a parameter that's a value (Idris's way): `Dial highest`,
//! for `type Dial (highest : Nat) = …`, binds `[highest : Nat]`.
//!
//! The variables are bound in the order of their first uses, each with an
//! unknown type worked out from its uses: usually `Type`, and for a value
//! argument the parameter's type. Uses that disagree are a type mismatch at
//! the later one, with a note saying the name was bound automatically
//! ([`explain`]).
//!
//! Anywhere else (e.g. `length xs` with `xs` unbound, or `Dial (highest + 1)`)
//! it stays an unknown name, so a misspelt value doesn't silently become a
//! new parameter.
//!
//! A name declared anywhere in the module isn't unknown, wherever it's
//! declared: it means that declaration. Such names that would otherwise have
//! been bound are reported, so the elaborator can warn
//! (docs/proposals/mutual-recursion.md §8.1), and so are imported names
//! (docs/proposals/namespaces.md §4.11).

use stitchwort_core::{Icit, Term};
use stitchwort_syntax::Diagnostic;
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
    /// The uses of bound names as a value argument of a type.
    values: Vec<Name>,
}

/// `d`, a failure elaborating the signature, with a note if it's a type
/// mismatch at a bound name used as a value argument of a type: the uses'
/// types disagree.
pub fn explain(auto: &AutoBound, d: Diagnostic) -> Diagnostic {
    let Some(at) = d.labels.first().map(|l| l.span) else {
        return d;
    };
    match auto.values.iter().find(|n| n.span == at) {
        Some(name) if d.code == "E-TYPE-MISMATCH" => d.with_note(format!(
            "`{0}` isn't declared, so it's bound automatically, its type taken from its first \
             use; its uses here need different types. Bind it yourself (`[{0}: …]`), or use \
             different names",
            name.text
        )),
        _ => d,
    }
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
            .all(|u| u.position != Position::Value);
        let found = if use_.module {
            &mut shadowing
        } else {
            &mut names
        };
        if all_types && !found.iter().any(|n| n.text == name.text) {
            found.push(name.clone());
        }
    }
    let values = uses
        .into_iter()
        .filter(|u| u.position == Position::ValueArg && names.iter().any(|n| n.text == u.name.text))
        .map(|u| u.name)
        .collect();
    Ok(AutoBound {
        names,
        shadowing,
        values,
    })
}

/// A use of a name that's a candidate for binding.
struct Use {
    name: Name,
    position: Position,
    /// The name is declared by the module being elaborated.
    module: bool,
}

/// Where a name is used.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    /// Where a type is expected.
    Type,
    /// The whole argument of a type for a parameter that's a value.
    ValueArg,
    /// Anywhere else.
    Value,
}

/// The explicit parameters of the type-former `head` (a data type, an
/// ability, or a definition whose result is a type): for each, whether it's
/// a type. `None` if `head` isn't one.
fn type_former(e: &Elaborator, head: &Expr, bound: &[String]) -> Option<Vec<bool>> {
    let Expr::Var(name) = head else {
        return None;
    };
    if bound.contains(&name.text) {
        return None;
    }
    let is_sort = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(_));
    let data = match e.named(&name.text)? {
        (Global::Data(d), _) => e.globals.data(*d),
        // An ability's parameters are those of its operations' type.
        (Global::Ability(a), _) => e.globals.data(e.abilities[*a].op_data),
        (Global::Def(id), _) => {
            let mut params = Vec::new();
            let mut ty = &e.globals.def(*id).ty;
            while let Term::Pi(_, icit, dom, cod) = ty.strip_loc() {
                if *icit == Icit::Explicit {
                    params.push(is_sort(dom));
                }
                ty = cod;
            }
            return is_sort(ty).then_some(params);
        }
        _ => return None,
    };
    Some(data.params.iter().map(|(_, ty)| is_sort(ty)).collect())
}

fn walk(
    e: &Elaborator,
    expr: &Expr,
    bound: &mut Vec<String>,
    is_type: bool,
    uses: &mut Vec<Use>,
) -> Result<()> {
    walk_at(
        e,
        expr,
        bound,
        if is_type {
            Position::Type
        } else {
            Position::Value
        },
        uses,
    )
}

fn walk_at(
    e: &Elaborator,
    expr: &Expr,
    bound: &mut Vec<String>,
    position: Position,
    uses: &mut Vec<Use>,
) -> Result<()> {
    e.globals.budget.nesting(crate::check::PASS)?;
    let is_type = position == Position::Type;
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
                    level: Level::Import | Level::Wildcard,
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
                    position,
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
            let params = type_former(e, head, bound);
            if params.is_none() {
                walk(e, head, bound, false, uses)?;
            }
            // Named arguments are implicit ones, not among `params`.
            let mut explicit = 0;
            for arg in args {
                let param = match arg {
                    Expr::NamedArg(..) => None,
                    _ => {
                        explicit += 1;
                        params.as_ref().and_then(|p| p.get(explicit - 1))
                    }
                };
                let position = match param {
                    Some(true) => Position::Type,
                    Some(false) if matches!(arg, Expr::Var(_)) => Position::ValueArg,
                    _ => Position::Value,
                };
                walk_at(e, arg, bound, position, uses)?;
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
        Expr::Calc { first, steps, .. } => {
            walk(e, first, bound, false, uses)?;
            for step in steps {
                walk(e, &step.rhs, bound, false, uses)?;
                if let Some(proof) = &step.proof {
                    walk(e, proof, bound, false, uses)?;
                }
            }
        }
        Expr::Rewrite { rules, body, .. } => {
            for rule in rules {
                walk(e, &rule.proof, bound, false, uses)?;
            }
            if let Some(body) = body {
                walk(e, body, bound, false, uses)?;
            }
        }
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
        | Pattern::Char(..)
        | Pattern::Nil(_) => {}
    }
}
