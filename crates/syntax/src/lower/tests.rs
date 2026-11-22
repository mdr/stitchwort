//! The parser and the lowering together, through the entry points: source
//! text in, the compiler's tree (or the errors) out. Grammar alone is
//! pinned by the tree dumps in `parser/tests.rs`; what these pin is what a
//! construct means once lowered, and the messages the front end gives, whichever
//! of the two finds the problem.

use crate::ast::*;
use crate::parser::*;
use crate::tree::RecoveryPoint;
use crate::{Diagnostic, SourceMap, Span};

type Result<T> = std::result::Result<T, Box<Diagnostic>>;

fn parse(text: &str) -> Module {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    parse_module(file, text).unwrap_or_else(|errors| panic!("{errors:?}"))
}

fn expression(text: &str) -> std::result::Result<Expr, Diagnostic> {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    parse_expression(file, text)
}

fn expr(text: &str) -> Expr {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    parse_expression(file, text).unwrap_or_else(|e| panic!("{e:?}"))
}

/// The right-hand side of the only equation in `text`.
fn rhs(text: &str) -> Expr {
    match parse(text)
        .decls
        .into_iter()
        .find(|d| matches!(d, Decl::Equation { .. }))
    {
        Some(Decl::Equation { rhs: Some(rhs), .. }) => rhs,
        other => panic!("expected an equation, got {other:?}"),
    }
}

/// The block's lines, as `let x` or `_` for an expression, then the result.
fn lines(mut e: &Expr) -> Vec<String> {
    let mut out = Vec::new();
    loop {
        match e {
            Expr::Let { name, body, .. } => {
                out.push(format!("let {}", name.text));
                e = body;
            }
            Expr::Seq(_, rest) => {
                out.push("_".into());
                e = rest;
            }
            _ => {
                out.push("result".into());
                return out;
            }
        }
    }
}

fn match_parts(e: &Expr) -> (&[Scrutinee], &[Alt]) {
    let Expr::Match {
        scrutinees, alts, ..
    } = e
    else {
        panic!("expected a `match`, got {e:?}");
    };
    (scrutinees, alts)
}

/// The alternatives of an or-pattern.
fn or_alternatives(p: &Pattern) -> &[Pattern] {
    let Pattern::Or(alternatives, _) = p else {
        panic!("expected an or-pattern, got {p:?}");
    };
    alternatives
}

/// The `match` of a clause lambda `e`, and its kind.
fn clause_parts(e: &Expr) -> (&[Alt], MatchKind) {
    let Expr::Lam(names, body, _) = e else {
        panic!("expected a lambda, got {e:?}");
    };
    let Expr::Match {
        scrutinees,
        alts,
        kind,
        ..
    } = &**body
    else {
        panic!("expected a `match`, got {body:?}");
    };
    assert_eq!(names.len(), scrutinees.len());
    (alts, *kind)
}

/// The argument of the call `g (…)` that is the right side of `text`.
fn bracketed_arg(text: &str) -> Expr {
    let e = rhs(&format!("def f: T := g ({text})\n"));
    let Expr::App(_, arg) = &e else {
        panic!("{e:?}")
    };
    (**arg).clone()
}

fn rhs_of(text: &str) -> Result<Expr> {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let module = parse_module(file, text).map_err(|mut e| e.remove(0))?;
    match module.decls.into_iter().last() {
        Some(Decl::Equation { rhs: Some(rhs), .. }) => Ok(rhs),
        _ => panic!("expected an equation"),
    }
}

fn else_branch(e: &Expr) -> &Expr {
    let Expr::If { otherwise, .. } = e else {
        panic!("expected an `if`, got {e:?}");
    };
    otherwise
}

fn is_num(e: &Expr, n: u32) -> bool {
    matches!(e, Expr::Num(v, _) if *v == n.into())
}

/// An expression's shape, fully bracketed.
fn shape(e: &Expr) -> String {
    match e {
        Expr::Var(n) => n.text.clone(),
        Expr::Num(n, _) => n.to_string(),
        Expr::Float(t, _) => t.clone(),
        Expr::Str(t, _) => format!("{t:?}"),
        Expr::Unit(_) => "()".into(),
        Expr::Bracketed(x, _) => shape(x),
        Expr::Lam(_, body, _) => format!("(=> {})", shape(body)),
        Expr::Pipe(a, b) => format!("(|> {} {})", shape(a), shape(b)),
        Expr::Seq(a, b) => format!("(; {} {})", shape(a), shape(b)),
        Expr::Let {
            name, value, body, ..
        } => {
            format!("(let {} {} {})", name.text, shape(value), shape(body))
        }
        Expr::Tuple(a, b, _) => format!("(, {} {})", shape(a), shape(b)),
        Expr::If {
            then, otherwise, ..
        } => format!("(if {} {})", shape(then), shape(otherwise)),
        Expr::Interpolated(x, _) => format!("${{{}}}", shape(x)),
        Expr::Neg(x, _, _) => format!("(- {})", shape(x)),
        Expr::App(f, a) => format!("({} {})", shape(f), shape(a)),
        Expr::Field(x, n, _) => format!("{}.{}", shape(x), n.text),
        Expr::Binary(op, a, b) => format!("({} {} {})", op_name(op), shape(a), shape(b)),
        other => panic!("unexpected {other:?}"),
    }
}

fn shape_of(text: &str) -> String {
    shape(
        &rhs_of(&format!(
            "def g (x : Nat) (y : Nat) (f : Nat) (a : Nat) (b : Nat) : Nat := {text}\n"
        ))
        .unwrap(),
    )
}

/// The parse of `text`'s declarations in recovery: the module, the
/// errors, and each declaration's recovery points.
fn recovered(text: &str) -> (Module, Vec<Diagnostic>, Vec<Vec<RecoveryPoint>>) {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let (module, errors, tree) = parse_module_and_tree(file, text, DEFAULT_STACK);
    let points = tree
        .decls()
        .map(|root| root.recoveries().iter().map(|r| r.point).collect())
        .collect();
    (module, errors, points)
}

/// The right-hand side of the only equation of `name` in `module`.
fn equation_rhs<'m>(module: &'m Module, name: &str) -> &'m Expr {
    let rhs = module.decls.iter().find_map(|d| match d {
        Decl::Equation { name: n, rhs, .. } if n.text == name => rhs.as_ref(),
        _ => None,
    });
    rhs.unwrap_or_else(|| panic!("no equation of {name}: {module:?}"))
}

/// A `let`-pattern's match: its scrutinee, pattern and body.
fn let_parts(e: &Expr) -> (&Expr, &Pattern, &Expr) {
    let Expr::Match {
        scrutinees,
        alts,
        kind: MatchKind::Let,
        ..
    } = e
    else {
        panic!("expected a `let` match, got {e:?}");
    };
    assert_eq!(scrutinees.len(), 1);
    assert_eq!(alts.len(), 1);
    (
        &scrutinees[0].expr,
        &alts[0].patterns[0],
        alts[0].body.as_ref().unwrap(),
    )
}

/// The first error's message and notes, for a source that must fail.
fn error_text(text: &str) -> String {
    let e = rhs_of(text).expect_err("expected a parse error");
    format!("{} {}", e.message, e.notes.join(" "))
}

/// Like `shape`, for the expressions pipelines are made of.
fn pshape(e: &Expr) -> String {
    match e {
        Expr::Var(n) => n.text.clone(),
        Expr::Num(n, _) => n.to_string(),
        Expr::App(f, a) => format!("({} {})", pshape(f), pshape(a)),
        Expr::Field(x, n, _) => format!("{}.{}", pshape(x), n.text),
        Expr::Binary(op, a, b) => format!("({} {} {})", op_name(op), pshape(a), pshape(b)),
        Expr::Pipe(a, b) => format!("(|> {} {})", pshape(a), pshape(b)),
        Expr::Arrow(a, b) => format!("(-> {} {})", pshape(a), pshape(b)),
        Expr::Lam(names, body, _) => {
            let names: Vec<&str> = names.iter().map(|n| n.text.as_str()).collect();
            format!("(\\{} {})", names.join(" "), pshape(body))
        }
        Expr::List(xs, _) => {
            let xs: Vec<String> = xs.iter().map(pshape).collect();
            format!("[{}]", xs.join(" "))
        }
        Expr::Let {
            name, value, body, ..
        } => format!("(let {} {} {})", name.text, pshape(value), pshape(body)),
        Expr::Match {
            scrutinees, alts, ..
        } => {
            let s: Vec<String> = scrutinees.iter().map(|s| pshape(&s.expr)).collect();
            let a: Vec<String> = alts
                .iter()
                .map(|a| pshape(a.body.as_ref().unwrap()))
                .collect();
            format!("(match {} | {})", s.join(","), a.join(" | "))
        }
        other => panic!("unexpected {other:?}"),
    }
}

fn pipe_shape(text: &str) -> String {
    pshape(&rhs_of(&format!("def g : Nat := {text}\n")).unwrap())
}

/// A definition's body, written on the lines after `def g (x : Nat) : Nat :=`.
fn pipe_body(body: &str) -> String {
    pshape(&rhs_of(&format!("def g (x : Nat) : Nat :=\n{body}\n")).unwrap())
}

fn section_shape(text: &str) -> String {
    pshape(&expression(text).unwrap())
}

// Local definitions in blocks

/// The names of a `LocalDefs`' definitions and its body.
fn local(e: &Expr) -> (Vec<String>, &Expr) {
    let Expr::LocalDefs { defs, body, .. } = e else {
        panic!("expected local definitions, got {e:?}");
    };
    let names = defs
        .iter()
        .map(|d| match &d.signature {
            Decl::Signature { name, .. } => name.text.to_string(),
            other => panic!("{other:?}"),
        })
        .collect();
    (names, body)
}

fn parse_error(text: &str) -> Diagnostic {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    parse_module(file, text).unwrap_err().remove(0)
}

fn parse_errors(text: &str) -> String {
    match parse_module_text(text) {
        Ok(_) => panic!("expected an error for {text:?}"),
        Err(errors) => errors
            .iter()
            .map(|d| format!("{}: {:?}", d.message, d.notes))
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

fn first_error(text: &str) -> String {
    match parse_module_text(text) {
        Ok(_) => panic!("{text}: parsed"),
        Err(errors) => errors[0].message.clone(),
    }
}

fn parse_module_text(text: &str) -> std::result::Result<Module, Vec<Diagnostic>> {
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    parse_module(file, text)
}

/// The names and arguments of attributes, as written.
fn attr_texts(attrs: &[crate::ast::Attribute]) -> Vec<String> {
    attrs
        .iter()
        .map(|a| match &a.arg {
            Some((arg, _)) => format!("{} {arg:?}", a.name.text),
            None => a.name.text.clone(),
        })
        .collect()
}

/// A data type's attributes as written: its own, each constructor's, and
/// each field's.
type DataAttrs = (Vec<String>, Vec<Vec<String>>, Vec<Vec<Vec<String>>>);

fn data_attrs(decl: &Decl) -> DataAttrs {
    let Decl::Data { attrs, ctors, .. } = decl else {
        panic!("expected a data type: {decl:?}");
    };
    (
        attr_texts(attrs),
        ctors.iter().map(|c| attr_texts(&c.attrs)).collect(),
        ctors
            .iter()
            .map(|c| c.fields.iter().map(|b| attr_texts(&b.attrs)).collect())
            .collect(),
    )
}

mod blocks;
mod declarations;
mod exprs;
mod lambdas;
mod matching;
mod operators;
mod patterns;
mod proofs;
mod recovery;

/// An operator's name in a shape: `Ne` whichever way it was spelled, since
/// the spelling matters only to messages (SW-3125).
fn op_name(op: &crate::ast::BinOp) -> String {
    match op {
        crate::ast::BinOp::Ne(_) => "Ne".to_string(),
        other => format!("{other:?}"),
    }
}
