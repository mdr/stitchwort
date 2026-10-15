//! The elaborator's type checker: checks surface expressions while turning them
//! into core terms, inserting implicit arguments as metavariables and solving
//! them by unification. Its output is re-checked by the kernel.

use std::rc::Rc;

use stitchwort_core::value::{Closure, Head, apply, eval, force, quote};
use stitchwort_core::{DataId, Globals, Icit, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{BinOp, Expr, Name as AstName};
use stitchwort_syntax::{Diagnostic, Span};

use crate::unify::unify;
use crate::{Elaborator, Global};

pub type Result<T> = std::result::Result<T, Diagnostic>;

pub struct Ctx<'e> {
    pub e: &'e Elaborator,
    /// What each variable evaluates to (inside a case branch, the matched
    /// variable is the constructor value).
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    /// Display names, for error messages.
    pub names: Vec<Name>,
    /// Names that can be referred to, and the level each refers to.
    scope: Vec<(String, usize)>,
    pub span: Span,
}

/// A position to return to with [`Ctx::reset`].
#[derive(Clone, Copy)]
pub struct Mark {
    level: usize,
    scope: usize,
}

impl<'e> Ctx<'e> {
    pub fn new(e: &'e Elaborator, span: Span) -> Self {
        Ctx {
            e,
            env: Vec::new(),
            types: Vec::new(),
            names: Vec::new(),
            scope: Vec::new(),
            span,
        }
    }

    /// A context with the given variables in scope (none of them by name).
    pub fn from_parts(
        e: &'e Elaborator,
        env: Vec<Value>,
        types: Vec<Value>,
        names: Vec<Name>,
        span: Span,
    ) -> Self {
        Ctx {
            e,
            env,
            types,
            names,
            scope: Vec::new(),
            span,
        }
    }

    pub fn g(&self) -> &'e Globals {
        &self.e.globals
    }

    pub fn level(&self) -> usize {
        self.env.len()
    }

    pub fn mark(&self) -> Mark {
        Mark {
            level: self.level(),
            scope: self.scope.len(),
        }
    }

    pub fn reset(&mut self, mark: Mark) {
        self.env.truncate(mark.level);
        self.types.truncate(mark.level);
        self.names.truncate(mark.level);
        self.scope.truncate(mark.scope);
    }

    /// Binds a variable that can be referred to by `name`.
    pub fn bind(&mut self, name: &str, ty: Value) {
        self.scope.push((name.to_string(), self.level()));
        self.bind_hidden(name.into(), ty);
    }

    /// Binds a variable that can't be referred to by name.
    pub fn bind_hidden(&mut self, name: Name, ty: Value) {
        self.env.push(Value::var(self.level()));
        self.types.push(ty);
        self.names.push(name);
    }

    /// Makes `name` refer to an existing variable.
    pub fn alias(&mut self, name: &str, level: usize) {
        self.scope.push((name.to_string(), level));
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, level)| *level)
    }

    pub fn eval(&self, term: &Term) -> Value {
        eval(self.g(), &self.env, term)
    }

    pub fn quote(&self, value: &Value) -> Term {
        quote(self.g(), self.level(), value)
    }

    pub fn unify(&self, a: &Value, b: &Value) -> bool {
        unify(self.g(), self.level(), a, b)
    }

    pub fn show(&self, value: &Value) -> String {
        pretty::value(self.g(), &self.names, value)
    }

    pub fn error(
        &self,
        code: &'static str,
        message: impl Into<String>,
        label: impl Into<String>,
    ) -> Diagnostic {
        Diagnostic::error(code, message).with_label(self.span, label)
    }

    /// A new metavariable, applied to every variable in scope (except those a
    /// case branch has replaced by a constructor), so its solution may depend
    /// on them.
    pub fn fresh_meta(&self) -> Term {
        let mut term = Term::Meta(self.g().new_meta(self.span));
        for (level, value) in self.env.iter().enumerate() {
            if matches!(value, Value::Neutral(Head::Var(l), s) if *l == level && s.is_empty()) {
                term = Term::app(term, Term::Var(self.level() - 1 - level));
            }
        }
        term
    }

    fn mismatch(&self, expected: &Value, found: &Value) -> Diagnostic {
        let expected_shown = self.show(expected);
        let found_shown = self.show(found);
        if let (Value::Sort(_), Value::Sort(_)) = (
            force(self.g(), expected.clone()),
            force(self.g(), found.clone()),
        ) {
            return self
                .error(
                    "E-UNIVERSE",
                    "universe mismatch",
                    format!("expected something of type `{expected_shown}`, but this has type `{found_shown}`"),
                )
                .with_note("`Type n` lives in `Type (n+1)`; allowing `Type : Type` would make the logic inconsistent");
        }
        self.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!("expected `{expected_shown}`, but this has type `{found_shown}`"),
        )
    }
}

fn with_span<T>(cx: &mut Ctx, span: Span, f: impl FnOnce(&mut Ctx) -> Result<T>) -> Result<T> {
    let saved = std::mem::replace(&mut cx.span, span);
    let result = f(cx);
    cx.span = saved;
    result
}

/// An argument in an application.
#[derive(Clone, Copy)]
enum Arg<'a> {
    Explicit(&'a Expr),
    Named(&'a AstName, &'a Expr),
}

pub fn infer(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let span = expr.span();
    with_span(cx, span, |cx| {
        let (term, ty) = infer_inner(cx, expr)?;
        Ok((Term::Loc(span, Rc::new(term)), ty))
    })
}

fn infer_inner(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    let g = cx.g();
    match expr {
        Expr::Var(_) | Expr::App(..) => {
            let mut args = Vec::new();
            let mut head = expr;
            while let Expr::App(f, a) = head {
                args.push(match a.as_ref() {
                    Expr::NamedArg(name, value, _) => Arg::Named(name, value),
                    other => Arg::Explicit(other),
                });
                head = f;
            }
            args.reverse();
            infer_app(cx, head, &args)
        }
        Expr::NamedArg(..) => Err(cx.error(
            "E-PARSE",
            "a named implicit argument must follow a function",
            "write `f [x := …]`",
        )),
        Expr::Num(n, _) => Ok((
            Term::Nat(Rc::new(n.clone())),
            Value::Data(nat(cx)?, Vec::new()),
        )),
        Expr::Type(i, _) => Ok((Term::Sort(Sort::Type(*i)), Value::Sort(Sort::Type(i + 1)))),
        Expr::Prop(_) => Ok((Term::Sort(Sort::Prop), Value::Sort(Sort::Type(0)))),
        Expr::Hole(_) => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty);
            Ok((cx.fresh_meta(), ty))
        }
        Expr::Lam(..) => Err(cx.error(
            "E-CANNOT-INFER",
            "can't work out the type of this function",
            "add a type annotation: `(… : T)`",
        )),
        Expr::Pi {
            names,
            implicit,
            auto,
            dom,
            cod,
            ..
        } => {
            let icit = match (implicit, auto) {
                (_, true) => Icit::Auto,
                (true, false) => Icit::Implicit,
                (false, false) => Icit::Explicit,
            };
            let (dom, s1) = check_type(cx, dom)?;
            let mark = cx.mark();
            for (k, name) in names.iter().enumerate() {
                let ty = cx.eval(&dom.shift(k, 0));
                cx.bind(&name.text, ty);
            }
            let result = check_type(cx, cod);
            cx.reset(mark);
            let (mut term, s2) = result?;
            for (k, name) in names.iter().enumerate().rev() {
                term = Term::Pi(
                    name.text.as_str().into(),
                    icit,
                    Rc::new(dom.shift(k, 0)),
                    Rc::new(term),
                );
            }
            Ok((term, Value::Sort(Sort::pi(s1, s2))))
        }
        Expr::Arrow(a, b) => {
            let (a, s1) = check_type(cx, a)?;
            let mark = cx.mark();
            let a_value = cx.eval(&a);
            cx.bind_hidden("_".into(), a_value);
            let result = check_type(cx, b);
            cx.reset(mark);
            let (b, s2) = result?;
            Ok((
                Term::Pi("_".into(), Icit::Explicit, Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::pi(s1, s2)),
            ))
        }
        Expr::Binary(BinOp::Eq, a, b) => Ok((equation(cx, a, b)?, Value::Sort(Sort::Prop))),
        Expr::Binary(BinOp::Ne, a, b) => {
            // `a != b` means `Not (a = b)`.
            let not = def_named(cx, "Not")?;
            let eq = equation(cx, a, b)?;
            Ok((Term::app(Term::Def(not), eq), Value::Sort(Sort::Prop)))
        }
        Expr::Binary(BinOp::EqEq, a, b) => {
            // `a == b` is `toBool d`, for a decision procedure `d` for
            // `a = b`, found as for `if h : a = b`.
            let eq = equation(cx, a, b)?;
            let decision = crate::auto::decide(cx, &cx.eval(&eq), 0)?;
            let to_bool = def_named(cx, "toBool")?;
            let (bool_data, _) = ctor_named(cx, "True")?;
            Ok((
                Term::app(
                    Term::app_icit(Term::Def(to_bool), eq, Icit::Implicit),
                    decision,
                ),
                Value::Data(bool_data, Vec::new()),
            ))
        }
        Expr::Binary(op, a, b) => {
            let name = match op {
                BinOp::Lt => "LessThan",
                BinOp::Le => "LessEq",
                BinOp::Add => "add",
                BinOp::Sub => "sub",
                BinOp::Mul => "mul",
                BinOp::Div => "div",
                BinOp::Mod => "mod",
                BinOp::Eq | BinOp::Ne | BinOp::EqEq => unreachable!("handled above"),
            };
            let id = def_named(cx, name)?;
            let head = (Term::Def(id), g.def(id).ty_value.clone());
            let (term, ty) = apply_args(cx, head, &[Arg::Explicit(a), Arg::Explicit(b)])?;
            // `/` and `%` take an automatic proof that the divisor isn't zero.
            Ok(insert(cx, term, ty))
        }
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty);
            let term = check_if(cx, binder.as_ref(), cond, then, otherwise, &ty)?;
            Ok((term, ty))
        }
        Expr::Ann(e, ty, _) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty);
            let e = check(cx, e, &ty_value)?;
            Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_value))
        }
        Expr::List(..) => {
            let (list, _) = ctor_named(cx, "Nil")?;
            let elem = cx.fresh_meta();
            let ty = Value::Data(list, vec![cx.eval(&elem)]);
            let term = check(cx, expr, &ty)?;
            Ok((annotate(cx, term, &ty), ty))
        }
    }
}

/// Infers an application `head args`.
fn infer_app(cx: &mut Ctx, head: &Expr, args: &[Arg]) -> Result<(Term, Value)> {
    let g = cx.g();
    let Expr::Var(name) = head else {
        let head = infer(cx, head)?;
        return apply_args(cx, head, args);
    };
    if let Some(level) = cx.lookup(&name.text) {
        let head = (Term::Var(cx.level() - 1 - level), cx.types[level].clone());
        return apply_args(cx, head, args);
    }
    match name.text.as_str() {
        "rfl" => {
            return Err(cx.error(
                "E-CANNOT-INFER",
                "can't work out what `rfl` proves here",
                "add a type annotation: `(rfl : a = b)`",
            ));
        }
        "J" => {
            let [
                Arg::Explicit(motive),
                Arg::Explicit(base),
                Arg::Explicit(proof),
            ] = args[..]
            else {
                return Err(cx.error(
                    "E-ARITY",
                    "`J` takes 3 arguments: a motive, a base case and a proof",
                    "here",
                ));
            };
            return infer_j(cx, motive, base, proof);
        }
        _ => {}
    }
    match cx.e.names.get(&name.text) {
        None => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("unknown name `{}`", name.text),
            "not in scope",
        )),
        Some((Global::Def(id), _)) => {
            let head = (Term::Def(*id), g.def(*id).ty_value.clone());
            apply_args(cx, head, args)
        }
        Some((Global::Data(d), _)) => {
            let data = g.data(*d);
            let n = data.params.len();
            if args.len() < n {
                return Err(cx.error(
                    "E-ARITY",
                    format!("`{}` needs {n} argument(s)", data.name),
                    "here",
                ));
            }
            let mut params = Vec::new();
            let mut terms = Vec::new();
            for ((_, param_ty), arg) in data.params.iter().zip(args) {
                let Arg::Explicit(arg) = arg else {
                    return Err(cx.error("E-ARITY", "data type parameters are explicit", "here"));
                };
                let ty = eval(g, &params, param_ty);
                let term = check(cx, arg, &ty)?;
                params.push(cx.eval(&term));
                terms.push(term);
            }
            let head = (Term::Data(*d, terms), Value::Sort(data.sort));
            apply_args(cx, head, &args[n..])
        }
        Some((Global::Ctor(d, c), _)) => {
            let explicit = explicit_args(cx, args)?;
            let missing = g.data(*d).ctors[*c]
                .fields
                .len()
                .saturating_sub(explicit.len());
            if missing > 0 {
                // A partially applied constructor is a function; unification
                // works out its type.
                let expected = fresh_function_type(cx, missing);
                let expected = cx.eval(&expected);
                let (term, ty) = ctor_app(cx, *d, *c, &explicit, Some(&expected))?;
                let ann = Term::Ann(Rc::new(term), Rc::new(cx.quote(&ty)));
                return Ok((ann, ty));
            }
            let (term, ty) = ctor_app(cx, *d, *c, &explicit, None)?;
            Ok((annotate(cx, term, &ty), ty))
        }
    }
}

/// `?a1 -> … -> ?an -> ?b`, with each type a fresh metavariable.
fn fresh_function_type(cx: &mut Ctx, arity: usize) -> Term {
    if arity == 0 {
        return cx.fresh_meta();
    }
    let dom = cx.fresh_meta();
    let mark = cx.mark();
    let dom_value = cx.eval(&dom);
    cx.bind_hidden("x".into(), dom_value);
    let cod = fresh_function_type(cx, arity - 1);
    cx.reset(mark);
    Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod))
}

fn explicit_args<'a>(cx: &Ctx, args: &[Arg<'a>]) -> Result<Vec<&'a Expr>> {
    args.iter()
        .map(|a| match a {
            Arg::Explicit(e) => Ok(*e),
            Arg::Named(..) => {
                Err(cx.error("E-ARITY", "constructors don't take named arguments", "here"))
            }
        })
        .collect()
}

/// Applies `head` to `args`, inserting implicit arguments where needed.
fn apply_args(cx: &mut Ctx, head: (Term, Value), args: &[Arg]) -> Result<(Term, Value)> {
    let (mut term, mut ty) = head;
    for arg in args {
        match arg {
            Arg::Named(name, value) => {
                (term, ty) = insert_until(cx, term, ty, name)?;
                let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone()) else {
                    unreachable!("insert_until stops at the named implicit parameter");
                };
                let value = check(cx, value, &dom)?;
                let v = cx.eval(&value);
                term = Term::app_icit(term, value, icit);
                ty = cod.apply(cx.g(), v);
            }
            Arg::Explicit(value) => {
                (term, ty) = insert(cx, term, ty);
                let (dom, cod) = match force(cx.g(), ty.clone()) {
                    Value::Pi(_, Icit::Explicit, dom, cod) => ((*dom).clone(), cod),
                    Value::Neutral(Head::Meta(_), _) => {
                        // Unknown type: it must be a function type.
                        let dom = cx.fresh_meta();
                        let dom = cx.eval(&dom);
                        let mark = cx.mark();
                        cx.bind_hidden("x".into(), dom.clone());
                        let cod = cx.fresh_meta();
                        cx.reset(mark);
                        let cod = Closure {
                            env: cx.env.as_slice().into(),
                            body: Rc::new(cod),
                        };
                        let pi = Value::Pi(
                            "x".into(),
                            Icit::Explicit,
                            Rc::new(dom.clone()),
                            cod.clone(),
                        );
                        if !cx.unify(&ty, &pi) {
                            return Err(cx.mismatch(&pi, &ty));
                        }
                        (dom, cod)
                    }
                    other => {
                        return Err(cx.error(
                            "E-NOT-A-FUNCTION",
                            "this isn't a function",
                            format!(
                                "it's applied to an argument, but its type is `{}`",
                                cx.show(&other)
                            ),
                        ));
                    }
                };
                let value = check(cx, value, &dom)?;
                let v = cx.eval(&value);
                term = Term::app(term, value);
                ty = cod.apply(cx.g(), v);
            }
        }
    }
    Ok((term, ty))
}

/// Applies `term` to a fresh metavariable for each leading implicit or auto
/// parameter. An auto argument is also recorded as an obligation, to be proved
/// once the declaration has been elaborated (see `auto.rs`).
pub fn insert(cx: &mut Ctx, mut term: Term, mut ty: Value) -> (Term, Value) {
    while let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone())
        && icit.is_implicit()
    {
        let meta = implicit_arg(cx, icit, &dom);
        let value = cx.eval(&meta);
        term = Term::app_icit(term, meta, icit);
        ty = cod.apply(cx.g(), value);
    }
    (term, ty)
}

fn implicit_arg(cx: &mut Ctx, icit: Icit, ty: &Value) -> Term {
    let meta = cx.fresh_meta();
    if icit == Icit::Auto {
        cx.e.obligations.borrow_mut().push(crate::auto::Obligation {
            env: cx.env.clone(),
            types: cx.types.clone(),
            names: cx.names.clone(),
            goal: ty.clone(),
            meta: meta.clone(),
            span: cx.span,
        });
    }
    meta
}

/// Inserts implicit arguments up to the implicit parameter called `name`.
fn insert_until(
    cx: &mut Ctx,
    mut term: Term,
    mut ty: Value,
    name: &AstName,
) -> Result<(Term, Value)> {
    loop {
        match force(cx.g(), ty.clone()) {
            Value::Pi(x, icit, _, _) if icit.is_implicit() && *x == *name.text => {
                return Ok((term, ty));
            }
            Value::Pi(_, icit, dom, cod) if icit.is_implicit() => {
                let meta = implicit_arg(cx, icit, &dom);
                let value = cx.eval(&meta);
                term = Term::app_icit(term, meta, icit);
                ty = cod.apply(cx.g(), value);
            }
            _ => {
                return Err(Diagnostic::error(
                    "E-UNKNOWN-NAME",
                    format!("no implicit parameter named `{}` here", name.text),
                )
                .with_label(name.span, "not an implicit parameter of this function"));
            }
        }
    }
}

pub fn check(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let span = expr.span();
    with_span(cx, span, |cx| {
        let term = check_inner(cx, expr, expected)?;
        Ok(Term::Loc(span, Rc::new(term)))
    })
}

fn check_inner(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let g = cx.g();
    let expected = force(g, expected.clone());
    match (expr, &expected) {
        (Expr::Hole(_), _) => Ok(cx.fresh_meta()),
        // Implicit parameters are introduced automatically.
        (_, Value::Pi(x, icit, dom, cod)) if icit.is_implicit() => {
            let mark = cx.mark();
            let var = Value::var(cx.level());
            cx.bind_hidden(x.clone(), (**dom).clone());
            let result = check(cx, expr, &cod.apply(g, var));
            cx.reset(mark);
            Ok(Term::Lam(x.clone(), *icit, Rc::new(result?)))
        }
        (
            Expr::If {
                binder,
                cond,
                then,
                otherwise,
                ..
            },
            _,
        ) => check_if(cx, binder.as_ref(), cond, then, otherwise, &expected),
        (Expr::Lam(names, body, span), Value::Pi(_, Icit::Explicit, dom, cod)) => {
            let (first, rest) = names.split_first().expect("lambdas have parameters");
            let mark = cx.mark();
            let var = Value::var(cx.level());
            cx.bind(&first.text, (**dom).clone());
            let cod = cod.apply(g, var);
            let result = if rest.is_empty() {
                check(cx, body, &cod)
            } else {
                check(cx, &Expr::Lam(rest.to_vec(), body.clone(), *span), &cod)
            };
            cx.reset(mark);
            Ok(Term::Lam(
                first.text.as_str().into(),
                Icit::Explicit,
                Rc::new(result?),
            ))
        }
        (Expr::Lam(..), _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "this is a function, but the expected type is `{}`",
                cx.show(&expected)
            ),
        )),
        (Expr::Var(name), Value::Eq(_, a, b))
            if name.text == "rfl" && cx.lookup("rfl").is_none() =>
        {
            if cx.unify(a, b) {
                Ok(Term::Refl)
            } else {
                Err(cx
                    .error(
                        "E-REFL",
                        "`rfl` can't prove this",
                        format!("`{}` and `{}` aren't equal", cx.show(a), cx.show(b)),
                    )
                    .with_note(
                        "`rfl` proves `a = b` only when both sides compute to the same value",
                    ))
            }
        }
        (Expr::Var(name), _) if name.text == "rfl" && cx.lookup("rfl").is_none() => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`rfl` proves an equation, but the expected type is `{}`",
                cx.show(&expected)
            ),
        )),
        (Expr::List(items, _), Value::Data(d, params)) => {
            let (list, nil) = ctor_named(cx, "Nil")?;
            let (_, cons) = ctor_named(cx, "Cons")?;
            if *d != list {
                return fallback(cx, expr, &expected);
            }
            let elem = params[0].clone();
            let mut terms = Vec::new();
            for item in items {
                terms.push(check(cx, item, &elem)?);
            }
            let mut term = Term::Ctor(list, nil, Vec::new());
            for item in terms.into_iter().rev() {
                term = Term::Ctor(list, cons, vec![item, term]);
            }
            Ok(term)
        }
        (Expr::Var(_) | Expr::App(..), Value::Data(..) | Value::Pi(_, Icit::Explicit, _, _)) => {
            match ctor_head(cx, expr)? {
                Some((d, c, args)) => {
                    let (term, ty) = ctor_app(cx, d, c, &args, Some(&expected))?;
                    if cx.unify(&ty, &expected) {
                        Ok(term)
                    } else {
                        Err(cx.mismatch(&expected, &ty))
                    }
                }
                None => fallback(cx, expr, &expected),
            }
        }
        _ => fallback(cx, expr, &expected),
    }
}

/// `a = b`, with the type of both sides inferred from either one.
fn equation(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<Term> {
    let (a, b, ty) = match infer(cx, a).map(|(t, ty)| insert(cx, t, ty)) {
        Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            let (b, ty) = infer(cx, b)?;
            let (b, ty) = insert(cx, b, ty);
            (check(cx, a, &ty)?, b, ty)
        }
        Err(e) => return Err(e),
    };
    let ty = cx.quote(&ty);
    Ok(Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b)))
}

/// `if c then a else b` is `ifThenElse c (\_ -> a) (\_ -> b)`, and
/// `if h : P then a else b` is `elimDec (decision for P) (\h -> a) (\h -> b)`.
/// The branches are functions so only the chosen one is evaluated.
fn check_if(
    cx: &mut Ctx,
    binder: Option<&AstName>,
    cond: &Expr,
    then: &Expr,
    otherwise: &Expr,
    expected: &Value,
) -> Result<Term> {
    let result_ty = cx.quote(expected);
    let branch = |cx: &mut Ctx, name: &str, ty: Value, body: &Expr| -> Result<Term> {
        let mark = cx.mark();
        cx.bind(name, ty);
        let result = check(cx, body, expected);
        cx.reset(mark);
        Ok(Term::Lam(name.into(), Icit::Explicit, Rc::new(result?)))
    };
    match binder {
        None => {
            let (bool_data, _) = ctor_named(cx, "True")?;
            let (unit_data, _) = ctor_named(cx, "Trivial")?;
            let cond = check(cx, cond, &Value::Data(bool_data, Vec::new()))?;
            let unit = Value::Data(unit_data, Vec::new());
            let then = branch(cx, "_", unit.clone(), then)?;
            let otherwise = branch(cx, "_", unit, otherwise)?;
            let ite = def_named(cx, "ifThenElse")?;
            let head = Term::app_icit(Term::Def(ite), result_ty, Icit::Implicit);
            Ok(Term::app(Term::app(Term::app(head, cond), then), otherwise))
        }
        Some(h) => {
            let (prop, sort) = check_type(cx, cond).map_err(|e| {
                if e.code == "E-NOT-A-TYPE" {
                    e.with_note("`if h : P` needs a proposition `P`; for a `Bool`, write `if c then … else …`")
                } else {
                    e
                }
            })?;
            if sort != Sort::Prop {
                return Err(cx.error(
                    "E-TYPE-MISMATCH",
                    "`if h : …` needs a proposition",
                    "this is a type of data; use `if c then … else …` for a `Bool`",
                ));
            }
            let prop_value = cx.eval(&prop);
            let decision = crate::auto::decide(cx, &prop_value, 0)?;
            let not = def_named(cx, "Not")?;
            let not_prop = cx.eval(&Term::app(Term::Def(not), prop.clone()));
            let then = branch(cx, &h.text, prop_value, then)?;
            let otherwise = branch(cx, &h.text, not_prop, otherwise)?;
            let elim = def_named(cx, "elimDec")?;
            let head = Term::app_icit(
                Term::app_icit(Term::Def(elim), prop, Icit::Implicit),
                result_ty,
                Icit::Implicit,
            );
            Ok(Term::app(
                Term::app(Term::app(head, decision), then),
                otherwise,
            ))
        }
    }
}

fn fallback(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let (term, found) = infer(cx, expr)?;
    let (term, found) = insert(cx, term, found);
    if cx.unify(&found, expected) {
        Ok(term)
    } else {
        Err(cx.mismatch(expected, &found))
    }
}

/// If `expr` is a constructor applied to explicit arguments: the constructor
/// and the arguments.
fn ctor_head<'a>(cx: &Ctx, expr: &'a Expr) -> Result<Option<(DataId, usize, Vec<&'a Expr>)>> {
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(a.as_ref());
        head = f;
    }
    args.reverse();
    let Expr::Var(name) = head else {
        return Ok(None);
    };
    if cx.lookup(&name.text).is_some() {
        return Ok(None);
    }
    match cx.e.names.get(&name.text) {
        Some((Global::Ctor(d, c), _)) => {
            if args.iter().any(|a| matches!(a, Expr::NamedArg(..))) {
                return Err(cx.error("E-ARITY", "constructors don't take named arguments", "here"));
            }
            Ok(Some((*d, *c, args)))
        }
        _ => Ok(None),
    }
}

/// Elaborates constructor `c` of `d` applied to `args`. The data type's
/// parameters come from `expected` if given, or are left to unification.
/// A partially applied constructor is a function, which needs `expected`.
fn ctor_app(
    cx: &mut Ctx,
    d: DataId,
    c: usize,
    args: &[&Expr],
    expected: Option<&Value>,
) -> Result<(Term, Value)> {
    let g = cx.g();
    let data = g.data(d);
    let ctor = &data.ctors[c];
    let k = ctor.fields.len();
    if args.len() > k {
        return Err(cx.error(
            "E-NOT-A-FUNCTION",
            format!("`{}` takes {k} argument(s)", ctor.name),
            format!("it's given {}", args.len()),
        ));
    }

    // Partial application: `\x … -> C args x …`, checked against a function type.
    let mut missing_types = Vec::new();
    let mark = cx.mark();
    let mut target = expected.cloned();
    for i in args.len()..k {
        match target.as_ref().map(|t| force(g, t.clone())) {
            Some(Value::Pi(_, Icit::Explicit, dom, cod)) => {
                let var = Value::var(cx.level());
                let name: Name = ctor.fields[i].0.clone();
                cx.bind_hidden(name.clone(), (*dom).clone());
                missing_types.push(name);
                target = Some(cod.apply(g, var));
            }
            _ => {
                cx.reset(mark);
                return Err(cx.error(
                    "E-CANNOT-INFER",
                    format!("`{}` is missing {} argument(s)", ctor.name, k - args.len()),
                    "add the missing arguments, or a type annotation",
                ));
            }
        }
    }

    let params = match target.as_ref().map(|t| force(g, t.clone())) {
        Some(Value::Data(d2, params)) if d2 == d => params,
        _ => data
            .params
            .iter()
            .map(|_| {
                let meta = cx.fresh_meta();
                cx.eval(&meta)
            })
            .collect(),
    };
    let mut env = params.clone();
    let mut terms = Vec::new();
    let first_missing_level = mark.level;
    for (i, (_, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty);
        let term = if let Some(arg) = args.get(i) {
            check(cx, arg, &ty)?
        } else {
            let level = first_missing_level + (i - args.len());
            let found = cx.types[level].clone();
            if !cx.unify(&found, &ty) {
                cx.reset(mark);
                return Err(cx.mismatch(&ty, &found));
            }
            Term::Var(cx.level() - 1 - level)
        };
        env.push(cx.eval(&term));
        terms.push(term);
    }
    let result_ty = Value::Data(d, params);
    if let Some(target) = &target
        && !cx.unify(&result_ty, target)
    {
        let error = cx.mismatch(target, &result_ty);
        cx.reset(mark);
        return Err(error);
    }
    cx.reset(mark);
    let mut term = Term::Ctor(d, c, terms);
    if missing_types.is_empty() {
        return Ok((term, result_ty));
    }
    for name in missing_types.into_iter().rev() {
        term = Term::Lam(name, Icit::Explicit, Rc::new(term));
    }
    Ok((term, expected.expect("checked above").clone()))
}

/// Wraps an inferred constructor in a type annotation, so the kernel (which
/// can only check constructors of parameterised types) can infer it too.
fn annotate(cx: &Ctx, term: Term, ty: &Value) -> Term {
    match ty {
        Value::Data(d, _) if !cx.g().data(*d).params.is_empty() => {
            Term::Ann(Rc::new(term), Rc::new(cx.quote(ty)))
        }
        _ => term,
    }
}

pub fn check_type(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Sort)> {
    let span = expr.span();
    let (term, ty) = infer(cx, expr)?;
    match force(cx.g(), ty) {
        Value::Sort(s) => Ok((term, s)),
        ty @ Value::Neutral(Head::Meta(_), _) => {
            // An unknown type of types defaults to `Type`.
            if cx.unify(&ty, &Value::Sort(Sort::Type(0))) {
                Ok((term, Sort::Type(0)))
            } else {
                Err(not_a_type(cx, span, &ty))
            }
        }
        other => Err(not_a_type(cx, span, &other)),
    }
}

fn not_a_type(cx: &Ctx, span: Span, ty: &Value) -> Diagnostic {
    Diagnostic::error("E-NOT-A-TYPE", "expected a type").with_label(
        span,
        format!("this has type `{}`, so it isn't a type", cx.show(ty)),
    )
}

fn infer_j(cx: &mut Ctx, motive: &Expr, base: &Expr, proof: &Expr) -> Result<(Term, Value)> {
    let g = cx.g();
    let (proof, proof_ty) = infer(cx, proof)?;
    let (proof, proof_ty) = insert(cx, proof, proof_ty);
    let Value::Eq(ty, x, y) = force(g, proof_ty.clone()) else {
        return Err(cx.error(
            "E-TYPE-MISMATCH",
            "`J` needs a proof of an equation",
            format!("its last argument has type `{}`", cx.show(&proof_ty)),
        ));
    };
    let Expr::Lam(names, body, _) = motive else {
        return Err(motive_error(cx));
    };
    let [y_name, p_name] = &names[..] else {
        return Err(motive_error(cx));
    };
    let mark = cx.mark();
    let level = cx.level();
    cx.bind(&y_name.text, (*ty).clone());
    cx.bind(
        &p_name.text,
        Value::Eq(ty.clone(), x.clone(), Rc::new(Value::var(level))),
    );
    let result = check_type(cx, body);
    cx.reset(mark);
    let (body, _) = result?;
    let motive = Term::Lam(
        y_name.text.as_str().into(),
        Icit::Explicit,
        Rc::new(Term::Lam(
            p_name.text.as_str().into(),
            Icit::Explicit,
            Rc::new(body),
        )),
    );
    let motive_value = cx.eval(&motive);
    let base_ty = apply(g, apply(g, motive_value.clone(), (*x).clone()), Value::Refl);
    let base = check(cx, base, &base_ty)?;
    let proof_value = cx.eval(&proof);
    let result = apply(g, apply(g, motive_value, (*y).clone()), proof_value);
    Ok((
        Term::J(Rc::new(motive), Rc::new(base), Rc::new(proof)),
        result,
    ))
}

fn motive_error(cx: &Ctx) -> Diagnostic {
    cx.error(
        "E-CANNOT-INFER",
        "the first argument of `J` must be a function of two arguments",
        "write it as `\\y p -> …`",
    )
}

/// `Nat`, which numbers need.
fn nat(cx: &Ctx) -> Result<DataId> {
    cx.e.globals
        .builtins
        .nat
        .ok_or_else(|| cx.error("E-UNKNOWN-NAME", "numbers need the prelude's `Nat`", "here"))
}

pub fn ctor_named(cx: &Ctx, name: &str) -> Result<(DataId, usize)> {
    match cx.e.names.get(name) {
        Some((Global::Ctor(d, c), _)) => Ok((*d, *c)),
        _ => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("this needs the prelude's `{name}`"),
            "here",
        )),
    }
}

pub fn def_named(cx: &Ctx, name: &str) -> Result<stitchwort_core::DefId> {
    match cx.e.names.get(name) {
        Some((Global::Def(id), _)) => Ok(*id),
        _ => Err(cx.error(
            "E-UNKNOWN-NAME",
            format!("this needs the prelude's `{name}`"),
            "here",
        )),
    }
}
