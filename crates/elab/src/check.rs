//! The elaborator's type checker: checks surface expressions while turning them
//! into core terms, inserting implicit arguments as metavariables and solving
//! them by unification. Its output is re-checked by the kernel.

use std::rc::Rc;

use stitchwort_core::chars::{self as compact, Chars};
use stitchwort_core::check as kernel;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Closure, Head, apply, eval, force, quote, unused};
use stitchwort_core::{DataId, Globals, Icit, Name, Sort, Term, Value, pretty};
use stitchwort_syntax::ast::{BinOp, Expr, Name as AstName};
use stitchwort_syntax::{Diagnostic, Span};

use crate::unify::unify;
use crate::{Elaborator, Global, effects, records};

pub type Result<T> = std::result::Result<T, Diagnostic>;

/// The name the elaborator's depth guards report. Each function the
/// elaborator recurses through over syntax or terms (`infer`, `check`,
/// `may_perform`, …) checks it has stack left first
/// (docs/proposals/stack-safe-evaluation.md).
pub(crate) const PASS: &str = "elaborator";

pub struct Ctx<'e> {
    pub e: &'e Elaborator,
    /// What each variable evaluates to (inside a case branch, the matched
    /// variable is the constructor value).
    pub env: Vec<Value>,
    pub types: Vec<Value>,
    /// Display names, for error messages.
    pub names: Vec<Name>,
    /// Each variable's type as written, where known: a term in the context
    /// of the variables before it. Dot notation finds a namespace from it
    /// (docs/proposals/namespaces.md §4.8), since `types` may have unfolded
    /// a nickname like `Price = Nat`.
    pub written: Vec<Option<crate::dot::Written>>,
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
            written: Vec::new(),
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
        let written = vec![None; env.len()];
        Ctx {
            e,
            env,
            types,
            names,
            written,
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
        self.written.truncate(mark.level);
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
        self.written.push(None);
    }

    /// Records the type the latest variable was declared with, as written: a
    /// term in the context of the variables before it.
    pub(crate) fn set_written(&mut self, ty: crate::dot::Written) {
        if let Some(last) = self.written.last_mut() {
            *last = Some(ty);
        }
    }

    /// Makes `name` refer to an existing variable.
    pub fn alias(&mut self, name: &str, level: usize) {
        self.scope.push((name.to_string(), level));
    }

    /// Makes every name that now refers to the variable at `old` refer to
    /// the one at `new` instead (a generalised `match`'s copies).
    pub(crate) fn rebind(&mut self, old: usize, new: usize) {
        let names: Vec<String> = self
            .scope
            .iter()
            .filter(|(n, level)| *level == old && self.lookup(n) == Some(old))
            .map(|(n, _)| n.clone())
            .collect();
        for n in names {
            self.scope.push((n, new));
        }
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<usize> {
        self.scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, level)| *level)
    }

    pub fn eval(&self, term: &Term) -> Result<Value> {
        Ok(eval(self.g(), &self.env, term)?)
    }

    pub fn quote(&self, value: &Value) -> Result<Term> {
        Ok(quote(self.g(), self.level(), value)?)
    }

    /// `Ok(false)` if `a` and `b` can't be made equal; an error if it ran out
    /// of resources finding out.
    pub fn unify(&self, a: &Value, b: &Value) -> Result<bool> {
        Ok(unify(self.g(), self.level(), a, b)?)
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

    pub(crate) fn mismatch(&self, expected: &Value, found: &Value) -> Diagnostic {
        let expected_shown = self.show(expected);
        let found_shown = self.show(found);
        if let (Ok(Value::Sort(_)), Ok(Value::Sort(_))) = (
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
pub(crate) enum Arg<'a> {
    Explicit(&'a Expr),
    Named(&'a AstName, &'a Expr),
    /// The value piped in by `|>`, already elaborated (`pipe.rs`).
    Piped(&'a Piped),
}

/// The left side of `x |> f`, elaborated, as `f`'s last argument.
pub(crate) struct Piped {
    pub term: Term,
    pub ty: Value,
    /// The right side's span: errors about the value not fitting point at
    /// the function it's piped into.
    pub span: Span,
}

pub fn infer(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    cx.g().budget.nesting(PASS)?;
    let span = expr.span();
    with_span(cx, span, |cx| {
        let (term, ty) = infer_inner(cx, expr)?;
        Ok((Term::Loc(span, Rc::new(term)), ty))
    })
}

fn infer_inner(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Value)> {
    // Code that performs operations, in a pure context: it may only perform
    // what it handles itself.
    if effects::may_perform(cx, expr)? {
        return effects::run_pure(cx, expr, None);
    }
    if let Some(logic) = crate::logic::classify(cx, expr) {
        return crate::logic::infer(cx, logic);
    }
    match expr {
        Expr::Unit(_) => {
            let unit = builtin_data(cx, Builtin::UnitType)?;
            Ok((
                Term::Ctor(unit, 0, Vec::new()),
                Value::Data(unit, Vec::new()),
            ))
        }
        Expr::Tuple(a, b, _) => infer_tuple(cx, a, b),
        Expr::Match { .. } => crate::matching::infer_match(cx, expr),
        Expr::Effect(row, ty) => {
            let (term, sort) = effects::effect_type(cx, row, ty)?;
            Ok((term, Value::Sort(sort)))
        }
        Expr::Let { .. } | Expr::Seq(..) | Expr::Handle { .. } => {
            unreachable!("these may perform operations, so they're handled above")
        }
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
        Expr::Pipe(value, f) => crate::pipe::infer_pipe(cx, value, f),
        Expr::NamedArg(..) => Err(cx.error(
            "E-PARSE",
            "a named implicit argument must follow a function",
            "write `f [x := …]`",
        )),
        // `-k` with nothing expected is an `Int`.
        Expr::Neg(..) => crate::numbers::group(cx, expr, None),
        Expr::Num(n, _) => Ok((
            Term::Nat(Rc::new(n.clone())),
            Value::Data(nat(cx)?, Vec::new()),
        )),
        Expr::Char(c, _) => {
            let char_data = builtin_data(cx, Builtin::Char)?;
            Ok((char_term(cx, *c)?, Value::Data(char_data, Vec::new())))
        }
        // `"ab"` is `MkText ['a', 'b']`: its characters are one compact list
        // when the prelude's `List` and `Char` are registered for it
        // (`stitchwort_core::chars`), and otherwise cons cells.
        Expr::Str(s, _) => {
            let (text, mk_text) = builtin_ctor(cx, Builtin::MkText)?;
            let (list, nil) = builtin_ctor(cx, Builtin::Nil)?;
            let (_, cons) = builtin_ctor(cx, Builtin::Cons)?;
            let chars = match cx.g().builtins.compact_literals() {
                Some(text_rep) => {
                    let buffer: std::rc::Rc<[char]> = s.chars().collect();
                    compact::term(text_rep, &Chars::whole(buffer))
                }
                None => {
                    let mut chars = Term::Ctor(list, nil, Vec::new());
                    for c in s.chars().rev() {
                        chars = Term::ctor(list, cons, vec![char_term(cx, c)?, chars]);
                    }
                    chars
                }
            };
            Ok((
                Term::ctor(text, mk_text, vec![chars]),
                Value::Data(text, Vec::new()),
            ))
        }
        Expr::Binary(BinOp::Append, a, b) => append(cx, a, b),
        Expr::Type(i, _) => Ok((Term::Sort(Sort::Type(*i)), Value::Sort(Sort::Type(i + 1)))),
        Expr::Prop(_) => Ok((Term::Sort(Sort::Prop), Value::Sort(Sort::Type(0)))),
        Expr::Hole(_) => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty)?;
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
                let ty = cx.eval(&dom.shift(cx.g(), k, 0)?)?;
                cx.bind(&name.text, ty);
            }
            let result = check_type(cx, cod);
            cx.reset(mark);
            let (mut term, s2) = result?;
            for (k, name) in names.iter().enumerate().rev() {
                term = Term::Pi(
                    name.text.as_str().into(),
                    icit,
                    Rc::new(dom.shift(cx.g(), k, 0)?),
                    Rc::new(term),
                );
            }
            Ok((term, Value::Sort(Sort::pi(s1, s2))))
        }
        Expr::Arrow(a, b) => {
            let (a, s1) = check_type(cx, a)?;
            let mark = cx.mark();
            let a_value = cx.eval(&a)?;
            cx.bind_hidden("_".into(), a_value);
            let result = check_type(cx, b);
            cx.reset(mark);
            let (b, s2) = result?;
            Ok((
                Term::Pi("_".into(), Icit::Explicit, Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::pi(s1, s2)),
            ))
        }
        // Arithmetic and comparisons: typed a group at a time.
        Expr::Binary(..) => crate::numbers::group(cx, expr, None),
        Expr::If {
            binder,
            cond,
            then,
            otherwise,
            ..
        } => {
            let ty = cx.fresh_meta();
            let ty = cx.eval(&ty)?;
            let term = check_if(cx, binder.as_ref(), cond, then, otherwise, &ty)?;
            Ok((term, ty))
        }
        Expr::Ann(e, ty, _) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let e = check(cx, e, &ty_value)?;
            Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_value))
        }
        Expr::Record { base: None, .. } => Err(cx
            .error(
                "E-CANNOT-INFER",
                "can't tell which record type this literal is",
                "nothing here says what type it should have",
            )
            .with_note("add a type annotation, as in `({ x = 0, y = 0 } : Point)`")),
        Expr::Record {
            base: Some(base),
            fields,
            ..
        } => records::infer_update(cx, base, fields),
        Expr::Field(e, field) => crate::dot::infer_dot(cx, e, field, &[]),
        Expr::List(..) => {
            let list = builtin_data(cx, Builtin::List)?;
            let elem = cx.fresh_meta();
            let ty = Value::Data(list, vec![cx.eval(&elem)?]);
            let term = check(cx, expr, &ty)?;
            Ok((annotate(cx, term, &ty)?, ty))
        }
    }
}

/// Infers a function on its own, ready to be applied (a name, without
/// inserting its implicit arguments).
pub(crate) fn infer_head(cx: &mut Ctx, head: &Expr) -> Result<(Term, Value)> {
    infer_app(cx, head, &[])
}

/// Infers an application `head args`.
pub(crate) fn infer_app(cx: &mut Ctx, head: &Expr, args: &[Arg]) -> Result<(Term, Value)> {
    let g = cx.g();
    if let Expr::Field(recv, field) = head {
        return crate::dot::infer_dot(cx, recv, field, args);
    }
    let Expr::Var(name) = head else {
        let head = infer(cx, head)?;
        return apply_args(cx, head, args);
    };
    if let Some(level) = cx.lookup(&name.text) {
        let head = (Term::Var(cx.level() - 1 - level), cx.types[level].clone());
        return apply_args(cx, head, args);
    }
    if let Some(fields) = as_fields(cx, name) {
        return infer_app(cx, &fields, args);
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
    match cx.e.named(&name.text) {
        None => Err(cx.e.not_found(name)),
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
                let ty = eval(g, &params, param_ty)?;
                let term = check(cx, arg, &ty)?;
                params.push(cx.eval(&term)?);
                terms.push(term);
            }
            let head = (Term::data(*d, terms), Value::Sort(data.sort));
            apply_args(cx, head, &args[n..])
        }
        Some((Global::Unchecked(item), _)) => Err(cx.e.unchecked(name, *item)),
        Some((Global::Failed, _)) => Err(crate::module::failed_name(name)),
        Some((Global::Ability(_), _)) => Err(cx.error(
            "E-ABILITY",
            format!("`{}` is an ability, not a type or a value", name.text),
            "abilities go in a function type's row: `-> {State s} …`",
        )),
        Some((Global::Op(a, i), _)) if args.is_empty() => {
            let (term, ty) = effects::op_value(cx, *a, *i)?;
            let ty_term = cx.quote(&ty)?;
            Ok((Term::Ann(Rc::new(term), Rc::new(ty_term)), ty))
        }
        Some((Global::Op(a, _), _)) => {
            let ability = cx.e.abilities[*a].name.clone();
            Err(cx
                .error(
                    "E-ABILITY",
                    format!(
                        "`{}` is an operation of `{ability}`, which isn't allowed here",
                        name.text
                    ),
                    "this function's type has no abilities",
                )
                .with_note(format!(
                    "add `{ability}` to the function's type: `-> {{{ability} …}} …`"
                )))
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
                let expected = fresh_function_type(cx, missing)?;
                let expected = cx.eval(&expected)?;
                let (term, ty) = ctor_app(cx, *d, *c, &explicit, Some(&expected))?;
                let ann = Term::Ann(Rc::new(term), Rc::new(cx.quote(&ty)?));
                return Ok((ann, ty));
            }
            let (term, ty) = ctor_app(cx, *d, *c, &explicit, None)?;
            Ok((annotate(cx, term, &ty)?, ty))
        }
    }
}

/// `?a1 -> … -> ?an -> ?b`, with each type a fresh metavariable.
fn fresh_function_type(cx: &mut Ctx, arity: usize) -> Result<Term> {
    if arity == 0 {
        return Ok(cx.fresh_meta());
    }
    let dom = cx.fresh_meta();
    let mark = cx.mark();
    let dom_value = cx.eval(&dom)?;
    cx.bind_hidden("x".into(), dom_value);
    let cod = fresh_function_type(cx, arity - 1)?;
    cx.reset(mark);
    Ok(Term::Pi(
        "x".into(),
        Icit::Explicit,
        Rc::new(dom),
        Rc::new(cod),
    ))
}

fn explicit_args<'a>(cx: &Ctx, args: &[Arg<'a>]) -> Result<Vec<&'a Expr>> {
    args.iter()
        .map(|a| match a {
            Arg::Explicit(e) => Ok(*e),
            Arg::Named(..) => {
                Err(cx.error("E-ARITY", "constructors don't take named arguments", "here"))
            }
            Arg::Piped(_) => unreachable!("`|>` applies a constructor as a function"),
        })
        .collect()
}

/// Applies `head` to one argument, which may be a named implicit `[x := e]`.
pub(crate) fn apply_one(cx: &mut Ctx, head: (Term, Value), arg: &Expr) -> Result<(Term, Value)> {
    let arg = match arg {
        Expr::NamedArg(name, value, _) => Arg::Named(name, value),
        other => Arg::Explicit(other),
    };
    apply_args(cx, head, &[arg])
}

/// Applies `head` to `args`, inserting implicit arguments where needed.
pub(crate) fn apply_args(cx: &mut Ctx, head: (Term, Value), args: &[Arg]) -> Result<(Term, Value)> {
    apply_args_with(cx, head, args, &mut Supply::new())
}

/// Implicit arguments made in advance, used in order before any new ones:
/// those [`written_result`] made, so the application is elaborated with the
/// metavariables its expected type has already been compared with.
pub(crate) type Supply = std::collections::VecDeque<Term>;

/// [`apply_args`], taking implicit arguments from `supply` first.
pub(crate) fn apply_args_with(
    cx: &mut Ctx,
    head: (Term, Value),
    args: &[Arg],
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    let (mut term, mut ty) = head;
    for arg in args {
        match arg {
            Arg::Named(name, value) => {
                (term, ty) = insert_until(cx, term, ty, name, supply)?;
                let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone())? else {
                    unreachable!("insert_until stops at the named implicit parameter");
                };
                let value = check(cx, value, &dom)?;
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                term = Term::app_icit(term, value, icit);
            }
            Arg::Piped(piped) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (dom, cod) = function_parts(cx, &ty)?;
                if !cx.unify(&piped.ty, &dom)? {
                    return Err(piped_mismatch(cx, piped, &dom));
                }
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &piped.term))?;
                term = Term::app(term, piped.term.clone());
            }
            Arg::Explicit(value) => {
                (term, ty) = insert_with(cx, term, ty, supply)?;
                let (dom, cod) = function_parts(cx, &ty)?;
                let value = match check(cx, value, &dom) {
                    Ok(value) => value,
                    Err(e) if e.code == "E-PARTIAL-ESCAPE" => {
                        return Err(partial_callback(cx, &term, value, &dom).unwrap_or(e));
                    }
                    Err(e) => return Err(e),
                };
                ty = cod.apply_lazy(cx.g(), || eval(cx.g(), &cx.env, &value))?;
                term = Term::app(term, value);
            }
        }
    }
    Ok((term, ty))
}

/// The domain and codomain of `ty`, a function type with an explicit
/// parameter (made one, if it's unknown).
pub(crate) fn function_parts(cx: &mut Ctx, ty: &Value) -> Result<(Value, Closure)> {
    match force(cx.g(), ty.clone())? {
        Value::Pi(_, Icit::Explicit, dom, cod) => Ok(((*dom).clone(), cod)),
        Value::Neutral(Head::Meta(_), _) => {
            // Unknown type: it must be a function type.
            let dom = cx.fresh_meta();
            let dom = cx.eval(&dom)?;
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
            if !cx.unify(ty, &pi)? {
                return Err(cx.mismatch(&pi, ty));
            }
            Ok((dom, cod))
        }
        other => Err(cx.error(
            "E-NOT-A-FUNCTION",
            "this isn't a function",
            format!(
                "it's applied to an argument, but its type is `{}`",
                cx.show(&other)
            ),
        )),
    }
}

/// `x |> f`, where `x`'s type isn't what `f` takes.
pub(crate) fn piped_mismatch(cx: &Ctx, piped: &Piped, dom: &Value) -> Diagnostic {
    Diagnostic::error(
        "E-TYPE-MISMATCH",
        "the value piped in doesn't fit the function",
    )
    .with_label(
        piped.span,
        format!(
            "this takes `{}` as its last argument, but the value before `|>` has type `{}`",
            cx.show(dom),
            cx.show(&piped.ty)
        ),
    )
}

/// A recursive call of the partial group being described, passed as `arg`
/// to `head`, whose parameter of type `dom` is a function with a fixed row:
/// nothing in `head` can answer its requests (docs/proposals/partial.md
/// §7.3.4).
fn partial_callback(cx: &Ctx, head: &Term, arg: &Expr, dom: &Value) -> Option<Diagnostic> {
    if !matches!(force(cx.g(), dom.clone()), Ok(Value::Pi(..))) {
        return None;
    }
    let helper = match head.spine().0 {
        Term::Def(id) => cx.g().def(*id).name.to_string(),
        Term::Var(ix) => cx.names[cx.level() - 1 - ix].to_string(),
        _ => return None,
    };
    let members = cx.e.recursion.as_ref()?.names.clone();
    let shown = |n: &String| format!("`{n}`");
    let what = match arg {
        Expr::Var(name) => format!("`{}`", name.text),
        _ => "this".to_string(),
    };
    let param = cx.show(dom);
    // The parameter's type with a row variable added to its last row.
    let suggested = match param.rfind('}') {
        Some(i) if !param[..i].contains('|') => format!("{} | e{}", &param[..i], &param[i..]),
        _ => param.clone(),
    };
    Some(
        Diagnostic::error(
            "E-PARTIAL-CALLBACK",
            format!("{what} can't be passed to `{helper}` here"),
        )
        .with_label(
            arg.span(),
            format!(
                "{what} calls {}, so as a value it makes requests that only {}'s own \
                 definition can answer",
                members.iter().map(shown).collect::<Vec<_>>().join(", "),
                shown(&members[0]),
            ),
        )
        .with_note(format!(
            "`{helper}`'s parameter has the type `{param}`, whose row is fixed"
        ))
        .with_note(format!(
            "make `{helper}` polymorphic in the rest of the row: give the parameter the type \
             `{suggested}`, and add `| e` to `{helper}`'s own row too"
        )),
    )
}

/// Applies `term` to a fresh metavariable for each leading implicit or auto
/// parameter. An auto argument is also recorded as an obligation, to be proved
/// once the declaration has been elaborated (see `auto.rs`).
pub fn insert(cx: &mut Ctx, term: Term, ty: Value) -> Result<(Term, Value)> {
    insert_with(cx, term, ty, &mut Supply::new())
}

/// [`insert`], taking implicit arguments from `supply` first.
fn insert_with(
    cx: &mut Ctx,
    mut term: Term,
    mut ty: Value,
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    while let Value::Pi(_, icit, dom, cod) = force(cx.g(), ty.clone())?
        && icit.is_implicit()
    {
        let meta = supplied_arg(cx, icit, &dom, supply);
        let value = cx.eval(&meta)?;
        term = Term::app_icit(term, meta, icit);
        ty = cod.apply(cx.g(), value)?;
    }
    Ok((term, ty))
}

pub(crate) fn implicit_arg(cx: &mut Ctx, icit: Icit, ty: &Value) -> Term {
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

/// An implicit argument from `supply`, or a new one. ([`written_result`]
/// makes no auto arguments; `pipe.rs` makes them with [`implicit_arg`], so
/// they're recorded as obligations.)
fn supplied_arg(cx: &mut Ctx, icit: Icit, ty: &Value, supply: &mut Supply) -> Term {
    match supply.pop_front() {
        Some(arg) => arg,
        None => implicit_arg(cx, icit, ty),
    }
}

/// Inserts implicit arguments up to the implicit parameter called `name`.
fn insert_until(
    cx: &mut Ctx,
    mut term: Term,
    mut ty: Value,
    name: &AstName,
    supply: &mut Supply,
) -> Result<(Term, Value)> {
    loop {
        match force(cx.g(), ty.clone())? {
            Value::Pi(x, icit, _, _) if icit.is_implicit() && *x == *name.text => {
                return Ok((term, ty));
            }
            Value::Pi(_, icit, dom, cod) if icit.is_implicit() => {
                let meta = supplied_arg(cx, icit, &dom, supply);
                let value = cx.eval(&meta)?;
                term = Term::app_icit(term, meta, icit);
                ty = cod.apply(cx.g(), value)?;
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
    cx.g().budget.nesting(PASS)?;
    let span = expr.span();
    with_span(cx, span, |cx| {
        let term = check_inner(cx, expr, expected)
            .map_err(|e| crate::numbers::explain_default(cx, e, &[expected]))?;
        Ok(Term::Loc(span, Rc::new(term)))
    })
}

fn check_inner(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let g = cx.g();
    let expected = force(g, expected.clone())?;
    // A computation in a row of abilities: computation mode.
    if !matches!(expr, Expr::Hole(_))
        && let Some((row, t)) = effects::comp_parts(cx, &expected)?
    {
        return effects::comp_check(cx, expr, &row, &t);
    }
    if effects::may_perform(cx, expr)? {
        return Ok(effects::run_pure(cx, expr, Some(&expected))?.0);
    }
    if let Some(logic) = crate::logic::classify(cx, expr) {
        return crate::logic::check_against(cx, logic, &expected);
    }
    match (expr, &expected) {
        (Expr::Unit(_), Value::Sort(_)) => {
            let unit = builtin_data(cx, Builtin::UnitType)?;
            let found = Value::Sort(Sort::Type(0));
            if cx.unify(&found, &expected)? {
                Ok(Term::Data(unit, Vec::new()))
            } else {
                Err(cx.mismatch(&expected, &found))
            }
        }
        (Expr::Hole(_), _) => Ok(cx.fresh_meta()),
        // `(A, B)` where a type is expected is `Pair A B`, and `(a, b)` where
        // a pair is expected is `MkPair a b`.
        (Expr::Tuple(a, b, _), Value::Sort(_)) => {
            let (term, ty) = type_tuple(cx, a, b)?;
            if cx.unify(&ty, &expected)? {
                Ok(term)
            } else {
                Err(cx.mismatch(&expected, &ty))
            }
        }
        (Expr::Tuple(a, b, _), Value::Data(d, params))
            if *d == builtin_data(cx, Builtin::Pair)? =>
        {
            let (pair, mk) = builtin_ctor(cx, Builtin::MkPair)?;
            let a = check(cx, a, &params[0])?;
            let b = check(cx, b, &params[1])?;
            Ok(Term::ctor(pair, mk, vec![a, b]))
        }
        // Implicit parameters are introduced automatically.
        (_, Value::Pi(x, icit, dom, cod)) if icit.is_implicit() => {
            let mark = cx.mark();
            let var = Value::var(cx.level());
            cx.bind_hidden(x.clone(), (**dom).clone());
            let result = check(cx, expr, &cod.apply(g, var)?);
            cx.reset(mark);
            Ok(Term::Lam(x.clone(), *icit, Rc::new(result?)))
        }
        // A literal takes its type from what's expected (a `Nat` or an
        // `Int`), and so does arithmetic.
        (Expr::Num(..) | Expr::Neg(..), _) if crate::numbers::literal(expr).is_some() => {
            let (k, negative) = crate::numbers::literal(expr).expect("just checked");
            crate::numbers::check_literal(cx, k, negative, &expected)
        }
        (Expr::Binary(op, ..), _) if crate::numbers::is_arith(*op) => {
            Ok(crate::numbers::group(cx, expr, Some(&expected))?.0)
        }
        (Expr::Neg(..), _) => Ok(crate::numbers::group(cx, expr, Some(&expected))?.0),
        (Expr::Match { .. }, _) => crate::matching::check_match(cx, expr, &expected),
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
            let cod = cod.apply(g, var)?;
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
            if cx.unify(a, b)? {
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
            let (list, nil) = builtin_ctor(cx, Builtin::Nil)?;
            let (_, cons) = builtin_ctor(cx, Builtin::Cons)?;
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
                term = Term::ctor(list, cons, vec![item, term]);
            }
            Ok(term)
        }
        (Expr::Var(_) | Expr::App(..), Value::Data(..) | Value::Pi(_, Icit::Explicit, _, _)) => {
            match ctor_head(cx, expr)? {
                Some((d, c, args)) => {
                    let (term, ty) = ctor_app(cx, d, c, &args, Some(&expected))?;
                    if cx.unify(&ty, &expected)? {
                        Ok(term)
                    } else {
                        Err(cx.mismatch(&expected, &ty))
                    }
                }
                None => fallback(cx, expr, &expected),
            }
        }
        (Expr::Record { base, fields, .. }, _) => {
            records::check_record(cx, base.as_deref(), fields, &expected)
        }
        _ => fallback(cx, expr, &expected),
    }
}

/// `'a'` is `MkChar 97 rfl`: the kernel checks that 97 is a scalar value by
/// computing `isScalar 97`.
fn char_term(cx: &Ctx, c: char) -> Result<Term> {
    let (char_data, mk_char) = builtin_ctor(cx, Builtin::MkChar)?;
    let code = Term::Nat(Rc::new(u32::from(c).into()));
    Ok(Term::ctor(char_data, mk_char, vec![code, Term::Refl]))
}

/// `a ++ b`: `textAppend` for texts, `append` for lists, chosen by the type of
/// whichever side can be inferred.
fn append(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let (a, b, ty) = match infer(cx, a).and_then(|(t, ty)| insert(cx, t, ty)) {
        Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
        Err(e) if e.code == "E-CANNOT-INFER" => {
            let (b, ty) = infer(cx, b)?;
            let (b, ty) = insert(cx, b, ty)?;
            (check(cx, a, &ty)?, b, ty)
        }
        Err(e) => return Err(e),
    };
    let text = builtin_data(cx, Builtin::Text)?;
    let list = builtin_data(cx, Builtin::List)?;
    let head = match force(cx.g(), ty.clone())? {
        Value::Data(d, _) if d == text => Term::Def(builtin_def(cx, Builtin::TextAppend)?),
        Value::Data(d, params) if d == list => {
            let elem = cx.quote(&params[0])?;
            Term::app_icit(
                Term::Def(builtin_def(cx, Builtin::Append)?),
                elem,
                Icit::Implicit,
            )
        }
        other => {
            return Err(cx.error(
                "E-TYPE-MISMATCH",
                "`++` joins two texts or two lists",
                format!("this is a `{}`", cx.show(&other)),
            ));
        }
    };
    Ok((Term::app(Term::app(head, a), b), ty))
}

/// `if c then a else b` is `ifThenElse c (\_ -> a) (\_ -> b)`, and
/// `if h : P then a else b` is `elimDec (decision for P) (\h -> a) (\h -> b)`.
/// The branches are functions so only the chosen one is evaluated.
///
/// `if c` with no binder where `c` isn't a `Bool` but a proposition is
/// `if _ : c` (as in Lean): `if x < y`. The `Bool` reading is tried first,
/// exactly as before, so a `Bool` condition elaborates as it always has;
/// only if it fails is everything it did undone and `c` tried as a
/// proposition. If that fails too, the `Bool` reading's error is reported,
/// unless `c` is a proposition with no decision procedure.
pub(crate) fn check_if(
    cx: &mut Ctx,
    binder: Option<&AstName>,
    cond: &Expr,
    then: &Expr,
    otherwise: &Expr,
    expected: &Value,
) -> Result<Term> {
    let result_ty = cx.quote(expected)?;
    let branch = |cx: &mut Ctx, name: &str, ty: Value, body: &Expr| -> Result<Term> {
        let mark = cx.mark();
        cx.bind(name, ty);
        let result = check(cx, body, expected);
        cx.reset(mark);
        Ok(Term::Lam(name.into(), Icit::Explicit, Rc::new(result?)))
    };
    match binder {
        None => {
            let unit_data = builtin_data(cx, Builtin::Unit)?;
            let cond = match crate::logic::condition(cx, cond, "if")? {
                crate::logic::Condition::Bool(cond) => cond,
                crate::logic::Condition::Decided { prop, decision } => {
                    return decided_if(
                        cx, "_", prop, decision, result_ty, &branch, then, otherwise,
                    );
                }
            };
            let unit = Value::Data(unit_data, Vec::new());
            let then = branch(cx, "_", unit.clone(), then)?;
            let otherwise = branch(cx, "_", unit, otherwise)?;
            let ite = builtin_def(cx, Builtin::IfThenElse)?;
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
            let decision = crate::auto::decide(cx, &cx.eval(&prop)?, 0)?;
            decided_if(
                cx, &h.text, prop, decision, result_ty, &branch, then, otherwise,
            )
        }
    }
}

/// `elimDec decision (\name -> then) (\name -> otherwise)`, where `decision`
/// decides `prop`: `name` is a proof of `prop` in `then` and of `Not prop`
/// in `otherwise`.
#[allow(clippy::too_many_arguments)]
fn decided_if(
    cx: &mut Ctx,
    name: &str,
    prop: Term,
    decision: Term,
    result_ty: Term,
    branch: &dyn Fn(&mut Ctx, &str, Value, &Expr) -> Result<Term>,
    then: &Expr,
    otherwise: &Expr,
) -> Result<Term> {
    let prop_value = cx.eval(&prop)?;
    let not = builtin_def(cx, Builtin::Not)?;
    let not_prop = cx.eval(&Term::app(Term::Def(not), prop.clone()))?;
    let then = branch(cx, name, prop_value, then)?;
    let otherwise = branch(cx, name, not_prop, otherwise)?;
    let elim = builtin_def(cx, Builtin::ElimDec)?;
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

/// Checks `expr` by inferring its type and comparing. An application whose
/// result type is known before its arguments are checked is compared with
/// `expected` first, so the arguments are checked knowing more
/// (docs/proposals/syntax-conveniences.md §7).
fn fallback(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    if cx.e.no_propagation.get() == 0
        && let Some(found) = propagate(cx, expr, expected)?
    {
        return found;
    }
    let (term, found) = infer(cx, expr)?;
    let (term, found) = insert(cx, term, found)?;
    compare(cx, term, &found, expected)
}

/// `term`, of type `found`, where `expected` is expected.
pub(crate) fn compare(cx: &mut Ctx, term: Term, found: &Value, expected: &Value) -> Result<Term> {
    if crate::undo::unify(cx, found, expected)? {
        return Ok(term);
    }
    // An effectful function whose row lists the same abilities in a
    // different order, or a total one where a partial one is expected.
    if let Some(term) =
        crate::undo::transaction(cx, |cx| effects::coerce(cx, &term, found, expected))?
    {
        return Ok(term);
    }
    // The message shows the types as the failed comparison left them, as it
    // always has: repeat it, keeping what it solved before failing.
    cx.unify(found, expected)?;
    if let Some(d) = effects::partial_mismatch(cx, found, expected)? {
        Err(d)
    } else {
        Err(crate::numbers::explain_default(
            cx,
            cx.mismatch(expected, found),
            &[found],
        ))
    }
}

/// Checks the application `expr` against `expected`, comparing its result
/// type with `expected` first (§7.2); `None` if that doesn't apply: `expr`
/// isn't an application of a variable or a definition, or its result type
/// depends on the arguments written or isn't known, or doesn't match
/// `expected` (and then nothing has changed). If it applies but the
/// application then fails, everything is undone and the application is
/// elaborated again the old way, with no propagation inside, and that way's
/// result is the answer: so a program rejected before keeps its message
/// (§7.4).
fn propagate(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Option<Result<Term>>> {
    if matches!(
        force(cx.g(), expected.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return Ok(None);
    }
    let mut args = Vec::new();
    let mut head = expr;
    while let Expr::App(f, a) = head {
        args.push(match a.as_ref() {
            Expr::NamedArg(name, value, _) => Arg::Named(name, value),
            other => Arg::Explicit(other),
        });
        head = f;
    }
    if args.is_empty() {
        return Ok(None);
    }
    args.reverse();
    let Some(head) = known_head(cx, head) else {
        return Ok(None);
    };
    let snapshot = crate::undo::Snapshot::take(cx);
    let Some((written, mut supply)) = written_result(cx, &head.1, &args)? else {
        snapshot.restore(cx);
        return Ok(None);
    };
    if !cx.unify(&written, expected)? {
        snapshot.restore(cx);
        return Ok(None);
    }
    // As `infer` and then `insert` would, for the application.
    let span = expr.span();
    let result = (|| -> Result<Term> {
        cx.g().budget.nesting(PASS)?;
        let (term, found) = apply_args_with(cx, head, &args, &mut supply)?;
        let term = Term::Loc(span, Rc::new(term));
        let (term, found) = insert_with(cx, term, found, &mut supply)?;
        if !supply.is_empty() {
            // The types as elaborated didn't line up with the walk's.
            return Err(Diagnostic::error(
                "E-PROPAGATE",
                "unused implicit arguments",
            ));
        }
        compare(cx, term, &found, expected)
    })();
    match result {
        Ok(term) => Ok(Some(Ok(term))),
        Err(e) if crate::undo::fatal(&e) => Err(e),
        Err(_) => {
            snapshot.restore(cx);
            let off = &cx.e.no_propagation;
            off.set(off.get() + 1);
            let old = (|| {
                let (term, found) = infer(cx, expr)?;
                let (term, found) = insert(cx, term, found)?;
                compare(cx, term, &found, expected)
            })();
            let off = &cx.e.no_propagation;
            off.set(off.get() - 1);
            Ok(Some(old))
        }
    }
}

/// The function at the head of an application, if it's a variable or a
/// definition, as `infer_app` finds it (without inserting implicit
/// arguments).
pub(crate) fn known_head(cx: &Ctx, head: &Expr) -> Option<(Term, Value)> {
    let Expr::Var(name) = head else {
        return None;
    };
    if let Some(level) = cx.lookup(&name.text) {
        return Some((Term::Var(cx.level() - 1 - level), cx.types[level].clone()));
    }
    if as_fields(cx, name).is_some() || matches!(name.text.as_str(), "rfl" | "J") {
        return None;
    }
    match cx.e.named(&name.text) {
        Some((Global::Def(id), _)) => Some((Term::Def(*id), cx.g().def(*id).ty_value.clone())),
        _ => None,
    }
}

/// The type of the application of a function of type `ty` to `args`, before
/// they're checked (§7.2): implicit parameters get metavariables, as
/// `apply_args` and then `insert` would give them, returned in order;
/// parameters given by `args` get fresh variables. `None` if the type
/// mentions those variables (it depends on the arguments' values), or isn't
/// known, or an auto parameter is met before or after (solving the result
/// first could change what proof search finds).
fn written_result(cx: &mut Ctx, ty: &Value, args: &[Arg]) -> Result<Option<(Value, Supply)>> {
    let g = cx.g();
    let base = cx.level();
    let mut ty = ty.clone();
    let mut supply = Supply::new();
    let mut written = 0;
    for arg in args {
        let stop = |x: &Name, icit: Icit| match arg {
            Arg::Named(name, _) => icit.is_implicit() && **x == *name.text,
            Arg::Explicit(_) | Arg::Piped(_) => icit == Icit::Explicit,
        };
        let Some(Value::Pi(_, icit, _, cod)) = implicits(cx, &mut ty, &mut supply, stop)? else {
            return Ok(None);
        };
        if icit == Icit::Auto {
            return Ok(None);
        }
        ty = cod.apply(g, Value::var(base + written))?;
        written += 1;
    }
    if implicits(cx, &mut ty, &mut supply, |_, _| false)?.is_none() {
        return Ok(None);
    }
    // What's left: an auto parameter anywhere in it rules propagation out.
    let term = quote(g, base + written, &ty)?;
    let mut rest = &term;
    while let Term::Pi(_, icit, _, cod) = rest {
        if *icit == Icit::Auto {
            return Ok(None);
        }
        rest = cod;
    }
    if (0..written).any(|i| term.mentions(i)) {
        return Ok(None);
    }
    Ok(Some((ty, supply)))
}

/// Gives the implicit parameters at the front of `ty` metavariables, added
/// to `supply`, until `stop` says to stop at one: that parameter's function
/// type (or `ty`, forced, if it isn't a function type). `None` at an auto
/// parameter.
fn implicits(
    cx: &mut Ctx,
    ty: &mut Value,
    supply: &mut Supply,
    stop: impl Fn(&Name, Icit) -> bool,
) -> Result<Option<Value>> {
    let g = cx.g();
    loop {
        let forced = force(g, ty.clone())?;
        match &forced {
            Value::Pi(x, icit, _, _) if stop(x, *icit) => return Ok(Some(forced)),
            Value::Pi(_, Icit::Auto, _, _) => return Ok(None),
            Value::Pi(_, Icit::Implicit, _, cod) => {
                let meta = cx.fresh_meta();
                let value = cx.eval(&meta)?;
                supply.push_back(meta);
                *ty = cod.apply(g, value)?;
            }
            _ => return Ok(Some(forced)),
        }
    }
}

/// The prelude's data type `b`, which syntax stands for (the built-in
/// registry, docs/proposals/namespaces.md §4.7): by identity, never by what
/// its name means here.
pub fn builtin_data(cx: &Ctx, b: Builtin) -> Result<DataId> {
    cx.g()
        .registry
        .data(b)
        .ok_or_else(|| missing_builtin(cx, b))
}

/// The prelude's constructor `b`: its data type and index.
pub fn builtin_ctor(cx: &Ctx, b: Builtin) -> Result<(DataId, usize)> {
    cx.g()
        .registry
        .ctor(b)
        .ok_or_else(|| missing_builtin(cx, b))
}

/// The prelude's definition `b`.
pub fn builtin_def(cx: &Ctx, b: Builtin) -> Result<stitchwort_core::DefId> {
    cx.g().registry.def(b).ok_or_else(|| missing_builtin(cx, b))
}

/// Only while the prelude loads, before `b`'s declaration is admitted: user
/// code isn't elaborated until every built-in is bound.
fn missing_builtin(cx: &Ctx, b: Builtin) -> Diagnostic {
    cx.error(
        "E-UNKNOWN-NAME",
        format!("this needs the prelude's `{}`", b.name()),
        "here",
    )
}

/// A qualified name that's really field access: its first component is a
/// local variable (`P.name`), or it names a declaration followed by
/// components that don't (`Origin.x`).
fn as_fields(cx: &Ctx, name: &AstName) -> Option<Expr> {
    let (first, _) = name.text.split_once('.')?;
    let parts: Vec<&str> = name.text.split('.').collect();
    let taken = if cx.lookup(first).is_some() {
        1
    } else {
        match cx.e.resolve(&name.text) {
            crate::scope::Resolved::Found { rest, .. } if !rest.is_empty() => {
                parts.len() - rest.len()
            }
            _ => return None,
        }
    };
    let mut expr = Expr::Var(AstName {
        text: parts[..taken].join("."),
        span: name.span,
    });
    for field in &parts[taken..] {
        expr = Expr::Field(
            Box::new(expr),
            AstName {
                text: field.to_string(),
                span: name.span,
            },
        );
    }
    Some(expr)
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
    if cx.lookup(&name.text).is_some() || as_fields(cx, name).is_some() {
        return Ok(None);
    }
    match cx.e.named(&name.text) {
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
        match target.as_ref().map(|t| force(g, t.clone())).transpose()? {
            Some(Value::Pi(_, Icit::Explicit, dom, cod)) => {
                let var = Value::var(cx.level());
                let name: Name = ctor.fields[i].0.clone();
                cx.bind_hidden(name.clone(), (*dom).clone());
                missing_types.push(name);
                target = Some(cod.apply(g, var)?);
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

    let params = match target.as_ref().map(|t| force(g, t.clone())).transpose()? {
        Some(Value::Data(d2, params)) if d2 == d => params,
        _ => data
            .params
            .iter()
            .map(|_| {
                let meta = cx.fresh_meta();
                cx.eval(&meta)
            })
            .collect::<Result<_>>()?,
    };
    let mut env = params.clone();
    let mut terms = Vec::new();
    let first_missing_level = mark.level;
    for (i, (_, field_ty)) in ctor.fields.iter().enumerate() {
        let ty = eval(g, &env, field_ty)?;
        let term = if let Some(arg) = args.get(i) {
            check(cx, arg, &ty)?
        } else {
            let level = first_missing_level + (i - args.len());
            let found = cx.types[level].clone();
            if !cx.unify(&found, &ty)? {
                cx.reset(mark);
                return Err(cx.mismatch(&ty, &found));
            }
            Term::Var(cx.level() - 1 - level)
        };
        env.push(if kernel::later_types_mention(&ctor.fields, i) {
            cx.eval(&term)?
        } else {
            unused()
        });
        terms.push(term);
    }
    let result_ty = Value::Data(d, params);
    if let Some(target) = &target
        && !cx.unify(&result_ty, target)?
    {
        let error = cx.mismatch(target, &result_ty);
        cx.reset(mark);
        return Err(error);
    }
    cx.reset(mark);
    let mut term = Term::ctor(d, c, terms);
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
fn annotate(cx: &Ctx, term: Term, ty: &Value) -> Result<Term> {
    Ok(match ty {
        Value::Data(d, _) if !cx.g().data(*d).params.is_empty() => {
            Term::Ann(Rc::new(term), Rc::new(cx.quote(ty)?))
        }
        _ => term,
    })
}

/// `Pair A B` for `(A, B)`: each component must be a type in `Type`, as
/// `Pair`'s parameters are (a proposition can't be a component).
fn type_tuple(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let pair = builtin_data(cx, Builtin::Pair)?;
    let mut parts = Vec::new();
    for part in [a, b] {
        let (term, sort) = check_type(cx, part)?;
        if sort != Sort::Type(0) {
            return Err(cx.mismatch(&Value::Sort(Sort::Type(0)), &Value::Sort(sort)));
        }
        parts.push(Rc::new(term));
    }
    Ok((Term::Data(pair, parts), Value::Sort(Sort::Type(0))))
}

/// `(a, b)` with no expected type: a type tuple if the first component's
/// type is a universe, otherwise a value tuple.
fn infer_tuple(cx: &mut Ctx, a: &Expr, b: &Expr) -> Result<(Term, Value)> {
    let (ta, tya) = infer(cx, a)?;
    if let Value::Sort(_) = force(cx.g(), tya.clone())? {
        return type_tuple(cx, a, b);
    }
    let (tb, tyb) = infer(cx, b)?;
    let (pair, mk) = builtin_ctor(cx, Builtin::MkPair)?;
    Ok((
        Term::ctor(pair, mk, vec![ta, tb]),
        Value::Data(pair, vec![tya, tyb]),
    ))
}

pub fn check_type(cx: &mut Ctx, expr: &Expr) -> Result<(Term, Sort)> {
    let span = expr.span();
    if let Expr::Unit(_) = expr {
        return Ok((
            Term::Data(builtin_data(cx, Builtin::UnitType)?, Vec::new()),
            Sort::Type(0),
        ));
    }
    // A tuple where a type is wanted is a type tuple, whatever its components
    // look like (a function's domain, for one).
    if let Expr::Tuple(a, b, _) = expr {
        let (term, _) = type_tuple(cx, a, b)?;
        return Ok((term, Sort::Type(0)));
    }
    // `p && q`, `p || q` and `not p` where a type is wanted are propositions.
    if let Some(logic) = crate::logic::classify(cx, expr) {
        let span = expr.span();
        let term = with_span(cx, span, |cx| crate::logic::as_prop(cx, logic))?;
        return Ok((Term::Loc(span, Rc::new(term)), Sort::Prop));
    }
    let (term, ty) = infer(cx, expr)?;
    match force(cx.g(), ty)? {
        Value::Sort(s) => Ok((term, s)),
        ty @ Value::Neutral(Head::Meta(_), _) => {
            // An unknown type of types defaults to `Type`.
            if cx.unify(&ty, &Value::Sort(Sort::Type(0)))? {
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
    let (proof, proof_ty) = insert(cx, proof, proof_ty)?;
    let Value::Eq(ty, x, y) = force(g, proof_ty.clone())? else {
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
    let motive_value = cx.eval(&motive)?;
    let base_ty = apply(
        g,
        apply(g, motive_value.clone(), (*x).clone())?,
        Value::Refl,
    )?;
    let base = check(cx, base, &base_ty)?;
    let proof_value = cx.eval(&proof)?;
    let result = apply(g, apply(g, motive_value, (*y).clone())?, proof_value)?;
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
pub(crate) fn nat(cx: &Ctx) -> Result<DataId> {
    cx.e.globals
        .builtins
        .nat
        .ok_or_else(|| cx.error("E-UNKNOWN-NAME", "numbers need the prelude's `Nat`", "here"))
}

/// Arguments as written, for [`apply_args`].
pub(crate) fn args_of(exprs: &[Expr]) -> Vec<Arg<'_>> {
    exprs
        .iter()
        .map(|a| match a {
            Expr::NamedArg(name, value, _) => Arg::Named(name, value),
            other => Arg::Explicit(other),
        })
        .collect()
}
