//! The type checker for core terms. See `docs/core.md` for the rules.
//!
//! Checking also completes terms: it fills in the type of each `a = b`, which
//! evaluation needs.

use std::rc::Rc;

use stitchwort_syntax::{Diagnostic, Span};

use crate::budget;
use crate::globals::{Ctor, Data, Def, FieldValidator, Globals, State, Validator};
use crate::pretty;
use crate::term::{Branch, DataId, DefId, Icit, Name, NumArm, Sort, Term};
use crate::termination;
use crate::value::{Value, apply, conv, eval, quote, unused};

type Result<T> = std::result::Result<T, Diagnostic>;

/// The typing context: a value and a type for each variable in scope.
pub struct Ctx<'g> {
    g: &'g Globals,
    /// What each variable evaluates to. Normally the variable itself, but
    /// inside a case branch the matched variable is the constructor value.
    /// For a `let` whose value hasn't been needed yet, its slot holds a
    /// placeholder (the slot's own variable) and `pending` holds the value
    /// term; see [`Ctx::define`].
    env: Vec<Value>,
    types: Vec<Value>,
    names: Vec<Name>,
    /// For each slot, the value term of a `let` not computed yet, in the
    /// context of the slots before it. Kernel-local: nothing computed here
    /// is kept in a term or shared with the elaborator.
    pending: Vec<Option<Rc<Term>>>,
    /// How many entries of `pending` are `Some`: when none are, evaluation
    /// needs no look at its term first.
    unforced: usize,
    span: Span,
}

impl<'g> Ctx<'g> {
    pub fn new(g: &'g Globals, span: Span) -> Self {
        Ctx {
            g,
            env: Vec::new(),
            types: Vec::new(),
            names: Vec::new(),
            pending: Vec::new(),
            unforced: 0,
            span,
        }
    }

    fn level(&self) -> usize {
        self.env.len()
    }

    fn bind(&mut self, name: Name, ty: Value) {
        self.env.push(Value::var(self.level()));
        self.types.push(ty);
        self.names.push(name);
        self.pending.push(None);
    }

    /// A transparent local definition `x : ty := value`: it takes a slot
    /// (terms under it count it), but no neutral variable stands for it,
    /// since it evaluates to `value` (docs/proposals/let.md §A.2). So no
    /// value computed under it can mention it, and none can escape its scope.
    ///
    /// `value` is computed only when checking first evaluates a term that
    /// mentions `x`, and then once ([`Ctx::eval`]): a `let` whose value no
    /// type needs costs nothing to check, as the function form `(\x => b) v`
    /// didn't (docs/proposals/let.md §A.2, "Cost at check time"). Until then
    /// the slot holds its own variable as a placeholder, which nothing reads:
    /// every evaluation in the checker goes through `Ctx::eval`.
    fn define(&mut self, name: Name, ty: Value, value: Rc<Term>) {
        self.env.push(Value::var(self.level()));
        self.types.push(ty);
        self.names.push(name);
        self.pending.push(Some(value));
        self.unforced += 1;
    }

    fn unbind(&mut self, n: usize) {
        let keep = self.level() - n;
        self.env.truncate(keep);
        self.types.truncate(keep);
        self.names.truncate(keep);
        self.unforced -= self.pending[keep..].iter().filter(|p| p.is_some()).count();
        self.pending.truncate(keep);
    }

    /// Evaluates `term` in the context, first computing the value of each
    /// `let` it mentions whose value hasn't been needed yet.
    fn eval(&mut self, term: &Term) -> Result<Value> {
        self.force_mentioned(term, self.level())?;
        Ok(eval(self.g, &self.env, term)?)
    }

    /// Computes the pending `let`s that `term`, in the context of the first
    /// `depth` slots, mentions (and, through their values, the ones those
    /// mention).
    fn force_mentioned(&mut self, term: &Term, depth: usize) -> Result<()> {
        if self.unforced == 0 {
            return Ok(());
        }
        let mut wanted = Vec::new();
        for (t, binders) in term.subterms() {
            if let Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) = t
                && let Some(ix) = ix.checked_sub(binders)
                && let Some(level) = depth.checked_sub(ix + 1)
                && self.pending.get(level).is_some_and(Option::is_some)
            {
                wanted.push(level);
            }
        }
        for level in wanted {
            self.force(level)?;
        }
        Ok(())
    }

    /// Computes the value of the pending `let` in slot `level`, if it's still
    /// pending. On an error (out of resources) it stays pending.
    fn force(&mut self, level: usize) -> Result<()> {
        let Some(value) = self.pending[level].clone() else {
            return Ok(());
        };
        self.g.budget.nesting(PASS)?;
        self.force_mentioned(&value, level)?;
        let computed = eval(self.g, &self.env[..level], &value)?;
        self.env[level] = computed;
        self.pending[level] = None;
        self.unforced -= 1;
        Ok(())
    }

    /// Computes every pending `let`, for code that reads the whole
    /// environment.
    fn force_all(&mut self) -> Result<()> {
        for level in 0..self.level() {
            self.force(level)?;
        }
        Ok(())
    }

    fn quote(&self, value: &Value) -> Result<Term> {
        Ok(quote(self.g, self.level(), value)?)
    }

    fn conv(&self, a: &Value, b: &Value) -> Result<bool> {
        Ok(conv(self.g, self.level(), a, b)?)
    }

    fn show(&self, value: &Value) -> String {
        pretty::value(self.g, &self.names, value)
    }

    fn error(
        &self,
        code: &'static str,
        message: impl Into<String>,
        label: impl Into<String>,
    ) -> Diagnostic {
        Diagnostic::error(code, message).with_label(self.span, label)
    }

    fn mismatch(&self, expected: &Value, found: &Value) -> Diagnostic {
        if let (Value::Sort(_), Value::Sort(_)) = (expected, found) {
            return self
                .error(
                    "E-UNIVERSE",
                    "universe mismatch",
                    format!(
                        "expected something of type `{}`, but this has type `{}`",
                        self.show(expected),
                        self.show(found)
                    ),
                )
                .with_note("`Type n` lives in `Type (n+1)`; allowing `Type : Type` would make the logic inconsistent");
        }
        self.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "expected `{}`, but this has type `{}`",
                self.show(expected),
                self.show(found)
            ),
        )
    }
}

/// The name the type checker's depth guard reports.
const PASS: &str = "type checker";

pub fn infer(cx: &mut Ctx, term: &Term) -> Result<(Term, Value)> {
    let g = cx.g;
    g.budget.nesting(PASS)?;
    match term {
        Term::Loc(span, inner) => {
            let saved = std::mem::replace(&mut cx.span, *span);
            let result = infer(cx, inner);
            cx.span = saved;
            let (inner, ty) = result?;
            Ok((Term::Loc(*span, Rc::new(inner)), ty))
        }
        Term::Var(ix) if *ix < cx.level() => {
            Ok((term.clone(), cx.types[cx.level() - 1 - ix].clone()))
        }
        Term::Var(ix) => Err(malformed(cx, format!("variable {ix} is out of scope"))),
        Term::Def(id) => match g.defs.get(id.0) {
            Some(def) => Ok((term.clone(), def.ty_value.clone())),
            None => Err(malformed(cx, "reference to an unknown definition")),
        },
        Term::Data(d, args) => {
            let Some(data) = g.datas.get(d.0) else {
                return Err(malformed(cx, "reference to an unknown data type"));
            };
            if args.len() != data.params.len() {
                return Err(malformed(
                    cx,
                    format!("`{}` needs {} parameter(s)", data.name, data.params.len()),
                ));
            }
            let mut params = Vec::new();
            let mut out = Vec::new();
            for (i, ((_, param_ty), arg)) in data.params.iter().zip(args).enumerate() {
                let ty = eval(g, &params, param_ty)?;
                let arg = check(cx, arg, &ty)?;
                params.push(if later_types_mention(&data.params, i) {
                    cx.eval(&arg)?
                } else {
                    unused()
                });
                out.push(arg);
            }
            Ok((Term::data(*d, out), Value::Sort(data.sort)))
        }
        Term::Sort(s) => Ok((term.clone(), Value::Sort(s.succ()))),
        Term::Nat(_) => match g.builtins.nat {
            Some(nat) => Ok((term.clone(), Value::Data(nat, Vec::new()))),
            None => Err(malformed(cx, "a number, but `Nat` isn't defined")),
        },
        // A compact list of characters is a `List Char`: its expansion's
        // `rfl`s prove `isScalar c = True` because each `c` is a Rust `char`
        // (a scalar value) and `isScalar` is the one it was registered with.
        Term::Chars(_) => match &g.builtins.text {
            Some(text) => Ok((
                term.clone(),
                Value::Data(text.list, vec![Value::Data(text.char, Vec::new())]),
            )),
            None => Err(malformed(
                cx,
                "a compact list of characters, but `List` and `Char` aren't registered for it",
            )),
        },
        Term::Pi(x, icit, dom, cod) => {
            let (dom, s1) = check_type(cx, dom)?;
            let dom_value = cx.eval(&dom)?;
            cx.bind(x.clone(), dom_value);
            let result = check_type(cx, cod);
            cx.unbind(1);
            let (cod, s2) = result?;
            Ok((
                Term::Pi(x.clone(), *icit, Rc::new(dom), Rc::new(cod)),
                Value::Sort(Sort::pi(s1, s2)),
            ))
        }
        Term::App(f, a, icit) => {
            let (f, f_ty) = infer(cx, f)?;
            match f_ty {
                Value::Pi(_, pi_icit, dom, cod) if pi_icit == *icit => {
                    let a = check(cx, a, &dom)?;
                    // As `Closure::apply_lazy`: `a` is computed only if the
                    // result type depends on it.
                    let arg = if cod.body.mentions(0) {
                        cx.eval(&a)?
                    } else {
                        unused()
                    };
                    let ty = cod.apply(g, arg)?;
                    Ok((Term::app_icit(f, a, *icit), ty))
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
        Term::Ann(e, ty) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let e = check(cx, e, &ty_value)?;
            Ok((Term::Ann(Rc::new(e), Rc::new(ty)), ty_value))
        }
        // The body's type is a value computed with `x` evaluating to `v`, so
        // it doesn't mention `x`: it's `B[v/x]` already, usable outside.
        Term::Let(x, ty, value, body, _) => {
            let (x, ty, value, erased) = check_let_value(cx, x, ty, value)?;
            let result = infer(cx, body);
            cx.unbind(1);
            let (body, body_ty) = result?;
            let skip = erased || !body.mentions(0);
            Ok((Term::Let(x, ty, value, Rc::new(body), skip), body_ty))
        }
        Term::Eq(Some(ty), a, b) => {
            let (ty, _) = check_type(cx, ty)?;
            let ty_value = cx.eval(&ty)?;
            let a = check(cx, a, &ty_value)?;
            let b = check(cx, b, &ty_value)?;
            Ok((
                Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::Prop),
            ))
        }
        Term::Eq(None, a, b) => {
            let (a, b, ty) = match infer(cx, a) {
                Ok((a, ty)) => (a, check(cx, b, &ty)?, ty),
                Err(e) if e.code == "E-CANNOT-INFER" => {
                    let (b, ty) = infer(cx, b)?;
                    (check(cx, a, &ty)?, b, ty)
                }
                Err(e) => return Err(e),
            };
            let ty = cx.quote(&ty)?;
            Ok((
                Term::Eq(Some(Rc::new(ty)), Rc::new(a), Rc::new(b)),
                Value::Sort(Sort::Prop),
            ))
        }
        Term::J(motive, base, proof) => infer_j(cx, motive, base, proof),
        // A constructor of a data type without parameters has only one possible type.
        Term::Ctor(d, _, _) if g.datas.get(d.0).is_some_and(|d| d.params.is_empty()) => {
            let ty = Value::Data(*d, Vec::new());
            Ok((check(cx, term, &ty)?, ty))
        }
        Term::Meta(_) => Err(malformed(cx, "unsolved metavariable")),
        Term::Lam(..) | Term::Ctor(..) | Term::Refl | Term::Case(..) | Term::NumCase(..) => Err(cx
            .error(
                "E-CANNOT-INFER",
                "can't work out the type of this",
                "add a type annotation: `(… : T)`",
            )),
    }
}

pub fn check(cx: &mut Ctx, term: &Term, expected: &Value) -> Result<Term> {
    let g = cx.g;
    g.budget.nesting(PASS)?;
    match (term, expected) {
        (Term::Loc(span, inner), _) => {
            let saved = std::mem::replace(&mut cx.span, *span);
            let result = check(cx, inner, expected);
            cx.span = saved;
            Ok(Term::Loc(*span, Rc::new(result?)))
        }
        (Term::Lam(x, icit, body), Value::Pi(_, pi_icit, dom, cod)) if icit == pi_icit => {
            let var = Value::var(cx.level());
            cx.bind(x.clone(), (**dom).clone());
            let result = check(cx, body, &cod.apply(g, var)?);
            cx.unbind(1);
            Ok(Term::Lam(x.clone(), *icit, Rc::new(result?)))
        }
        (Term::Lam(..), _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "this is a function, but the expected type is `{}`",
                cx.show(expected)
            ),
        )),
        (Term::Ctor(d, c, _), _) if g.datas.get(d.0).and_then(|d| d.ctors.get(*c)).is_none() => {
            Err(malformed(cx, "reference to an unknown constructor"))
        }
        (Term::Ctor(d, c, args), Value::Data(d2, params)) if d == d2 => {
            let ctor = &g.data(*d).ctors[*c];
            if args.len() != ctor.fields.len() {
                return Err(malformed(
                    cx,
                    format!("`{}` needs {} field(s)", ctor.name, ctor.fields.len()),
                ));
            }
            let mut env = params.clone();
            let mut out = Vec::new();
            for (i, ((_, field_ty), arg)) in ctor.fields.iter().zip(args).enumerate() {
                let ty = eval(g, &env, field_ty)?;
                let arg = check(cx, arg, &ty)?;
                env.push(if later_types_mention(&ctor.fields, i) {
                    cx.eval(&arg)?
                } else {
                    unused()
                });
                out.push(arg);
            }
            Ok(Term::ctor(*d, *c, out))
        }
        (Term::Ctor(d, c, _), _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`{}` builds a `{}`, but the expected type is `{}`",
                g.data(*d).ctors[*c].name,
                g.data(*d).name,
                cx.show(expected)
            ),
        )),
        (Term::Refl, Value::Eq(_, a, b)) => {
            if cx.conv(a, b)? {
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
        (Term::Refl, _) => Err(cx.error(
            "E-TYPE-MISMATCH",
            "type mismatch",
            format!(
                "`rfl` proves an equation, but the expected type is `{}`",
                cx.show(expected)
            ),
        )),
        (Term::Let(x, ty, value, body, _), _) => {
            let (x, ty, value, erased) = check_let_value(cx, x, ty, value)?;
            let result = check(cx, body, expected);
            cx.unbind(1);
            let body = result?;
            let skip = erased || !body.mentions(0);
            Ok(Term::Let(x, ty, value, Rc::new(body), skip))
        }
        (Term::Case(ix, d, branches), _) => check_case(cx, *ix, *d, branches, expected),
        (Term::NumCase(ix, arms, default), _) => check_num_case(cx, *ix, arms, default, expected),
        _ => {
            let (term, found) = infer(cx, term)?;
            if cx.conv(&found, expected)? {
                Ok(term)
            } else {
                Err(cx.mismatch(expected, &found))
            }
        }
    }
}

pub fn check_type(cx: &mut Ctx, term: &Term) -> Result<(Term, Sort)> {
    let (term, ty) = infer(cx, term)?;
    match ty {
        Value::Sort(s) => Ok((term, s)),
        other => Err(cx.error(
            "E-NOT-A-TYPE",
            "expected a type",
            format!("this has type `{}`, so it isn't a type", cx.show(&other)),
        )),
    }
}

/// The premises of `Let(x, A, v, b)` before its body: `A` is a type (in
/// any universe: a proof, data and a type are all defined the same way), and
/// `v : A`. Leaves `x := v` defined in the context, for the body; the caller
/// removes it. Also whether `x` is erased when running: exactly when a
/// parameter of type `A` would be (a proposition, or a type former;
/// docs/proposals/let.md §6.1 rule 5), whatever the term said.
fn check_let_value(
    cx: &mut Ctx,
    x: &Name,
    ty: &Term,
    value: &Term,
) -> Result<(Name, Rc<Term>, Rc<Term>, bool)> {
    let (ty, sort) = check_type(cx, ty)?;
    let ty_value = cx.eval(&ty)?;
    let erased = sort == Sort::Prop || is_type_former(cx.g, cx.level(), &ty_value)?;
    let value = Rc::new(check(cx, value, &ty_value)?);
    // Computed only when checking the body needs it (`Ctx::define`).
    cx.define(x.clone(), ty_value, value.clone());
    Ok((x.clone(), Rc::new(ty), value, erased))
}

/// The universe that `ty` lives in.
fn sort_of(cx: &mut Ctx, ty: &Value) -> Result<Sort> {
    if let Value::Sort(s) = ty {
        return Ok(s.succ());
    }
    let term = cx.quote(ty)?;
    Ok(check_type(cx, &term)?.1)
}

fn infer_j(cx: &mut Ctx, motive: &Term, base: &Term, proof: &Term) -> Result<(Term, Value)> {
    let g = cx.g;
    let (proof, proof_ty) = infer(cx, proof)?;
    let Value::Eq(ty, x, y) = proof_ty else {
        return Err(cx.error(
            "E-TYPE-MISMATCH",
            "`J` needs a proof of an equation",
            format!("its last argument has type `{}`", cx.show(&proof_ty)),
        ));
    };
    let Term::Lam(y_name, Icit::Explicit, inner) = motive.strip_loc() else {
        return Err(motive_error(cx));
    };
    let Term::Lam(p_name, Icit::Explicit, body) = inner.strip_loc() else {
        return Err(motive_error(cx));
    };
    let level = cx.level();
    cx.bind(y_name.clone(), (*ty).clone());
    cx.bind(
        p_name.clone(),
        Value::Eq(ty.clone(), x.clone(), Rc::new(Value::var(level))),
    );
    let result = check_type(cx, body);
    cx.unbind(2);
    let (body, _) = result?;
    let motive = Term::Lam(
        y_name.clone(),
        Icit::Explicit,
        Rc::new(Term::Lam(p_name.clone(), Icit::Explicit, Rc::new(body))),
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

fn check_case(
    cx: &mut Ctx,
    ix: usize,
    d: DataId,
    branches: &[Branch],
    goal: &Value,
) -> Result<Term> {
    let g = cx.g;
    g.budget.nesting(PASS)?;
    if ix >= cx.level() {
        return Err(malformed(cx, format!("variable {ix} is out of scope")));
    }
    // Refinement rewrites the whole environment. (A case is never under a
    // `let`, so nothing's pending here; this keeps it so.)
    cx.force_all()?;
    let x = cx.level() - 1 - ix;
    let Some(data) = g.datas.get(d.0) else {
        return Err(malformed(cx, "reference to an unknown data type"));
    };
    // A data type whose constructors aren't in yet isn't empty.
    if data.state != State::Final {
        return Err(malformed(
            cx,
            format!("a match on `{}`, which isn't finished", data.name),
        ));
    }
    let params = match &cx.types[x] {
        Value::Data(d2, params) if *d2 == d => params.clone(),
        other => {
            return Err(cx.error(
                "E-TYPE-MISMATCH",
                "type mismatch",
                format!(
                    "this matches on a `{}`, but `{}` has type `{}`",
                    data.name,
                    cx.names[x],
                    cx.show(other)
                ),
            ));
        }
    };
    if branches.len() != data.ctors.len() {
        return Err(cx.error(
            "E-NONEXHAUSTIVE",
            "missing cases",
            format!("`{}` has {} constructors", data.name, data.ctors.len()),
        ));
    }
    if data.sort == Sort::Prop && sort_of(cx, goal)? != Sort::Prop {
        // Like Lean, propositions defined together never eliminate into
        // data: a deliberately conservative rule
        // (docs/proposals/mutual-recursion.md §7.3).
        let subsingleton = data.group.len() == 1
            && data.ctors.len() <= 1
            && data
                .ctors
                .iter()
                .all(|c| c.field_sorts.iter().all(|s| *s == Sort::Prop));
        if !subsingleton {
            let note = if data.group.len() > 1 {
                format!(
                    "`{}` is a proposition, so its proofs are erased at runtime. It's defined \
                     together with other types, and matching on a proof of one of those can only \
                     produce another proof.",
                    data.name
                )
            } else {
                format!(
                    "`{}` is a proposition, so its proofs are erased at runtime. Matching on one \
                     can only produce data when the proposition has at most one constructor and \
                     every field is itself a proof.",
                    data.name
                )
            };
            return Err(cx
                .error(
                    "E-PROP-ELIM",
                    format!("can't match on a proof of `{}` to produce data", data.name),
                    format!("the result type `{}` isn't a proposition", cx.show(goal)),
                )
                .with_note(note));
        }
    }

    if let Some((ctor, branch)) = data
        .ctors
        .iter()
        .zip(branches)
        .find(|(ctor, branch)| ctor.fields.len() != branch.names.len())
    {
        return Err(malformed(
            cx,
            format!(
                "the `{}` branch binds {} field(s), but it has {}",
                ctor.name,
                branch.names.len(),
                ctor.fields.len()
            ),
        ));
    }

    let goal_term = cx.quote(goal)?;
    let mut out = Vec::new();
    for (c, (ctor, branch)) in data.ctors.iter().zip(branches).enumerate() {
        let base = cx.level();
        let fields: Vec<Value> = (0..ctor.fields.len())
            .map(|i| Value::var(base + i))
            .collect();
        // Inside the branch, the matched variable *is* the constructor value,
        // so it's substituted into the goal and the whole context.
        let value = Value::Ctor(d, c, fields.clone().into());
        let level = cx.level();
        let mut env = substitute(g, level, x, &value, &cx.env)?;
        env[x] = value.clone();
        let refined_types = substitute(g, level, x, &value, &cx.types)?;
        let branch_goal = substitute(g, level, x, &value, &[eval(g, &cx.env, &goal_term)?])?
            .pop()
            .expect("one value in, one out");
        let saved_env = std::mem::replace(&mut cx.env, env);
        let saved_types = std::mem::replace(&mut cx.types, refined_types);

        let mut field_env = params.clone();
        for ((_, field_ty), (name, field)) in
            ctor.fields.iter().zip(branch.names.iter().zip(&fields))
        {
            let ty = eval(g, &field_env, field_ty)?;
            field_env.push(field.clone());
            cx.bind(name.clone(), ty);
        }
        let result = check(cx, &branch.body, &branch_goal);
        cx.unbind(ctor.fields.len());
        cx.env = saved_env;
        cx.types = saved_types;
        out.push(Branch {
            names: branch.names.clone(),
            body: Rc::new(result?),
        });
    }
    Ok(Term::Case(ix, d, out.into()))
}

/// `NumCase(x, arms, default) ⇐ G`: `x` must be a variable of type `Nat`,
/// and the arms' numbers strictly increasing (and at least one). Each arm is
/// checked with its number substituted for `x` throughout the context and the
/// goal, as a `case` branch substitutes its constructor value. The default is
/// checked with nothing new known. That makes it a weakened form of the nested
/// `Zero`/`Succ` cases it stands for (docs/proposals/number-patterns.md).
fn check_num_case(
    cx: &mut Ctx,
    ix: usize,
    arms: &[NumArm],
    default: &Term,
    goal: &Value,
) -> Result<Term> {
    let g = cx.g;
    g.budget.nesting(PASS)?;
    if ix >= cx.level() {
        return Err(malformed(cx, format!("variable {ix} is out of scope")));
    }
    // Refinement rewrites the whole environment. (A case is never under a
    // `let`, so nothing's pending here; this keeps it so.)
    cx.force_all()?;
    let x = cx.level() - 1 - ix;
    let Some(nat) = g.builtins.nat else {
        return Err(malformed(cx, "a number case without `Nat`"));
    };
    // Registering `Nat` requires it to be finished, but as for `case`, the
    // type matched on must be.
    if g.data(nat).state != State::Final {
        return Err(malformed(
            cx,
            "a number case on `Nat`, which isn't finished",
        ));
    }
    // The elaborator only compiles a column of a `Nat` to a number case, so
    // anything else is a compiler bug.
    match &cx.types[x] {
        Value::Data(d, params) if *d == nat && params.is_empty() => {}
        other => {
            return Err(malformed(
                cx,
                format!(
                    "a number case on `{}`, which has type `{}`",
                    cx.names[x],
                    cx.show(other)
                ),
            ));
        }
    }
    if arms.is_empty() {
        return Err(malformed(cx, "a number case with no numbers"));
    }
    if arms.windows(2).any(|w| w[0].value >= w[1].value) {
        return Err(malformed(
            cx,
            "a number case's numbers aren't in strictly increasing order",
        ));
    }
    let goal_term = cx.quote(goal)?;
    let mut out = Vec::new();
    for arm in arms {
        let value = Value::Nat(arm.value.clone());
        let level = cx.level();
        let mut env = substitute(g, level, x, &value, &cx.env)?;
        env[x] = value.clone();
        let refined_types = substitute(g, level, x, &value, &cx.types)?;
        let arm_goal = substitute(g, level, x, &value, &[eval(g, &cx.env, &goal_term)?])?
            .pop()
            .expect("one value in, one out");
        let saved_env = std::mem::replace(&mut cx.env, env);
        let saved_types = std::mem::replace(&mut cx.types, refined_types);
        let result = check(cx, &arm.body, &arm_goal);
        cx.env = saved_env;
        cx.types = saved_types;
        out.push(NumArm {
            value: arm.value.clone(),
            body: Rc::new(result?),
        });
    }
    let default = check(cx, default, goal)?;
    Ok(Term::NumCase(ix, out.into(), Rc::new(default)))
}

/// Substitutes `value` for variable `x` in each of `values`, with `level`
/// variables in scope. Case branches use this to refine the whole context:
/// with nested patterns, a variable matched later can appear in the type of
/// one bound earlier (`rest : res o` after `o` is matched as `L o'`).
pub fn substitute(
    g: &Globals,
    level: usize,
    x: usize,
    value: &Value,
    values: &[Value],
) -> budget::Result<Vec<Value>> {
    let mut env: Vec<Value> = (0..level).map(Value::var).collect();
    env[x] = value.clone();
    values
        .iter()
        .map(|v| eval(g, &env, &quote(g, level, v)?))
        .collect()
}

/// Whether the types of the binders after binder `i` in a telescope (data
/// parameters, or constructor fields) mention it. If not, checking doesn't
/// need its value. In binder `j`'s type, binder `i` is variable `j - 1 - i`.
pub fn later_types_mention(binders: &[(Name, Term)], i: usize) -> bool {
    binders
        .iter()
        .enumerate()
        .skip(i + 1)
        .any(|(j, (_, ty))| ty.mentions(j - 1 - i))
}

/// Infers the type of a closed term.
pub fn infer_closed(g: &Globals, term: &Term, span: Span) -> Result<(Term, Value)> {
    infer(&mut Ctx::new(g, span), term)
}

// Declarations

/// Checks the body of a definition added by [`declare_def`], which makes it
/// final, or failed if it's refused: a group of one ([`define_group`]).
/// Until then the definition has no body, so it never unfolds: recursive
/// references inside its own body stay opaque while it's being checked.
pub fn define_def(g: &mut Globals, id: DefId, body: &Term) -> Result<()> {
    define_group(g, &[(id, body.clone())])
}

/// Checks the bodies of a group of definitions, each added by
/// [`declare_def`], which may call each other
/// (docs/proposals/mutual-recursion.md §5.3). Either every member becomes
/// final, or (on any error, including running out of resources) every one
/// becomes failed and no body is installed.
///
/// - Every member must be pending, and listed once.
/// - Every member's entry arity is fixed (from its submitted body) before
///   any body is checked.
/// - A body may refer to final declarations and to members of this group,
///   and to nothing else that's pending; a signature (checked by
///   `declare_def`) only to final declarations.
/// - Every body is checked with every member opaque: none has a body until
///   all are accepted, so checking can't unfold an unchecked definition.
/// - Termination is decided for the whole group at once, from every call
///   between any two members.
pub fn define_group(g: &mut Globals, members: &[(DefId, Term)]) -> Result<()> {
    // Refused before anything changes: an empty group, or an id that isn't
    // a definition at all.
    if members.is_empty() {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: an empty group of definitions",
        ));
    }
    if members.iter().any(|(id, _)| id.0 >= g.defs.len()) {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown definition",
        ));
    }
    let ids: Rc<[DefId]> = members.iter().map(|(id, _)| *id).collect();
    // From here on, a refusal leaves every member that was pending failed.
    let fail = |g: &mut Globals, e: Diagnostic| {
        for id in ids.iter() {
            let def = &mut g.defs[id.0];
            if def.state == State::Pending {
                def.state = State::Failed;
            }
        }
        Err(e)
    };
    for (k, (id, _)) in members.iter().enumerate() {
        let def = g.def(*id);
        let problem = if ids[..k].contains(id) {
            Some("is listed twice in one group")
        } else if def.state != State::Pending {
            Some("has already been defined")
        } else {
            None
        };
        if let Some(problem) = problem {
            let e = malformed(&Ctx::new(g, def.span), format!("`{}` {problem}", def.name));
            return fail(g, e);
        }
    }
    // The definition-entry arities and the group, fixed before anything is
    // checked: every consumer (the termination checker's saturation rule,
    // graph dimensions and parameters, the evaluator's unfolding,
    // extraction) reads these.
    for (id, body) in members {
        let def = &mut g.defs[id.0];
        def.arity = body.count_lams();
        def.group = Some(ids.clone());
    }
    match admit_group(g, members) {
        Ok(bodies) => {
            for ((id, _), body) in members.iter().zip(bodies) {
                let def = &mut g.defs[id.0];
                def.body = Some(Rc::new(body));
                def.state = State::Final;
            }
            Ok(())
        }
        Err(e) => fail(g, e),
    }
}

/// Everything [`define_group`] checks once the members are known to be
/// pending: the checked bodies, in order.
fn admit_group(g: &Globals, members: &[(DefId, Term)]) -> Result<Vec<Term>> {
    let ids: Vec<DefId> = members.iter().map(|(id, _)| *id).collect();
    // Every reference in every member is checked first, so a malformed one
    // is refused before any body is type-checked.
    let mut failed = None;
    for (id, body) in members {
        let def = g.def(*id);
        let cx = Ctx::new(g, def.span);
        failed = failed.or(admissible(&cx, [&def.ty], None)?);
        failed = failed.or(admissible(&cx, [body], Some(Itself::Group(&ids)))?);
        if !case_only_in_tree(body.peel_lams(def.arity), true) {
            return Err(malformed(
                &cx,
                "`case` may only appear at the top of a definition",
            ));
        }
    }
    let mut checked = Vec::new();
    for (id, body) in members {
        let def = g.def(*id);
        let mut cx = Ctx::new(g, def.span);
        // Checking keeps every location and lambda, so the checked body has
        // the same parameters; the termination checker refuses it if not.
        checked.push(check(&mut cx, body, &def.ty_value)?);
    }
    let group: Vec<termination::Member> = ids
        .iter()
        .zip(&checked)
        .map(|(id, body)| termination::Member { id: *id, body })
        .collect();
    termination::check_group(g, &group, crate::sct::MAX_GRAPHS)?;
    match failed {
        Some(dep) => {
            let first = g.def(ids[0]);
            Err(failed_dependency(
                &Ctx::new(g, first.span),
                &first.name,
                &dep,
            ))
        }
        None => Ok(checked),
    }
}

/// Checks a definition's type and adds it without a body.
pub fn declare_def(
    g: &mut Globals,
    name: &Name,
    ty: &Term,
    theorem: bool,
    export: bool,
    span: Span,
) -> Result<DefId> {
    let mut cx = Ctx::new(g, span);
    if !case_only_in_tree(ty, false) {
        return Err(malformed(
            &cx,
            "`case` may only appear at the top of a definition",
        ));
    }
    // A failed reference is let through: `define_def` finds it again.
    admissible(&cx, [ty], None)?;
    let (ty, sort) = check_type(&mut cx, ty)?;
    if theorem && sort != Sort::Prop {
        let ty_value = cx.eval(&ty)?;
        return Err(Diagnostic::error(
            "E-NOT-A-PROP",
            format!("`{name}` is declared as a theorem, but its type isn't a proposition"),
        )
        .with_label(
            span,
            format!(
                "`{}` is a type of data, not a proposition",
                cx.show(&ty_value)
            ),
        )
        .with_note("remove `theorem` to make it an ordinary definition"));
    }
    let ty_value = eval(g, &[], &ty)?;
    g.defs.push(Def {
        name: name.clone(),
        path: g.path(name),
        ty,
        ty_value,
        body: None,
        state: State::Pending,
        arity: 0,
        group: None,
        theorem,
        export,
        validators: Vec::new(),
        span,
    });
    Ok(DefId(g.defs.len() - 1))
}

/// Checks a data type's parameters and adds it with no constructors yet, so
/// its constructors can refer to it: a data group of one
/// ([`declare_data_group`]).
pub fn declare_data(
    g: &mut Globals,
    name: Name,
    params: Vec<(Name, Term)>,
    sort: Sort,
    span: Span,
) -> Result<DataId> {
    let ids = declare_data_group(g, params, sort, vec![(name, span)])?;
    Ok(ids[0])
}

/// Declares a group of data types whose constructors may mention each other
/// (docs/proposals/mutual-recursion.md §5.4, §7): one shared parameter
/// telescope, checked once, in one context, and one universe. The members
/// are added in order, with no constructors yet, each recording the group
/// (the immutable metadata of §7.3). The parameters may refer only to final
/// declarations: a reference to a declaration that doesn't exist yet,
/// including one a member is about to become, is refused before anything is
/// added.
pub fn declare_data_group(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span)>,
) -> Result<Vec<DataId>> {
    let members = members
        .into_iter()
        .map(|(name, span)| (name, span, false))
        .collect();
    declare_data_group_as(g, params, sort, members)
}

/// [`declare_data_group`], saying for each member whether it's a record
/// (docs/proposals/records.md): a type with exactly one constructor, which
/// `define_data_group` checks, and which extracted JS represents without a
/// tag. The flag is fixed here and hashed; nothing in checking depends on it.
pub fn declare_data_group_as(
    g: &mut Globals,
    params: Vec<(Name, Term)>,
    sort: Sort,
    members: Vec<(Name, Span, bool)>,
) -> Result<Vec<DataId>> {
    let Some(&(_, span, _)) = members.first() else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: an empty group of data types",
        ));
    };
    let mut cx = Ctx::new(g, span);
    // A failed reference is let through: `define_data_group` finds it again.
    admissible(&cx, params.iter().map(|(_, ty)| ty), None)?;
    let mut checked = Vec::new();
    for (x, ty) in params {
        let (ty, _) = check_type(&mut cx, &ty)?;
        let value = cx.eval(&ty)?;
        cx.bind(x.clone(), value);
        checked.push((x, ty));
    }
    let (defs_before, datas_before) = (g.defs.len(), g.datas.len());
    let group: Rc<[DataId]> = (0..members.len())
        .map(|i| DataId(datas_before + i))
        .collect();
    for (name, span, record) in members {
        let path = g.path(&name);
        g.datas.push(Data {
            name,
            path,
            params: checked.clone(),
            sort,
            ctors: Vec::new(),
            record,
            validators: Vec::new(),
            group: group.clone(),
            defs_before,
            datas_before,
            state: State::Pending,
            span,
        });
    }
    Ok(group.to_vec())
}

pub struct CtorDecl {
    pub name: Name,
    pub fields: Vec<(Name, Term, Span)>,
}

/// Checks and adds the constructors of a data type added by
/// [`declare_data`], which makes it final, or failed if they're refused: a
/// data group of one ([`define_data_group`]).
pub fn define_ctors(g: &mut Globals, d: DataId, ctors: Vec<CtorDecl>) -> Result<()> {
    define_data_group(g, vec![(d, ctors)])
}

/// Checks and adds the constructors of every member of a data group added
/// by [`declare_data_group`]. Either every member becomes final, or (on any
/// error) every one becomes failed and none has constructors.
///
/// - Every member of the group must be listed, once, and be pending; nothing
///   else may be.
/// - A field may refer to final declarations and to the group's members *as
///   types*: not to their constructors, and no `case` on one (none has
///   constructors until all are accepted).
/// - Strict positivity is checked for every member in every field of every
///   member's constructors: a member can't occur to the left of an arrow,
///   even in a sibling's constructor.
pub fn define_data_group(g: &mut Globals, members: Vec<(DataId, Vec<CtorDecl>)>) -> Result<()> {
    // Refused before anything changes: an empty group, or an id that isn't
    // a data type at all.
    if members.is_empty() {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: an empty group of data types",
        ));
    }
    if members.iter().any(|(d, _)| d.0 >= g.datas.len()) {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown data type",
        ));
    }
    let listed: Vec<DataId> = members.iter().map(|(d, _)| *d).collect();
    // From here on, a refusal leaves failed every pending member of every
    // group a listed type belongs to.
    let fail = |g: &mut Globals, e: Diagnostic| {
        let groups: Vec<Rc<[DataId]>> = listed.iter().map(|d| g.data(*d).group.clone()).collect();
        for d in groups.iter().flat_map(|group| group.iter()) {
            let data = &mut g.datas[d.0];
            if data.state == State::Pending {
                data.state = State::Failed;
            }
        }
        Err(e)
    };
    let group = g.data(listed[0]).group.clone();
    for (k, d) in listed.iter().enumerate() {
        let data = g.data(*d);
        let problem = if listed[..k].contains(d) {
            Some(format!("`{}` is listed twice in one group", data.name))
        } else if data.state != State::Pending {
            Some(format!(
                "`{}`'s constructors are already defined",
                data.name
            ))
        } else if !group.contains(d) {
            Some(format!(
                "`{}` wasn't declared in the same group as `{}`",
                data.name,
                g.data(listed[0]).name
            ))
        } else if data.record && members[k].1.len() != 1 {
            Some(format!(
                "`{}` is a record, so it has exactly one constructor",
                data.name
            ))
        } else {
            None
        };
        if let Some(problem) = problem {
            let e = malformed(&Ctx::new(g, data.span), problem);
            return fail(g, e);
        }
    }
    if let Some(missing) = group.iter().find(|d| !listed.contains(d)) {
        let data = g.data(*missing);
        let e = malformed(
            &Ctx::new(g, data.span),
            format!(
                "`{}` was declared in this group, but its constructors aren't given",
                data.name
            ),
        );
        return fail(g, e);
    }
    match admit_data_group(g, &group, members) {
        Ok(ctors) => {
            // Every member at once: until now none had constructors, could
            // be matched on, or had a hash.
            for (d, ctors) in ctors {
                g.datas[d.0].ctors = ctors;
                g.datas[d.0].state = State::Final;
            }
            Ok(())
        }
        Err(e) => fail(g, e),
    }
}

/// Everything [`define_data_group`] checks once the members are known to be
/// the group's, and pending: each member's checked constructors.
fn admit_data_group(
    g: &Globals,
    group: &[DataId],
    members: Vec<(DataId, Vec<CtorDecl>)>,
) -> Result<Vec<(DataId, Vec<Ctor>)>> {
    // The members' parameters are one telescope, shared by construction.
    let first = g.data(group[0]);
    let mut cx = Ctx::new(g, first.span);
    let mut failed = admissible(&cx, first.params.iter().map(|(_, ty)| ty), None)?;
    for (x, ty) in &first.params {
        let value = cx.eval(ty)?;
        cx.bind(x.clone(), value);
    }
    let mut out = Vec::new();
    for (d, ctors) in members {
        let data = g.data(d);
        let mut checked = Vec::new();
        for ctor in ctors {
            let mut fields = Vec::new();
            let mut field_sorts = Vec::new();
            let mut field_erased = Vec::new();
            for (x, ty, span) in ctor.fields {
                cx.span = span;
                if !case_only_in_tree(&ty, false) {
                    return Err(malformed(
                        &cx,
                        "`case` may only appear at the top of a definition",
                    ));
                }
                // The group's types may appear in a field, but not their
                // constructors.
                let field_failed = admissible(&cx, [&ty], Some(Itself::DataGroup(group)))?;
                failed = failed.or(field_failed);
                if let Some(later) = declared_later(g, &ty, d) {
                    return Err(cx
                        .error(
                            "E-POSITIVITY",
                            format!(
                                "field `{x}` uses {later}, which was declared after `{}`",
                                data.name
                            ),
                            "declared later",
                        )
                        .with_note(
                            "something declared after a data type could mention it, hiding a \
                             negative occurrence from the positivity check",
                        ));
                }
                let (ty, sort) = check_type(&mut cx, &ty)?;
                if !sort.fits_in(data.sort) {
                    return Err(cx.error(
                        "E-UNIVERSE",
                        format!("field `{x}` is too large for `{}`", data.name),
                        format!(
                            "its type is in `{}`, but `{}` is in `{}`",
                            pretty::term(g, &[], &Term::Sort(sort)),
                            data.name,
                            pretty::term(g, &[], &Term::Sort(data.sort))
                        ),
                    ));
                }
                if let Some((found, how)) = not_positive(&ty, group, cx.level()) {
                    return Err(not_positive_error(&cx, &x, found, how, group));
                }
                let value = cx.eval(&ty)?;
                field_erased.push(sort == Sort::Prop || is_type_former(g, cx.level(), &value)?);
                cx.bind(x.clone(), value);
                fields.push((x, ty));
                field_sorts.push(sort);
            }
            cx.unbind(fields.len());
            checked.push(Ctor {
                name: ctor.name,
                fields,
                field_sorts,
                field_erased,
            });
        }
        out.push((d, checked));
    }
    match failed {
        Some(dep) => Err(failed_dependency(&cx, &first.name, &dep)),
        None => Ok(out),
    }
}

/// Marks every pending declaration failed. For an elaborator that gives up
/// on a declaration before submitting its body or constructors: failing is
/// always safe, and it stops later declarations tripping over a pending one.
pub fn abandon_pending(g: &mut Globals) {
    for def in &mut g.defs {
        if def.state == State::Pending {
            def.state = State::Failed;
        }
    }
    for data in &mut g.datas {
        if data.state == State::Pending {
            data.state = State::Failed;
        }
    }
}

/// The declarations being admitted, which may refer to each other.
#[derive(Clone, Copy, PartialEq)]
enum Itself<'a> {
    /// The definitions of a function group, in their bodies.
    Group(&'a [DefId]),
    /// The data types of a data group, as types (not their constructors or
    /// a `case`) in their fields.
    DataGroup(&'a [DataId]),
}

/// The admission rule (docs/proposals/kernel-admission.md): everything
/// `terms` refer to must be final, apart from `itself`. A pending reference
/// is refused at once. A failed one is returned, so that the caller can
/// still check the rest (and report its own errors) before failing.
///
/// Every final declaration was admitted under this rule, so everything it
/// reaches is final too: there's no need to follow references.
fn admissible<'t>(
    cx: &Ctx,
    terms: impl IntoIterator<Item = &'t Term>,
    itself: Option<Itself>,
) -> Result<Option<Name>> {
    let g = cx.g;
    let in_group =
        |id: &DefId| matches!(itself, Some(Itself::Group(members)) if members.contains(id));
    let in_data_group =
        |d: &DataId| matches!(itself, Some(Itself::DataGroup(members)) if members.contains(d));
    let mut failed = None;
    for term in terms {
        for (t, _) in term.subterms() {
            let (state, name) = match t {
                Term::Def(id) if !in_group(id) => match g.defs.get(id.0) {
                    Some(def) => (def.state, &def.name),
                    None => return Err(malformed(cx, "reference to an unknown definition")),
                },
                Term::Data(d, _) if in_data_group(d) => continue,
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _) => {
                    match g.datas.get(d.0) {
                        Some(data) => (data.state, &data.name),
                        None => return Err(malformed(cx, "reference to an unknown data type")),
                    }
                }
                // A number case uses `Nat`. Its arms and default are walked
                // like any other subterms.
                Term::NumCase(..) => match g.builtins.nat.and_then(|d| g.datas.get(d.0)) {
                    Some(data) => (data.state, &data.name),
                    None => return Err(malformed(cx, "a number case without `Nat`")),
                },
                // A compact list uses `List` and `Char`, as its expansion
                // would. (Registering them requires both to be final, so
                // this always passes; it's checked as any reference is.)
                Term::Chars(_) => match &g.builtins.text {
                    Some(text) => {
                        let (list, char) = (g.data(text.list), g.data(text.char));
                        if list.state != State::Final {
                            (list.state, &list.name)
                        } else {
                            (char.state, &char.name)
                        }
                    }
                    None => {
                        return Err(malformed(
                            cx,
                            "a compact list of characters, but `List` and `Char` aren't \
                             registered for it",
                        ));
                    }
                },
                _ => continue,
            };
            match state {
                State::Final => {}
                State::Pending => {
                    let message = match itself {
                        Some(Itself::Group(members)) if members.len() > 1 => format!(
                            "this refers to `{name}`, which isn't finished and isn't in this group"
                        ),
                        // A constructor of, or a match on, one of the
                        // group's own types.
                        Some(Itself::DataGroup(_))
                            if matches!(t, Term::Ctor(..) | Term::Case(..)) =>
                        {
                            format!(
                                "this uses `{name}`'s constructors, which aren't finished: a \
                                 field may use the group's types, but not their constructors"
                            )
                        }
                        _ => format!("this refers to `{name}`, which isn't finished"),
                    };
                    return Err(malformed(cx, message));
                }
                State::Failed => {
                    failed.get_or_insert_with(|| name.clone());
                }
            }
        }
    }
    Ok(failed)
}

/// `what` checked, but uses `dep`, which failed, so it fails too.
fn failed_dependency(cx: &Ctx, what: &Name, dep: &Name) -> Diagnostic {
    cx.error(
        "E-FAILED-DEPENDENCY",
        format!("`{what}` uses `{dep}`, which has errors"),
        format!("`{dep}` has errors"),
    )
    .with_note(format!(
        "`{what}` can't be accepted until the errors in `{dep}` are fixed"
    ))
}

/// A definition or data type in `term` declared after data type `d`'s group
/// (and not in it), if any: the first one, reading left to right.
fn declared_later(g: &Globals, term: &Term, d: DataId) -> Option<String> {
    let data = g.data(d);
    let later_data = |d2: DataId| {
        (d2.0 >= data.datas_before && !data.group.contains(&d2)).then(|| {
            let name = g.datas.get(d2.0).map_or("?".into(), |x| x.name.to_string());
            format!("the data type `{name}`")
        })
    };
    term.subterms().find_map(|(t, _)| match t {
        Term::Def(id) => (id.0 >= data.defs_before).then(|| {
            let name = g.defs.get(id.0).map_or("?".into(), |x| x.name.to_string());
            format!("`{name}`")
        }),
        Term::Data(d2, _) | Term::Ctor(d2, _, _) | Term::Case(_, d2, _) => later_data(*d2),
        // A compact list refers to `List` and `Char`, as its expansion would.
        Term::Chars(_) => g
            .builtins
            .text
            .as_ref()
            .and_then(|text| later_data(text.list).or_else(|| later_data(text.char))),
        _ => None,
    })
}

/// "`a`, `b` and `c`".
fn listed(names: &[String]) -> String {
    match names.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => names.join(""),
    }
}

/// An error for a term no correct elaborator would produce.
fn malformed(cx: &Ctx, message: impl Into<String>) -> Diagnostic {
    cx.error("E-MALFORMED", "malformed core term", message)
        .with_note("this is a bug in the compiler, not in your program")
}

/// Whether `case` appears only in case-tree positions: at the top of a
/// definition's body (`in_tree`), and at the top of each branch. Evaluation
/// relies on this.
/// It runs before the term is type-checked, so it uses a work list rather
/// than recursion: the term may nest more deeply than recursion could follow.
fn case_only_in_tree(term: &Term, in_tree: bool) -> bool {
    let mut pending = vec![(term, in_tree)];
    while let Some((term, in_tree)) = pending.pop() {
        match term {
            Term::Case(_, _, branches) => {
                if !in_tree {
                    return false;
                }
                pending.extend(branches.iter().map(|b| (&*b.body, true)));
            }
            Term::NumCase(_, arms, default) => {
                if !in_tree {
                    return false;
                }
                pending.extend(arms.iter().map(|a| (&*a.body, true)));
                pending.push((default, true));
            }
            Term::Loc(_, t) => pending.push((t, in_tree)),
            _ => term.for_each_child(|t, _| pending.push((t, false))),
        }
    }
    true
}

/// How a member of a data group occurs in a field's type, when that isn't
/// strictly positive.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Occurrence {
    /// In the input of a function.
    Input,
    /// Applied to something other than the group's parameters.
    OtherParameters,
    /// Inside another type (a nested occurrence, like `List Rose`), or
    /// anywhere else.
    Inside,
}

/// Strict positivity across a data group: each member may appear in a
/// field's type only as itself applied to the group's parameters, possibly
/// as the result of a function whose inputs mention no member. The member
/// that doesn't, if one doesn't (the first found), and how it occurs.
fn not_positive(ty: &Term, group: &[DataId], depth: usize) -> Option<(DataId, Occurrence)> {
    let (mut ty, mut depth) = (ty, depth);
    loop {
        let found = occurs(ty, group)?;
        match ty.strip_loc() {
            Term::Data(d2, args) if group.contains(d2) => {
                let own_params = args.iter().enumerate().all(
                    |(j, arg)| matches!(arg.strip_loc(), Term::Var(ix) if depth - 1 - ix == j),
                );
                return (!own_params).then_some((*d2, Occurrence::OtherParameters));
            }
            Term::Pi(_, _, dom, cod) => match occurs(dom, group) {
                Some(d2) => return Some((d2, Occurrence::Input)),
                None => (ty, depth) = (cod, depth + 1),
            },
            _ => return Some((found, Occurrence::Inside)),
        }
    }
}

/// The error for field `x`, in which `found`, a member of `group`, occurs
/// `how`.
fn not_positive_error(
    cx: &Ctx,
    x: &Name,
    found: DataId,
    how: Occurrence,
    group: &[DataId],
) -> Diagnostic {
    let g = cx.g;
    let name = &g.data(found).name;
    let together = (group.len() > 1).then(|| {
        let names: Vec<String> = group
            .iter()
            .map(|d| format!("`{}`", g.data(*d).name))
            .collect();
        listed(&names)
    });
    match how {
        Occurrence::Input => {
            let note = match &together {
                Some(names) => format!(
                    "{names} are defined together, so their constructors can't contain functions \
                     that take any of them as input; that would make it possible to prove anything"
                ),
                None => "a data type can't contain functions that take that same type as input; \
                         that would make it possible to prove anything"
                    .to_string(),
            };
            cx.error(
                "E-POSITIVITY",
                format!("`{name}` is used in a negative position"),
                format!("field `{x}` takes a `{name}` as input"),
            )
            .with_note(note)
        }
        Occurrence::OtherParameters => cx
            .error(
                "E-POSITIVITY",
                format!("`{name}` is used with different parameters"),
                format!("field `{x}` uses `{name}` with parameters other than its own"),
            )
            .with_note(match &together {
                Some(names) => format!(
                    "{names} are defined together, so in their fields each can only be applied to \
                     the parameters they're all declared with, as written"
                ),
                None => "in its own fields, a data type can only be applied to the parameters \
                         it's declared with, as written"
                    .to_string(),
            }),
        Occurrence::Inside => cx
            .error(
                "E-POSITIVITY",
                format!("`{name}` is used inside another type"),
                format!("field `{x}` has `{name}` inside another type"),
            )
            .with_note(format!(
                "a data type's fields can contain {} only directly, or as the result of a function \
                 field: whether it's safe inside another type (such as a `List`) would depend on \
                 how that type uses it, which isn't checked",
                together
                    .as_deref()
                    .map_or_else(|| "it".to_string(), |names| names.to_string())
            ))
            .with_note(
                "for a tree whose children are in a list, write two types defined together \
                 instead: a tree, and a forest of trees",
            ),
    }
}

/// The first member of `group` that `term` mentions as a type or matches on.
fn occurs(term: &Term, group: &[DataId]) -> Option<DataId> {
    term.subterms().find_map(|(t, _)| match t {
        Term::Data(d2, _) | Term::Case(_, d2, _) if group.contains(d2) => Some(*d2),
        _ => None,
    })
}

/// Checks and adds a validator for proof parameter `param` of an exported
/// definition: `decision` must have type `decidable P`, where `P` is the
/// parameter's type, in the context of the parameters before it.
///
/// `decidable` must be shaped like the prelude's `Decidable`: one `Prop`
/// parameter `p`, and a first constructor whose only field is a proof of `p`.
/// That's what lets extracted code treat the first constructor as "the
/// precondition holds".
pub fn add_validator(
    g: &mut Globals,
    id: DefId,
    param: usize,
    decidable: DataId,
    decision: &Term,
) -> Result<()> {
    let Some(def) = g.defs.get(id.0) else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown definition",
        ));
    };
    let span = def.span;
    let tel = telescope(g, &def.ty_value, span)?;
    let mut cx = Ctx::new(g, span);
    if def.state != State::Final {
        return Err(malformed(
            &cx,
            "a validator for a definition that isn't final",
        ));
    }
    let Some((_, prop, true)) = tel.params.get(param) else {
        return Err(malformed(
            &cx,
            "a validator for a parameter that isn't erased",
        ));
    };
    if !shaped_like_decidable(g, decidable) || !case_only_in_tree(decision, false) {
        return Err(malformed(&cx, "a validator that isn't a decision"));
    }
    let failed = admissible(&cx, [decision], None)?;
    for (x, ty, _) in &tel.params[..param] {
        cx.bind(x.clone(), ty.clone());
    }
    let expected = Value::Data(decidable, vec![prop.clone()]);
    let decision = check(&mut cx, decision, &expected)?;
    if let Some(dep) = failed {
        return Err(failed_dependency(&cx, &def.name, &dep));
    }
    g.defs[id.0].validators.push(Validator { param, decision });
    Ok(())
}

/// Adds a decision procedure for proof field `field` of constructor `ctor`
/// of data type `d`, which extracted JS runs on a decoded value to establish
/// the proof the input doesn't carry (docs/proposals/records.md §11.3). It
/// must have type `Decidable P`, where `P` is the field's type, in the
/// context of the type's parameters and the constructor's earlier fields.
pub fn add_field_validator(
    g: &mut Globals,
    d: DataId,
    ctor: usize,
    field: usize,
    decidable: DataId,
    decision: &Term,
) -> Result<()> {
    let Some(data) = g.datas.get(d.0) else {
        return Err(Diagnostic::error(
            "E-MALFORMED",
            "malformed core term: reference to an unknown data type",
        ));
    };
    let mut cx = Ctx::new(g, data.span);
    if data.state != State::Final {
        return Err(malformed(
            &cx,
            "a validator for a data type that isn't final",
        ));
    }
    let Some(c) = data.ctors.get(ctor) else {
        return Err(malformed(
            &cx,
            "a validator for a constructor that doesn't exist",
        ));
    };
    if c.field_sorts.get(field) != Some(&Sort::Prop) {
        return Err(malformed(&cx, "a validator for a field that isn't a proof"));
    }
    if data
        .validators
        .iter()
        .any(|v| v.ctor == ctor && v.field == field)
    {
        return Err(malformed(&cx, "a second validator for one field"));
    }
    if !shaped_like_decidable(g, decidable) || !case_only_in_tree(decision, false) {
        return Err(malformed(&cx, "a validator that isn't a decision"));
    }
    let failed = admissible(&cx, [decision], None)?;
    let telescope = data.params.iter().chain(&c.fields[..field]);
    for (x, ty) in telescope {
        let value = cx.eval(ty)?;
        cx.bind(x.clone(), value);
    }
    let prop = cx.eval(&c.fields[field].1)?;
    let expected = Value::Data(decidable, vec![prop]);
    let decision = check(&mut cx, decision, &expected)?;
    if let Some(dep) = failed {
        return Err(failed_dependency(&cx, &data.name, &dep));
    }
    g.datas[d.0].validators.push(FieldValidator {
        ctor,
        field,
        decision,
    });
    Ok(())
}

/// Whether `decidable` is shaped like the prelude's `Decidable`: one `Prop`
/// parameter, and two constructors, the first holding a proof of it.
fn shaped_like_decidable(g: &Globals, decidable: DataId) -> bool {
    g.datas.get(decidable.0).is_some_and(|d| {
        d.state == State::Final
            && d.params.len() == 1
            && matches!(d.params[0].1.strip_loc(), Term::Sort(Sort::Prop))
            && d.ctors.len() == 2
            && d.ctors[0].fields.len() == 1
            && matches!(d.ctors[0].fields[0].1.strip_loc(), Term::Var(0))
    })
}

/// Whether `ty` is `Type`, `Prop`, or a function type ending in one: values of
/// such types are types, which are erased at runtime.
pub fn is_type_former(g: &Globals, level: usize, ty: &Value) -> budget::Result<bool> {
    let (mut level, mut ty) = (level, ty.clone());
    loop {
        match ty {
            Value::Sort(_) => return Ok(true),
            Value::Pi(_, _, _, cod) => {
                ty = cod.apply(g, Value::var(level))?;
                level += 1;
            }
            _ => return Ok(false),
        }
    }
}

/// A definition's parameters, as seen through its type.
pub struct Telescope {
    /// Name, type, and whether the parameter is erased at runtime.
    pub params: Vec<(Name, Value, bool)>,
    /// The result type, with the parameters as variables.
    pub result: Value,
    /// Whether values of the result type are erased (proofs or types).
    pub result_erased: bool,
}

/// Splits an already-checked type into its parameters and result.
pub fn telescope(g: &Globals, ty: &Value, span: Span) -> Result<Telescope> {
    let mut cx = Ctx::new(g, span);
    let mut params = Vec::new();
    let mut ty = ty.clone();
    while let Value::Pi(x, _, dom, cod) = &ty {
        let erased = is_erased(&mut cx, dom)?;
        let next = cod.apply(g, Value::var(cx.level()))?;
        cx.bind(x.clone(), (**dom).clone());
        params.push((x.clone(), (**dom).clone(), erased));
        ty = next;
    }
    let result_erased = is_erased(&mut cx, &ty)?;
    Ok(Telescope {
        params,
        result: ty,
        result_erased,
    })
}

fn is_erased(cx: &mut Ctx, ty: &Value) -> Result<bool> {
    Ok(is_type_former(cx.g, cx.level(), ty)? || sort_of(cx, ty)? == Sort::Prop)
}
