//! A derived `==` for data types that aren't records: `T.%decEq`, a proved
//! decision procedure for `=` on `T`, which `==` then finds (`auto.rs`).
//! Records get theirs from `records.rs`, which this follows: the procedure
//! is generated as source, naming the library through `Std.` paths, and
//! elaborated like any definition, so the kernel checks it and nothing in
//! the kernel changes.
//!
//! It's derived automatically, when `T` is declared, for every type it can
//! be: one with constructors (not a proposition, not defined together with
//! other types) whose parameters are types and whose fields are data that
//! doesn't depend on earlier fields, and is either `T` itself, with the same
//! parameters, or has a decision procedure for `=` already. A parameter `a`
//! that fields use becomes an argument `(x y : a) -> Decidable (x = y)`, as
//! `List.decEq` takes. Otherwise nothing is generated, and why not is kept
//! for the note when `==` is used on `T`. The prelude's types are skipped:
//! those that need one have one written by hand.
//!
//! For `type T a = | C1 … | C2 x y | …` it generates
//!
//! - `T.%tag : [a : Type] -> T a -> Nat`, each constructor's position (only
//!   with two constructors or more);
//! - `T.%C2%1 : [a : Type] -> A -> T a -> A` for each field: that field of a
//!   `C2`, or the first argument for another constructor. With `Eq.cong`,
//!   this gives injectivity: `C2 x y = C2 x' y'` implies `y = y'`;
//! - and, as source (two constructors or more for `T.%differ`):
//!
//! ```text
//! T.%differ : [a : Type] -> (r : T a) -> (s : T a) ->
//!   Nat.equal (T.%tag r) (T.%tag s) = False -> Not (r = s)
//! T.%differ r s t e = Nat.equalFalse (T.%tag r) (T.%tag s) t (Eq.cong T.%tag e)
//!
//! T.%decEq : [a : Type] -> ((x : a) -> (y : a) -> Decidable (x = y)) ->
//!   (r : T a) -> (s : T a) -> Decidable (r = s)
//! T.%decEq d (C2 a0 a1) (C2 b0 b1) =
//!   if h0 : a0 = b0 then
//!     if h1 : a1 = b1 then Yes (J (\y q -> (C2 a0 a1 : T a) = C2 b0 y) (J … rfl h0) h1)
//!     else No (\e -> h1 (Eq.cong (T.%C2%1 a1) e))
//!   else No (\e -> h0 (Eq.cong (T.%C2%0 a0) e))
//! …   -- one equation for each constructor
//! T.%decEq d r s = No (T.%differ r s rfl)
//! ```
//!
//! The last equation covers every pair of different constructors: the case
//! tree checks it once for each, where the tags are two different numbers,
//! so `rfl` proves `Nat.equal` of them is `False`. (That's n² - n checks for
//! n constructors, which is why the proof is in `T.%differ`, checked once.)
//! A field of type `T a` is decided by calling `T.%decEq d` on it
//! (structural recursion) through `Decidable.elim`, since `if h : a0 = b0`
//! would look for a procedure that isn't defined yet. A field whose type
//! mentions `a` (`a` itself, `List a`) is decided with `d`: while `T.%decEq`
//! is elaborated, and only then, `auto` also uses the decision procedures
//! that are arguments in scope (`Elaborator::local_deciders`).
//!
//! Generating eagerly, when `T` is declared, is simpler than on first use,
//! which would mean elaborating a new definition in the middle of the one
//! using `==`. It costs a few `==` searches per type (about 1–6 ms per
//! type, more for many constructors).
//!
//! Names generated here contain `%`, which source can't write, so they never
//! clash with the user's (a program may still define its own `T.decEq`,
//! which, being more recent, `==` prefers).

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::check as kernel;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{eval, force, quote, unused};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, BinOp, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, auto};

/// How `==` compares one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
enum Field {
    /// It's `T` again: a recursive call.
    Recursive,
    /// Its type has a decision procedure, which `if h : x = y` finds.
    Decided,
}

/// What a derived `==` for a data type is made from.
struct Plan {
    /// Which parameters take a decision procedure: those fields use.
    deciders: Vec<bool>,
    /// For each constructor, each field's.
    fields: Vec<Vec<Field>>,
}

impl Elaborator {
    /// After data type `d` (not a record) is admitted: its `==`, if one can
    /// be derived, or else why not.
    pub(crate) fn derive_data_eq(&mut self, d: DataId) -> Result<()> {
        // Nor for a type the compiler declared, whose constructors' names
        // source can't write: an ability's operations (`effects.rs`).
        let generated = (self.globals.data(d).ctors.iter()).any(|c| c.name.starts_with('%'));
        if self.loading_prelude
            || generated
            || self.globals.registry.data(Builtin::Decidable).is_none()
        {
            return Ok(());
        }
        let plan = match self.eq_plan(d)? {
            Ok(plan) => plan,
            Err(why) => {
                self.no_eq.insert(d, why);
                return Ok(());
            }
        };
        let ctors = self.globals.data(d).ctors.len();
        if ctors > 1 {
            self.derive_tag(d)?;
        }
        for c in 0..ctors {
            for k in 0..plan.fields[c].len() {
                self.derive_field(d, c, k)?;
            }
        }
        self.clear_metas();
        let (differ, signature, equations) = self.eq_source(d, &plan);
        let result = match differ {
            Some((signature, equation)) => self.definition(&signature, &[equation]),
            None => Ok(()),
        };
        self.clear_metas();
        self.local_deciders.set(true);
        let result = result.and_then(|()| self.definition(&signature, &equations));
        self.local_deciders.set(false);
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if e.code == "E-RESOURCE" => return Err(e),
            Err(e) => {
                self.no_eq
                    .insert(d, format!("deriving it failed: {}", e.message));
            }
        }
        Ok(())
    }

    /// Whether `==` can be derived for `d`, and how; or why not.
    fn eq_plan(&mut self, d: DataId) -> Result<std::result::Result<Plan, String>> {
        let g = &self.globals;
        let data = g.data(d);
        let name = data.name.to_string();
        let np = data.params.len();
        if data.group.len() > 1 {
            return Ok(Err(format!(
                "`{name}` is defined together with other types, which `==` isn't derived for yet"
            )));
        }
        if data.sort == Sort::Prop {
            return Ok(Err(format!("`{name}` is a proposition")));
        }
        if data.ctors.is_empty() {
            return Ok(Err(format!("`{name}` has no constructors")));
        }
        for (x, ty) in &data.params {
            if !matches!(ty.strip_loc(), Term::Sort(Sort::Type(0))) {
                return Ok(Err(format!(
                    "its parameter `{x}` isn't a `Type`, and `==` is only derived for types \
                     whose parameters are"
                )));
            }
        }
        // Each field, classified; the decidable ones are checked below.
        let mut deciders = vec![false; np];
        let mut fields = Vec::new();
        let mut to_decide = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let mut kinds = Vec::new();
            for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                let what = format!("the field `{field}` of `{}`", ctor.name);
                if ctor.field_erased[i] {
                    return Ok(Err(format!(
                        "{what} is a proof or a type, which `==` can't compare: two values \
                         equal in their data can still differ there"
                    )));
                }
                if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                    return Ok(Err(format!(
                        "the type of {what} depends on an earlier field, which `==` isn't \
                         derived for yet"
                    )));
                }
                // The field's type with the parameters as variables `0..np`.
                let env: Vec<Value> = (0..np)
                    .map(Value::var)
                    .chain((0..i).map(|_| unused()))
                    .collect();
                let value = force(g, eval(g, &env, ty)?)?;
                if matches!(value, Value::Pi(..)) {
                    return Ok(Err(format!(
                        "{what} is a function, and functions can't be compared"
                    )));
                }
                let direct = match ty.strip_loc() {
                    Term::Data(e, args) if *e == d => args.iter().enumerate().all(
                        |(j, a)| matches!(a.strip_loc(), Term::Var(v) if *v == i + np - 1 - j),
                    ),
                    _ => false,
                };
                if direct {
                    kinds.push(Field::Recursive);
                    continue;
                }
                if ty
                    .subterms()
                    .any(|(t, _)| matches!(t, Term::Data(e, _) if *e == d))
                {
                    return Ok(Err(format!(
                        "{what} contains `{name}` inside another type, which `==` isn't \
                         derived for yet"
                    )));
                }
                for (j, used) in deciders.iter_mut().enumerate() {
                    *used |= ty.mentions(i + np - 1 - j);
                }
                kinds.push(Field::Decided);
                to_decide.push((c, i, value));
            }
            fields.push(kinds);
        }
        // Every other field's type needs a decision procedure for `=`, given
        // one for each parameter.
        let decidable = self.globals.registry.data(Builtin::Decidable);
        let Some(decidable) = decidable else {
            return Ok(Err("there's no prelude".into()));
        };
        self.clear_metas();
        let span = self.globals.data(d).span;
        let mut cx = Ctx::new(self, span);
        for _ in 0..np {
            cx.bind_hidden("%p".into(), Value::Sort(Sort::Type(0)));
        }
        for (j, used) in deciders.iter().enumerate() {
            if *used {
                let ty = cx.eval(&decider_type(decidable, cx.level(), j))?;
                cx.bind_hidden("%d".into(), ty);
            }
        }
        self.local_deciders.set(true);
        let mut why = None;
        for (c, i, ty) in to_decide {
            let mark = cx.mark();
            let level = cx.level();
            cx.bind_hidden("x".into(), ty.clone());
            cx.bind_hidden("y".into(), ty.clone());
            let eq = Value::Eq(
                Rc::new(ty.clone()),
                Rc::new(Value::var(level)),
                Rc::new(Value::var(level + 1)),
            );
            let found = auto::decide(&mut cx, &eq, 0);
            cx.reset(mark);
            match found {
                Ok(_) => {}
                Err(e) if e.code == "E-RESOURCE" => {
                    self.local_deciders.set(false);
                    return Err(e);
                }
                Err(_) => {
                    let ctor = &cx.g().data(d).ctors[c];
                    why = Some(format!(
                        "the field `{}` of `{}` has type `{}`, which has no decision procedure \
                         for `=` (when `{name}` was declared)",
                        ctor.fields[i].0,
                        ctor.name,
                        cx.show(&ty)
                    ));
                    break;
                }
            }
        }
        drop(cx);
        self.local_deciders.set(false);
        self.clear_metas();
        Ok(match why {
            Some(why) => Err(why),
            None => Ok(Plan { deciders, fields }),
        })
    }

    /// Declares `T.%tag : [params] -> T params -> Nat`.
    fn derive_tag(&mut self, d: DataId) -> Result<()> {
        let Some(nat) = self.globals.registry.data(Builtin::Nat) else {
            return Ok(());
        };
        let data = self.globals.data(d);
        let np = data.params.len();
        let params: Vec<Term> = (0..np).map(|k| Term::Var(np - 1 - k)).collect();
        let ty = Term::Pi(
            "r".into(),
            Icit::Explicit,
            Rc::new(Term::data(d, params)),
            Rc::new(Term::data(nat, Vec::new())),
        );
        let branches: Vec<Branch> = data
            .ctors
            .iter()
            .enumerate()
            .map(|(c, ctor)| Branch {
                body: Rc::new(Term::Nat(Rc::new(BigUint::from(c)))),
                names: ctor.fields.iter().map(|(x, _)| x.clone()).collect(),
            })
            .collect();
        let body = Term::Lam(
            "r".into(),
            Icit::Explicit,
            Rc::new(Term::Case(0, d, branches.into())),
        );
        self.declare_member(d, "%tag", ty, body)
    }

    /// Declares `T.%C%k : [params] -> A -> T params -> A`: field `k` of a
    /// `C`, or the first argument for another constructor.
    fn derive_field(&mut self, d: DataId, c: usize, k: usize) -> Result<()> {
        let g = &self.globals;
        let data = g.data(d);
        let np = data.params.len();
        let ctor = &data.ctors[c];
        let env: Vec<Value> = (0..np)
            .map(Value::var)
            .chain((0..k).map(|_| unused()))
            .collect();
        let field = eval(g, &env, &ctor.fields[k].1)?;
        let params: Vec<Term> = (0..np).map(|j| Term::Var(np - j)).collect();
        let ty = Term::Pi(
            "default".into(),
            Icit::Explicit,
            Rc::new(quote(g, np, &field)?),
            Rc::new(Term::Pi(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::data(d, params)),
                Rc::new(quote(g, np + 2, &field)?),
            )),
        );
        let branches: Vec<Branch> = data
            .ctors
            .iter()
            .enumerate()
            .map(|(other, o)| {
                let n = o.fields.len();
                let body = if other == c {
                    Term::Var(n - 1 - k)
                } else {
                    Term::Var(n + 1)
                };
                Branch {
                    body: Rc::new(body),
                    names: o.fields.iter().map(|(x, _)| x.clone()).collect(),
                }
            })
            .collect();
        let body = Term::Lam(
            "default".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::Case(0, d, branches.into())),
            )),
        );
        let member = format!("%{}%{k}", ctor.name);
        self.declare_member(d, &member, ty, body)
    }

    /// Adds `T.member`, of type `[params] -> ty`, with body `[params] ->
    /// body`, in `T`'s namespace.
    fn declare_member(&mut self, d: DataId, member: &str, ty: Term, body: Term) -> Result<()> {
        let data = self.globals.data(d);
        let (mut ty, mut body) = (ty, body);
        for (x, t) in data.params.iter().rev() {
            ty = Term::Pi(x.clone(), Icit::Implicit, Rc::new(t.clone()), Rc::new(ty));
            body = Term::Lam(x.clone(), Icit::Implicit, Rc::new(body));
        }
        let name: Name = format!("{}.{member}", data.name).into();
        let span = data.span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        let key = Self::member_key(&self.data_key(d), member);
        self.scope.insert(&key, Global::Def(id), span, false);
        Ok(())
    }

    /// The source of `T.%differ` (with two constructors or more) and of
    /// `T.%decEq`: their signatures and equations.
    #[allow(clippy::type_complexity)]
    fn eq_source(&self, d: DataId, plan: &Plan) -> (Option<(Decl, Decl)>, Decl, Vec<Decl>) {
        let data = self.globals.data(d);
        let ty_name = self.relative_to_root(&data.name);
        let span = data.span;
        let n = |text: &str| ast::Name {
            text: text.to_string(),
            span,
        };
        let var = |text: &str| Expr::Var(n(text));
        let apps = |head: Expr, args: Vec<Expr>| {
            args.into_iter()
                .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
        };
        let eq = |a: Expr, b: Expr| Expr::Binary(BinOp::Eq, Box::new(a), Box::new(b));
        let lam = |names: &[&str], body: Expr| {
            Expr::Lam(names.iter().map(|x| n(x)).collect(), Box::new(body), span)
        };
        let pi = |x: &str, implicit: bool, dom: Expr, cod: Expr| Expr::Pi {
            names: vec![n(x)],
            implicit,
            auto: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
            span,
        };
        let decidable = |p: Expr| apps(var("Std.Decidable"), vec![p]);
        let np = data.params.len();
        let param = |j: usize| format!("%p{j}");
        let decider = |j: usize| format!("%d{j}");
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let h = |k: usize| format!("%h{k}");
        let dec_eq = format!("{ty_name}.%decEq");
        let deciders: Vec<usize> = (0..np).filter(|j| plan.deciders[*j]).collect();

        // [%p0 : Type] -> … -> (%d0 : (%x : %p0) -> (%y : %p0) -> Decidable (%x = %y)) -> … ->
        //   (%r %s : T %p0 …) -> Decidable (%r = %s)
        let this = apps(var(&ty_name), (0..np).map(|j| var(&param(j))).collect());
        let mut ty = Expr::Pi {
            names: vec![n("%r"), n("%s")],
            implicit: false,
            auto: false,
            dom: Box::new(this.clone()),
            cod: Box::new(decidable(eq(var("%r"), var("%s")))),
            span,
        };
        for &j in deciders.iter().rev() {
            let procedure = pi(
                "%x",
                false,
                var(&param(j)),
                pi(
                    "%y",
                    false,
                    var(&param(j)),
                    decidable(eq(var("%x"), var("%y"))),
                ),
            );
            ty = pi(&decider(j), false, procedure, ty);
        }
        for j in (0..np).rev() {
            ty = pi(&param(j), true, Expr::Type(0, span), ty);
        }
        let name = n(&dec_eq);
        let signature = Decl::Signature {
            name: name.clone(),
            ty,
            theorem: false,
            export: false,
            synonym: false,
            span,
        };

        let decider_patterns = || -> Vec<Pattern> {
            deciders
                .iter()
                .map(|&j| Pattern::Var(n(&decider(j))))
                .collect()
        };
        let recurse = || {
            apps(
                var(&dec_eq),
                deciders.iter().map(|&j| var(&decider(j))).collect(),
            )
        };
        let mut equations = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let ctor_name = format!("{ty_name}.{}", ctor.name);
            let count = ctor.fields.len();
            let pattern = |f: &dyn Fn(usize) -> String| {
                Pattern::Ctor(
                    n(&ctor_name),
                    (0..count).map(|k| Pattern::Var(n(&f(k)))).collect(),
                    span,
                )
            };
            // `(C %a0 … : T %p0 …) = C %b0 … %b(k-1) %y %a(k+1) …`, annotated
            // for the parameters fields don't determine.
            let motive_eq = |k: usize| {
                let left = Expr::Ann(
                    Box::new(apps(
                        var(&ctor_name),
                        (0..count).map(|j| var(&a(j))).collect(),
                    )),
                    Box::new(this.clone()),
                    span,
                );
                let right = apps(
                    var(&ctor_name),
                    (0..count)
                        .map(|j| match j.cmp(&k) {
                            std::cmp::Ordering::Less => var(&b(j)),
                            std::cmp::Ordering::Equal => var("%y"),
                            std::cmp::Ordering::Greater => var(&a(j)),
                        })
                        .collect(),
                );
                eq(left, right)
            };
            let mut proof = var("rfl");
            for k in 0..count {
                let motive = lam(&["%y", "%q"], motive_eq(k));
                proof = apps(var("J"), vec![motive, proof, var(&h(k))]);
            }
            let mut body = apps(var("Std.Decidable.Yes"), vec![proof]);
            for k in (0..count).rev() {
                let field = format!("{ty_name}.%{}%{k}", ctor.name);
                let cong = apps(
                    var("Std.Eq.cong"),
                    vec![apps(var(&field), vec![var(&a(k))]), var("%e")],
                );
                let refute = lam(&["%e"], apps(var(&h(k)), vec![cong]));
                let no = apps(var("Std.Decidable.No"), vec![refute]);
                body = match plan.fields[c][k] {
                    Field::Recursive => apps(
                        var("Std.Decidable.elim"),
                        vec![
                            apps(recurse(), vec![var(&a(k)), var(&b(k))]),
                            lam(&[&h(k)], body),
                            lam(&[&h(k)], no),
                        ],
                    ),
                    Field::Decided => Expr::If {
                        binder: Some(n(&h(k))),
                        cond: Box::new(eq(var(&a(k)), var(&b(k)))),
                        then: Box::new(body),
                        otherwise: Box::new(no),
                        span,
                    },
                };
            }
            let mut patterns = decider_patterns();
            patterns.push(pattern(&a));
            patterns.push(pattern(&b));
            equations.push(Decl::Equation {
                name: name.clone(),
                patterns,
                rhs: Some(body),
                arm: None,
                span,
            });
        }
        let mut differ = None;
        if data.ctors.len() > 1 {
            // Different constructors: their tags differ. Proved once, by
            // `T.%differ`, which each pair of constructors gives `rfl`:
            //
            // T.%differ : [%p0 : Type] -> … -> (%r %s : T %p0 …) ->
            //   Nat.equal (T.%tag %r) (T.%tag %s) = False -> Not (%r = %s)
            // T.%differ %r %s %t %e = Nat.equalFalse (T.%tag %r) (T.%tag %s) %t (Eq.cong T.%tag %e)
            let tag = format!("{ty_name}.%tag");
            let tag_of = |x: &str| apps(var(&tag), vec![var(x)]);
            let differ_name = n(&format!("{ty_name}.%differ"));
            let unequal = eq(
                apps(var("Std.Nat.equal"), vec![tag_of("%r"), tag_of("%s")]),
                var("Std.Bool.False"),
            );
            let mut ty = Expr::Pi {
                names: vec![n("%r"), n("%s")],
                implicit: false,
                auto: false,
                dom: Box::new(this.clone()),
                cod: Box::new(Expr::Arrow(
                    Box::new(unequal),
                    Box::new(apps(var("Std.Not"), vec![eq(var("%r"), var("%s"))])),
                )),
                span,
            };
            for j in (0..np).rev() {
                ty = pi(&param(j), true, Expr::Type(0, span), ty);
            }
            let cong = apps(var("Std.Eq.cong"), vec![var(&tag), var("%e")]);
            let rhs = apps(
                var("Std.Nat.equalFalse"),
                vec![tag_of("%r"), tag_of("%s"), var("%t"), cong],
            );
            differ = Some((
                Decl::Signature {
                    name: differ_name.clone(),
                    ty,
                    theorem: false,
                    export: false,
                    synonym: false,
                    span,
                },
                Decl::Equation {
                    name: differ_name,
                    patterns: ["%r", "%s", "%t", "%e"]
                        .iter()
                        .map(|x| Pattern::Var(n(x)))
                        .collect(),
                    rhs: Some(rhs),
                    arm: None,
                    span,
                },
            ));
            let refute = apps(
                var(&format!("{ty_name}.%differ")),
                vec![var("%r"), var("%s"), var("rfl")],
            );
            let mut patterns = decider_patterns();
            patterns.push(Pattern::Var(n("%r")));
            patterns.push(Pattern::Var(n("%s")));
            equations.push(Decl::Equation {
                name,
                patterns,
                rhs: Some(apps(var("Std.Decidable.No"), vec![refute])),
                arm: None,
                span,
            });
        }
        (differ, signature, equations)
    }
}

/// `(x : p) -> (y : p) -> Decidable (x = y)`, for parameter `j` (at level
/// `j`), as a term at level `level`.
fn decider_type(decidable: DataId, level: usize, j: usize) -> Term {
    let p = |at: usize| Rc::new(Term::Var(at - 1 - j));
    Term::Pi(
        "x".into(),
        Icit::Explicit,
        p(level),
        Rc::new(Term::Pi(
            "y".into(),
            Icit::Explicit,
            p(level + 1),
            Rc::new(Term::data(
                decidable,
                vec![Term::Eq(
                    Some(p(level + 2)),
                    Rc::new(Term::Var(1)),
                    Rc::new(Term::Var(0)),
                )],
            )),
        )),
    )
}
