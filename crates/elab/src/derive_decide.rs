//! A derived decision procedure for each record of propositions that can
//! have one (SW-1015): a `Prop` record whose fields' propositions are each
//! decided by something `if h:` can find gets, written test first as a
//! hand-written instance is (docs/proposals/decidable-record.md §5.3),
//!
//! ```text
//! type Ok (n: Nat): Prop = { small: n < 10, even: n % 2 = 0 }
//!
//! Ok.%param%0 : Type                  -- the parameters' types, so the source
//! Ok.%field%0 : (n: Nat) -> Prop      --   below is typed; each field's
//! Ok.%field%1 : (n: Nat) -> Prop      --   proposition, without earlier proofs
//!
//! Ok.%holds : (%p0: Ok.%param%0) -> Bool
//! Ok.%holds %p0 = (D0 %p0).holds && (D1 %p0).holds
//!   -- Dk is `if %h: Ok.%field%k %p0 then Decidable.yes %h else Decidable.no %h`
//!
//! Ok.%holdsSound %p0 %h = Decidable.sound whole %h
//! Ok.%holdsComplete %p0 %r = Decidable.complete whole %r
//!   -- whole = Decidable.map (Decidable.andThen D0 (u => D1))
//! --     (q => Ok.%mk q.left q.right) (r => Both r.small r.even)
//!
//! instance Ok.%instDecidable [n: _]: Std.Decidable (Ok n) :=
//!   { holds = Ok.%holds n, sound = Ok.%holdsSound n, complete = Ok.%holdsComplete n }
//!
//! @[reading] Ok.%holdsReads %p0 : Ok.%holds %p0 = True ↔ Ok %p0
//! @[reading] Ok.%holdsReadsFalse %p0 : Ok.%holds %p0 = False ↔ ¬Ok %p0
//! ```
//!
//! so `auto`, `byDecision`, `if h: Ok n` and the counterexample search
//! decide it, as they decide `And`; the decision's `holds` is a test that
//! computes where the fields' decisions do, and the readings (docs/proposals/
//! bool-as-proposition.md §5) take a fact about it apart as the record. Each
//! field's decision is found by `if h:`, as any `if h:` finds it: an instance
//! in this module above the record, or in a namespace it uses. It's source,
//! elaborated and checked like any definition, so the kernel checks it. The
//! test and the proofs state the same decision, so that its `holds` is
//! exactly the test.
//!
//! It's generated for a declared record that is a proposition (not defined
//! together with other types, without indices) whose fields' types don't
//! mention earlier fields: the fields' propositions are stated without the
//! earlier fields' proofs, which a test has none of. When a field has no
//! decision (a proposition defined by recursion on a variable, say, that
//! nothing decides) nothing is generated, and why is kept for the note when
//! it's wanted (`no_decide`). The core's records (`And`, `Iff`) have theirs
//! written by hand.

use std::rc::Rc;

use stitchwort_core::value::{eval, force, quote, unused};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, BinOp, Bracket, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, kernel};

impl Elaborator {
    /// After record `d` is admitted: `T.%instDecidable`, if `d` is a
    /// proposition whose fields can each be decided.
    pub(crate) fn derive_record_decidable(&mut self, d: DataId) -> Result<()> {
        let data = self.kernel.data(d);
        if self.unit.loading_prelude
            || data.sort() != Sort::Prop
            || data.group().len() > 1
            || !data.indices().is_empty()
            || data.ctors().len() != 1
        {
            return Ok(());
        }
        let fields = &data.ctors()[0].fields;
        if let Some(k) = (0..fields.len()).find(|&k| crate::cases::mentions_fields(&fields[k].1, k))
        {
            let why = format!(
                "the type of its field `{}` mentions an earlier field",
                fields[k].0
            );
            self.tables.no_decide.insert(&self.session.owners, d, why);
            return Ok(());
        }
        // Each field's proposition must be decided by something `auto` finds,
        // given nothing about the parameters: checked before anything is
        // declared, so a record that can't be decided leaves no half-made
        // instance behind (which the check cache couldn't keep).
        self.clear_metas();
        if let Some(why) = self.undecidable_field(d)? {
            self.tables.no_decide.insert(
                &self.session.owners,
                d,
                format!("deriving it failed: {why}"),
            );
            return Ok(());
        }
        self.clear_metas();
        let result = self.define_decidable(d);
        self.clear_metas();
        match result {
            Ok(()) => Ok(()),
            Err(e) if e.code == "E-RESOURCE" => Err(e),
            Err(e) => {
                self.tables.no_decide.insert(
                    &self.session.owners,
                    d,
                    format!("deriving it failed: {}", e.message),
                );
                Ok(())
            }
        }
    }

    /// Declares and defines everything [`Self::decidable_source`] writes.
    fn define_decidable(&mut self, d: DataId) -> Result<()> {
        self.declare_decidable_helpers(d)?;
        self.clear_metas();
        let source = self.decidable_source(d);
        let steps = [source.holds, source.sound, source.complete, source.instance]
            .into_iter()
            .chain(source.readings);
        for (signature, equations) in steps {
            self.clear_metas();
            self.definition(&signature, &equations)?;
        }
        Ok(())
    }

    /// Why the proposition of some field of record `d` has no decision
    /// `auto` finds (with the record's parameters as variables), if so.
    fn undecidable_field(&mut self, d: DataId) -> Result<Option<String>> {
        let data = self.kernel.data(d);
        let span = data.span();
        let np = data.params().len();
        let params: Vec<(Name, Term)> = data.params().to_vec();
        let fields: Vec<Term> = data.ctors()[0]
            .fields
            .iter()
            .map(|(_, t)| t.clone())
            .collect();
        let mut why = None;
        {
            let mut cx = Ctx::new(self, span);
            for (x, ty) in &params {
                let ty = cx.eval(ty)?;
                cx.bind_hidden(x.clone(), ty);
            }
            for (k, ty) in fields.iter().enumerate() {
                let env: Vec<Value> = (0..np + k).map(Value::var).collect();
                let prop = force(&cx.g(), eval(&cx.g(), &env, ty)?)?;
                match crate::auto::decide(&mut cx, &prop, 0) {
                    Ok(_) => {}
                    Err(e) if e.code == "E-RESOURCE" => return Err(e),
                    Err(e) => {
                        why = Some(e.message);
                        break;
                    }
                }
            }
        }
        self.clear_metas();
        Ok(why)
    }

    /// Declares, unless made already, what the generated source states its
    /// types with (all arguments explicit, the parameters only):
    /// `T.%param%j : (earlier parameters) -> Type`, the type of parameter
    /// `j`, so a test can be written with typed parameters, and `T.%field%k
    /// : (parameters) -> Prop`, the proposition of field `k`, without the
    /// proofs of the fields before it (which its type doesn't mention).
    fn declare_decidable_helpers(&mut self, d: DataId) -> Result<()> {
        let data = self.kernel.data(d);
        let span = data.span();
        let np = data.params().len();
        let params: Vec<(Name, Term)> = data.params().to_vec();
        let fields: Vec<Term> = data.ctors()[0]
            .fields
            .iter()
            .map(|(_, t)| t.clone())
            .collect();
        // The universe each parameter's type is in, as the kernel infers it.
        let mut sorts = Vec::new();
        {
            let mut cx = Ctx::new(self, span);
            for (x, ty) in &params {
                let mut kcx = crate::rewrite::kernel_context(&cx)?;
                let (_, sort) = kernel::without_glue(&cx.g(), || kernel::infer(&mut kcx, ty))?;
                sorts.push(force(&cx.g(), sort)?);
                let ty = cx.eval(ty)?;
                cx.bind_hidden(x.clone(), ty);
            }
        }
        self.clear_metas();
        let pi = |binders: &[(Name, Term)], result: Term| {
            binders.iter().rev().fold(result, |ty, (x, t)| {
                Term::Pi(x.clone(), Icit::Explicit, Rc::new(t.clone()), Rc::new(ty))
            })
        };
        let lam = |binders: &[(Name, Term)], body: Term| {
            binders.iter().rev().fold(body, |body, (x, _)| {
                Term::Lam(x.clone(), Icit::Explicit, Rc::new(body))
            })
        };
        let mut helpers: Vec<(String, Term, Term)> = Vec::new();
        for (j, sort) in sorts.iter().enumerate() {
            let Value::Sort(sort) = sort else {
                continue;
            };
            helpers.push((
                format!("%param%{j}"),
                pi(&params[..j], Term::Sort(*sort)),
                lam(&params[..j], params[j].1.clone()),
            ));
        }
        {
            let g = &self.ev();
            for (k, field) in fields.iter().enumerate() {
                let env: Vec<Value> = (0..np)
                    .map(Value::var)
                    .chain((0..k).map(|_| unused()))
                    .collect();
                let prop = quote(g, np, &eval(g, &env, field)?)?;
                helpers.push((
                    format!("%field%{k}"),
                    pi(&params, Term::Sort(Sort::Prop)),
                    lam(&params, prop),
                ));
            }
        }
        for (member, ty, body) in helpers {
            let key = Self::member_key(&self.data_key(d), &member);
            if self.scope.get(&key).is_some() {
                continue;
            }
            let name: Name = format!("{}.{member}", self.kernel.data(d).name()).into();
            let id = kernel::declare_def(
                &mut self.kernel,
                &self.tables,
                &self.unit,
                &name,
                &ty,
                false,
                false,
                span,
            )?;
            kernel::define_def(&mut self.kernel, &self.tables, id, &body)?;
            self.scope.insert(&key, Global::Def(id), span, false);
        }
        Ok(())
    }

    /// The test, its two proofs, the instance and its two readings, as
    /// source (see the module comment).
    fn decidable_source(&self, d: DataId) -> DecidableSource {
        let data = self.kernel.data(d);
        let ty_name = self.relative_to_root(data.name());
        let span = data.span();
        let n = |text: &str| ast::Name {
            text: text.to_string(),
            span,
        };
        let var = |text: &str| Expr::Var(n(text));
        let apps = |head: Expr, args: Vec<Expr>| {
            args.into_iter()
                .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
        };
        let lam = |names: &[&str], body: Expr| {
            Expr::Lam(names.iter().map(|x| n(x)).collect(), Box::new(body), span)
        };
        let eq = |a: Expr, b: Expr| Expr::Binary(BinOp::Eq, Box::new(a), Box::new(b));
        let record = |fields: Vec<(&str, Expr)>| Expr::Record {
            base: None,
            fields: fields.into_iter().map(|(f, e)| (n(f), e)).collect(),
            span,
        };
        let signature =
            |name: &ast::Name, ty: Expr, instance: bool, reading: bool| Decl::Signature {
                name: name.clone(),
                ty,
                theorem: reading,
                export: false,
                synonym: false,
                instance,
                decreasing: None,
                opaque: false,
                unfolding: Vec::new(),
                defaults: Vec::new(),
                attrs: if reading {
                    vec![ast::Attribute {
                        name: n("reading"),
                        arg: None,
                        span,
                    }]
                } else {
                    Vec::new()
                },
                body_error: None,
                span,
            };
        let np = data.params().len();
        let ctor = &data.ctors()[0];
        let count = ctor.fields.len();
        // The parameters' own names for the instance, so a note about a
        // field reads as the field's type is written (`no way to decide
        // `Even n``); `%p0` … elsewhere.
        let param = |j: usize| data.params()[j].0.to_string();
        let own = |j: usize| format!("%p{j}");
        // An `auto` parameter is given by name (docs/proposals/interfaces.md
        // §7.5): `T p [ord := q]`.
        let applied = |name: &dyn Fn(usize) -> String| {
            apps(
                var(&ty_name),
                (0..np)
                    .map(|j| {
                        if data.auto_params().get(j) == Some(&true) {
                            Expr::NamedArg(
                                n(&data.params()[j].0),
                                Box::new(var(&name(j))),
                                span,
                                Bracket::Square,
                            )
                        } else {
                            var(&name(j))
                        }
                    })
                    .collect(),
            )
        };
        let this = applied(&own);
        let args = || -> Vec<Expr> { (0..np).map(|j| var(&own(j))).collect() };
        // (%p0: T.%param%0) -> (%p1: T.%param%1 %p0) -> … -> rest
        let params_pi = |rest: Expr| {
            (0..np).rev().fold(rest, |cod, j| Expr::Pi {
                names: vec![n(&own(j))],
                implicit: false,
                auto: false,
                dom: Box::new(apps(
                    var(&format!("{ty_name}.%param%{j}")),
                    (0..j).map(|i| var(&own(i))).collect(),
                )),
                cod: Box::new(cod),
                span,
            })
        };
        let patterns = |extra: Option<&str>| -> Vec<Pattern> {
            (0..np)
                .map(own)
                .chain(extra.map(str::to_string))
                .map(|x| Pattern::Var(n(&x)))
                .collect()
        };
        let equation = |name: &ast::Name, extra: Option<&str>, rhs: Expr| Decl::Equation {
            guard: None,
            name: name.clone(),
            patterns: patterns(extra),
            rhs: Some(rhs),
            arm: None,
            span,
        };

        let holds_name = n(&format!("{ty_name}.%holds"));
        let sound_name = n(&format!("{ty_name}.%holdsSound"));
        let complete_name = n(&format!("{ty_name}.%holdsComplete"));
        let test = apps(var(&holds_name.text), args());
        let is_true = eq(test.clone(), var("Std.Bool.True"));
        let is_false = eq(test.clone(), var("Std.Bool.False"));

        // Field `k`'s decision, found as `if %h: P` finds it:
        // `if %h: P then Decidable.yes %h else Decidable.no %h`.
        let decision = |k: usize| {
            let prop = apps(var(&format!("{ty_name}.%field%{k}")), args());
            Expr::Ann(
                Box::new(Expr::If {
                    binder: Some(n("%h")),
                    cond: Box::new(prop.clone()),
                    then: Box::new(apps(var("Std.Decidable.yes"), vec![var("%h")])),
                    otherwise: Box::new(apps(var("Std.Decidable.no"), vec![var("%h")])),
                    span,
                }),
                Box::new(apps(var("Std.Decidable"), vec![prop])),
                span,
            )
        };
        let holds_of = |k: usize| apps(var("Std.Decidable.holds"), vec![decision(k)]);
        // The test: the fields' tests joined by `&&`, each run only once
        // those before it hold.
        let body = if count == 0 {
            var("Std.Bool.True")
        } else {
            let mut tests = holds_of(count - 1);
            for k in (0..count - 1).rev() {
                tests = Expr::Binary(BinOp::And, Box::new(holds_of(k)), Box::new(tests));
            }
            tests
        };
        let holds_signature = signature(&holds_name, params_pi(var("Std.Bool")), false, false);
        let holds = (holds_signature, vec![equation(&holds_name, None, body)]);

        // The decision the proofs are taken from: the fields' decisions
        // joined as `Decidable.andThen` does, mapped to the record.
        let ctor_name = format!("{ty_name}.{}", ctor.name);
        let whole = if count == 0 {
            apps(var("Std.Decidable.yes"), vec![var(&ctor_name)])
        } else {
            let mut all = decision(count - 1);
            for k in (0..count - 1).rev() {
                all = apps(
                    var("Std.Decidable.andThen"),
                    vec![decision(k), lam(&["%u"], all)],
                );
            }
            // Field `k` of the record, from `%q`, the conjunction of all
            // the fields: `And.left (And.right … %q)`.
            let part = |k: usize| {
                let mut x = var("%q");
                for _ in 0..k {
                    x = apps(var("Std.And.right"), vec![x]);
                }
                if k + 1 < count {
                    x = apps(var("Std.And.left"), vec![x]);
                }
                x
            };
            let build = apps(var(&ctor_name), (0..count).map(part).collect());
            let field = |k: usize| Expr::Field(Box::new(var("%r")), n(&ctor.fields[k].0));
            let mut split = field(count - 1);
            for k in (0..count - 1).rev() {
                split = apps(var("Std.And.Both"), vec![field(k), split]);
            }
            apps(
                var("Std.Decidable.map"),
                vec![all, lam(&["%q"], build), lam(&["%r"], split)],
            )
        };
        let whole = Expr::Ann(
            Box::new(whole),
            Box::new(apps(var("Std.Decidable"), vec![this.clone()])),
            span,
        );
        let sound_signature = signature(
            &sound_name,
            params_pi(Expr::Arrow(
                Box::new(is_true.clone()),
                Box::new(this.clone()),
            )),
            false,
            false,
        );
        let sound = (
            sound_signature,
            vec![equation(
                &sound_name,
                Some("%h"),
                apps(var("Std.Decidable.sound"), vec![whole.clone(), var("%h")]),
            )],
        );
        let complete_signature = signature(
            &complete_name,
            params_pi(Expr::Arrow(
                Box::new(this.clone()),
                Box::new(is_true.clone()),
            )),
            false,
            false,
        );
        let complete = (
            complete_signature,
            vec![equation(
                &complete_name,
                Some("%r"),
                apps(var("Std.Decidable.complete"), vec![whole, var("%r")]),
            )],
        );

        // instance T.%instDecidable : [p : _] -> … -> Std.Decidable (T p …) :=
        //   { holds = T.%holds p …, sound = T.%holdsSound p …, complete = … }
        let own_this = applied(&param);
        let mut ty = apps(var("Std.Decidable"), vec![own_this]);
        for j in (0..np).rev() {
            ty = Expr::Pi {
                names: vec![n(&param(j))],
                implicit: true,
                auto: false,
                dom: Box::new(Expr::Hole(span)),
                cod: Box::new(ty),
                span,
            };
        }
        let by_name = |f: &ast::Name| apps(var(&f.text), (0..np).map(|j| var(&param(j))).collect());
        let instance_name = n(&format!("{ty_name}.%instDecidable"));
        let instance = (
            signature(&instance_name, ty, true, false),
            vec![Decl::Equation {
                guard: None,
                name: instance_name,
                patterns: Vec::new(),
                rhs: Some(record(vec![
                    ("holds", by_name(&holds_name)),
                    ("sound", by_name(&sound_name)),
                    ("complete", by_name(&complete_name)),
                ])),
                arm: None,
                span,
            }],
        );

        // The test's two readings: `T.%holds p … = True ↔ T p …`, and
        // `… = False ↔ ¬T p …` from `Decidable.refute` and `toBoolOfNot`.
        let reads_name = n(&format!("{ty_name}.%holdsReads"));
        let reads_false_name = n(&format!("{ty_name}.%holdsReadsFalse"));
        let iff = |a: Expr, b: Expr| apps(var("Std.Iff"), vec![a, b]);
        let reads = (
            signature(
                &reads_name,
                params_pi(iff(is_true, this.clone())),
                false,
                true,
            ),
            vec![equation(
                &reads_name,
                None,
                record(vec![
                    ("forward", apps(var(&sound_name.text), args())),
                    ("backward", apps(var(&complete_name.text), args())),
                ]),
            )],
        );
        let decided = Expr::Ann(
            Box::new(record(vec![
                ("holds", test),
                ("sound", apps(var(&sound_name.text), args())),
                ("complete", apps(var(&complete_name.text), args())),
            ])),
            Box::new(apps(var("Std.Decidable"), vec![this.clone()])),
            span,
        );
        let refute = apps(
            var("Std.Decidable.refute"),
            vec![decided.clone(), var("%e")],
        );
        let to_bool = apps(var("Std.Decidable.toBoolOfNot"), vec![decided, var("%n")]);
        let reads_false = (
            signature(
                &reads_false_name,
                params_pi(iff(is_false, apps(var("Std.Not"), vec![this]))),
                false,
                true,
            ),
            vec![equation(
                &reads_false_name,
                None,
                record(vec![
                    ("forward", lam(&["%e"], refute)),
                    ("backward", lam(&["%n"], to_bool)),
                ]),
            )],
        );
        DecidableSource {
            holds,
            sound,
            complete,
            instance,
            readings: vec![reads, reads_false],
        }
    }
}

/// What [`Elaborator::decidable_source`] generates, each declaration with
/// its equations, in the order they're defined.
struct DecidableSource {
    holds: (Decl, Vec<Decl>),
    sound: (Decl, Vec<Decl>),
    complete: (Decl, Vec<Decl>),
    instance: (Decl, Vec<Decl>),
    readings: Vec<(Decl, Vec<Decl>)>,
}
