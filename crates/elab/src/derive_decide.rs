//! A derived decision procedure for each record of propositions that can
//! have one (SW-1015): a `Prop` record whose fields' propositions are each
//! decided by something `auto` can find gets
//!
//! ```text
//! type Ok (n: Nat): Prop = { small: n < 10, even: n % 2 = 0 }
//!
//! instance Ok.%instDecidable [n: _]: Std.Decidable (Ok n) :=
//!   if %h0: Ok.%%mk%P%0 n then
//!     if %h1: Ok.%%mk%P%1 n %h0 then Std.Decidable.yes (Ok.%mk %h0 %h1)
//!     else Std.Decidable.no (%r => %h1 %r.even)
//!   else Std.Decidable.no (%r => %h0 %r.small)
//! ```
//!
//! so `auto`, `byDecision`, `if h: Ok n` and the counterexample search
//! decide it, as they decide `And`. Each field's proposition is stated
//! through `T.%C%P%k` (its type, the one `==`'s derivation uses), and
//! decided by `if h:`, which finds the decision as any `if h:` does: an
//! instance in this module above the record, or in a namespace it uses.
//! It's source, elaborated and checked like any definition, so the kernel
//! checks it.
//!
//! It's generated for a declared record that is a proposition (not defined
//! together with other types, without indices) whose fields' types don't
//! mention earlier fields: a refutation `%r => %hk %r.f` needs `%r.f` to
//! have the type `%hk` refutes, and with no definitional proof irrelevance
//! `%r`'s earlier fields aren't `%h0 …`. When a field has no decision (a
//! proposition defined by recursion on a variable, say, that nothing
//! decides) nothing is generated, and why is kept for the note when it's
//! wanted (`no_decide`). The core's records (`And`, `Iff`) have theirs
//! written by hand.

use stitchwort_core::value::{eval, force};
use stitchwort_core::{DataId, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Bracket, Decl, Expr};

use crate::check::Ctx;
use crate::{Elaborator, Result};

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
        // `T.%C%P%k`, the fields' types, unless made already.
        let count = fields.len();
        for k in 0..count {
            let ctor = &self.kernel.data(d).ctors()[0].name;
            let key = Self::member_key(&self.data_key(d), &format!("%{ctor}%P%{k}"));
            if self.scope.get(&key).is_none() {
                self.derive_proof_type(d, 0, k)?;
            }
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
        let (signature, equation) = self.decidable_source(d);
        let result = self.definition(&signature, &[equation]);
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

    /// The signature and the equation of `T.%instDecidable`.
    fn decidable_source(&self, d: DataId) -> (Decl, Decl) {
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
        let np = data.params().len();
        let ctor = &data.ctors()[0];
        let count = ctor.fields.len();
        // The parameters' own names, so a note about a field reads as the
        // field's type is written (`no way to decide `Even n``).
        let param = |j: usize| data.params()[j].0.to_string();
        let h = |k: usize| format!("%h{k}");
        // An `auto` parameter is given by name (docs/proposals/interfaces.md
        // §7.5): `T p [ord := q]`.
        let this = apps(
            var(&ty_name),
            (0..np)
                .map(|j| {
                    if data.auto_params().get(j) == Some(&true) {
                        Expr::NamedArg(
                            n(&data.params()[j].0),
                            Box::new(var(&param(j))),
                            span,
                            Bracket::Square,
                        )
                    } else {
                        var(&param(j))
                    }
                })
                .collect(),
        );
        // [p : _] -> … -> Std.Decidable (T p …)
        let mut ty = apps(var("Std.Decidable"), vec![this]);
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
        let name = n(&format!("{ty_name}.%instDecidable"));
        let signature = Decl::Signature {
            name: name.clone(),
            ty,
            theorem: false,
            export: false,
            synonym: false,
            instance: true,
            decreasing: None,
            opaque: false,
            unfolding: Vec::new(),
            defaults: Vec::new(),
            attrs: Vec::new(),
            body_error: None,
            span,
        };
        // Decidable.yes (T.%mk %h0 …), under an `if %hk:` for each field.
        let ctor_name = format!("{ty_name}.{}", ctor.name);
        let helper = format!("{ty_name}.%{}%P%", ctor.name);
        let mut body = apps(
            var("Std.Decidable.yes"),
            vec![apps(
                var(&ctor_name),
                (0..count).map(|k| var(&h(k))).collect(),
            )],
        );
        for k in (0..count).rev() {
            let prop = apps(
                var(&format!("{helper}{k}")),
                (0..np)
                    .map(|j| var(&param(j)))
                    .chain((0..k).map(|j| var(&h(j))))
                    .collect(),
            );
            let field = Expr::Field(Box::new(var("%r")), n(&ctor.fields[k].0));
            let refute = Expr::Lam(
                vec![n("%r")],
                Box::new(Expr::App(Box::new(var(&h(k))), Box::new(field))),
                span,
            );
            body = Expr::If {
                binder: Some(n(&h(k))),
                cond: Box::new(prop),
                then: Box::new(body),
                otherwise: Box::new(apps(var("Std.Decidable.no"), vec![refute])),
                span,
            };
        }
        let equation = Decl::Equation {
            guard: None,
            name,
            patterns: Vec::new(),
            rhs: Some(body),
            arm: None,
            span,
        };
        (signature, equation)
    }
}
