//! A generated extensionality lemma for each record that can have one
//! (SW-263, D503), like Lean's `@[ext]`:
//!
//! ```text
//! type Mod (n: Nat) = { value: Nat, isLt: value < Mod.size n }
//!
//! theorem Mod.ext [n: _] (x: Mod n) (y: Mod n) (valueEq: x.value = y.value): x = y
//! ```
//!
//! Two records are equal when their data fields are: there's a hypothesis
//! `x.f = y.f` for each data field `f`, and the proof fields are left out,
//! as any two proofs of the same equation are equal (`DecEq.uniqueEq`,
//! Hedberg's theorem; there's no definitional proof irrelevance). The proof
//! is the one derived `==` uses (`derive::fields_equal`): each data field's
//! `J`, carrying the proofs along. It's source, elaborated and checked like
//! any theorem, so the kernel checks it.
//!
//! It's generated for a declared record (not an interface, not a
//! proposition, not defined together with other types, without indices)
//! whose fields are
//!
//! - data that doesn't depend on earlier fields (any type, functions too),
//!   or
//! - a proof of an equation `l = r` in a type with a `DecEq` instance that
//!   doesn't mention the record or a type parameter, depending on the
//!   parameters and earlier data fields only.
//!
//! Any other proof field has no such proof (`Or` has two different proofs
//! of one fact), and a data field whose type mentions an earlier field has
//! no `x.f = y.f` to state. Then nothing is generated, nor for the library's
//! own records (its index lists names from source; `Std.Mod` has its own).
//! A module that declares
//! its own `T.ext` keeps it, with no error: the generated one is skipped, as
//! for `DecEq` instances.
//!
//! The names are the field's own (`valueEq`), `x`, `y` and the parameters'.

use stitchwort_core::{DataId, Sort};
use stitchwort_syntax::ast::{self, BinOp, Decl, Expr, Pattern};

use crate::{Elaborator, Result, derive::fields_equal, interfaces};

impl Elaborator {
    /// After record `d` is admitted, and its `DecEq` derived: `T.ext`, if
    /// it can be generated and the module doesn't declare one.
    pub(crate) fn derive_record_ext(&mut self, d: DataId) -> Result<()> {
        let data = self.globals.data(d);
        if self.loading_prelude
            || data.sort == Sort::Prop
            || data.group.len() > 1
            || !data.indices.is_empty()
            || data.ctors.len() != 1
        {
            return Ok(());
        }
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(());
        };
        if self.declares_ext() {
            return Ok(());
        }
        let plan = match self.field_plan_for(d, dec_eq, "an extensionality lemma", false)? {
            Ok(plan) if plan.deciders.iter().all(|x| !x) => plan,
            _ => return Ok(()),
        };
        // `T.%mk%P%k`, the proof fields' types, unless `==` made them.
        for (k, kind) in plan.fields[0].iter().enumerate() {
            if *kind == crate::derive::Field::Proof {
                let ctor = &self.globals.data(d).ctors[0].name;
                let key = Self::member_key(&self.data_key(d), &format!("%{ctor}%P%{k}"));
                if self.scope.get(&key).is_none() {
                    self.derive_proof_type(d, 0, k)?;
                }
            }
        }
        self.clear_metas();
        let (signature, equation) = self.ext_source(d, &plan.fields[0]);
        let result = self.definition(&signature, &[equation]);
        self.clear_metas();
        match result {
            Err(e) if e.code == "E-RESOURCE" => Err(e),
            _ => Ok(()),
        }
    }

    /// Whether the module declares `T.ext` for the item being checked.
    fn declares_ext(&self) -> bool {
        let Some(item) = self.module.item else {
            return false;
        };
        let wanted = format!("{}.ext", self.module.items[item].name);
        self.module.items.iter().any(|i| i.name == wanted)
    }

    /// The signature and the equation of `T.ext`.
    fn ext_source(&self, d: DataId, kinds: &[crate::derive::Field]) -> (Decl, Decl) {
        let data = self.globals.data(d);
        let ty_name = self.relative_to_root(&data.name);
        let span = data.span;
        let n = |text: &str| ast::Name {
            text: text.to_string(),
            span,
        };
        let var = |text: &str| Expr::Var(n(text));
        let eq = |a: Expr, b: Expr| Expr::Binary(BinOp::Eq, Box::new(a), Box::new(b));
        let pi = |x: &str, implicit: bool, dom: Expr, cod: Expr| Expr::Pi {
            names: vec![n(x)],
            implicit,
            auto: false,
            dom: Box::new(dom),
            cod: Box::new(cod),
            span,
        };
        let np = data.params.len();
        let ctor = &data.ctors[0];
        let count = ctor.fields.len();
        let params: Vec<String> = data.params.iter().map(|(x, _)| x.to_string()).collect();
        let mut taken: Vec<String> = params.clone();
        let mut fresh = |base: String| {
            let mut name = base;
            while taken.contains(&name) {
                name.push('\'');
            }
            taken.push(name.clone());
            name
        };
        let (x, y) = (fresh("x".into()), fresh("y".into()));
        let data_fields: Vec<usize> = (0..count)
            .filter(|k| kinds[*k] != crate::derive::Field::Proof)
            .collect();
        let hyps: Vec<(usize, String)> = data_fields
            .iter()
            .map(|&k| (k, fresh(format!("{}Eq", ctor.fields[k].0))))
            .collect();
        let hyp = |k: usize| {
            hyps.iter()
                .find(|(j, _)| *j == k)
                .map(|(_, h)| h.clone())
                .expect("a data field")
        };
        let this = (0..np).fold(var(&ty_name), |f, j| {
            let arg = var(&params[j]);
            let arg = if data.auto_params.get(j) == Some(&true) {
                Expr::NamedArg(n(&params[j]), Box::new(arg), span)
            } else {
                arg
            };
            Expr::App(Box::new(f), Box::new(arg))
        });
        // [p: _] -> … -> (x y : T p…) -> (fEq : x.f = y.f) -> … -> x = y
        let mut ty = eq(var(&x), var(&y));
        for &k in data_fields.iter().rev() {
            let field = n(&ctor.fields[k].0);
            let left = Expr::Field(Box::new(var(&x)), field.clone());
            let right = Expr::Field(Box::new(var(&y)), field);
            ty = pi(&hyp(k), false, eq(left, right), ty);
        }
        ty = Expr::Pi {
            names: vec![n(&x), n(&y)],
            implicit: false,
            auto: false,
            dom: Box::new(this.clone()),
            cod: Box::new(ty),
            span,
        };
        for p in params.iter().rev() {
            ty = pi(p, true, Expr::Hole(span), ty);
        }
        let name = n(&format!("{ty_name}.ext"));
        let signature = Decl::Signature {
            name: name.clone(),
            ty,
            theorem: true,
            export: false,
            synonym: false,
            instance: false,
            span,
        };
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let is_proof: Vec<bool> = kinds
            .iter()
            .map(|k| *k == crate::derive::Field::Proof)
            .collect();
        let proof = fields_equal(
            span,
            &ty_name,
            &ctor.name,
            &is_proof,
            np,
            &this,
            &a,
            &b,
            &|k| var(&hyp(k)),
            &|j| params[j].clone(),
        );
        let ctor_name = format!("{ty_name}.{}", ctor.name);
        let pattern = |f: &dyn Fn(usize) -> String| {
            Pattern::Ctor(
                n(&ctor_name),
                (0..count).map(|k| Pattern::Var(n(&f(k)))).collect(),
                span,
            )
        };
        let mut patterns = vec![pattern(&a), pattern(&b)];
        patterns.extend(data_fields.iter().map(|&k| Pattern::Var(n(&hyp(k)))));
        let equation = Decl::Equation {
            name,
            patterns,
            rhs: Some(proof),
            arm: None,
            span,
        };
        (signature, equation)
    }
}
