//! A derived `DecEq` instance for data types and records declared in a
//! program: `T.%instDecEq`, made from `T.%decEq`, a proved decision
//! procedure for `=` on `T` (docs/proposals/interfaces.md §5.11, D164,
//! D179). `==`, `!=`, `if h: x = y` and `auto` then find it as any instance.
//! Both are generated as source, naming the library through `Std.` paths,
//! and elaborated like any definition, so the kernel checks them and
//! nothing in the kernel changes.
//!
//! It's derived when `T` is declared, for every type it can be: one with
//! constructors (not a proposition, not defined together with other types,
//! without indices) whose fields are
//!
//! - data that doesn't depend on earlier fields and is either `T` itself,
//!   with the same parameters, or has a `DecEq` instance, given one for each
//!   parameter that's a type; or
//! - a proof of an equation `l = r` in a type with a `DecEq` instance (not
//!   one that mentions `T`: that evidence would depend on the instance being
//!   derived), depending on the parameters and earlier data fields only.
//!   It's left out of the comparison: any two proofs of such an equation
//!   are equal (`DecEq.uniqueEq`, Hedberg's theorem).
//!
//! Parameters may be values (`type Dial (highest: Nat)`): they're head
//! variables of the instance. Each parameter that's a type and that fields
//! use gets a prerequisite, `[auto decEq: DecEq a]`. Otherwise nothing is
//! generated, and why not is kept for the note when `==` is used on `T`.
//! The library's types are skipped: those that need one have one written
//! by hand. So is a type whose module declares its own `DecEq` instance
//! (§5.11: it replaces the derived one), as far as the module's names say
//! before anything is checked.
//!
//! For `type T a = | C1 … | C2 x y | …` it generates
//!
//! - `T.%tag : [a : Type] -> T a -> Nat`, each constructor's position (only
//!   with two constructors or more);
//! - `T.%C2%1 : [a : Type] -> A -> T a -> A` for each data field: that field
//!   of a `C2`, or the first argument for another constructor. With
//!   `Eq.cong`, this gives injectivity: `C2 x y = C2 x' y'` implies
//!   `y = y'`;
//! - `T.%C2%P%k : (a : Type) -> (fields before k) -> Prop` for each proof
//!   field: its type, so the generated source can state it;
//! - and, as source (two constructors or more for `T.%differ`):
//!
//! ```text
//! T.%differ : [a : _] -> (r : T a) -> (s : T a) ->
//!   Nat.equal (T.%tag r) (T.%tag s) = False -> Not (r = s)
//! T.%differ r s t e = Nat.equalFalse (T.%tag r) (T.%tag s) t (Eq.cong T.%tag e)
//!
//! T.%decEq : [a : _] -> [auto decEq: DecEq a] -> (r : T a) -> (s : T a) -> Decidable (r = s)
//! T.%decEq (C2 a0 a1) (C2 b0 b1) =
//!   if h0 : a0 = b0 then
//!     if h1 : a1 = b1 then Yes (J (y q => (C2 a0 a1 : T a) = C2 b0 y) (J … rfl h0) h1)
//!     else No (e => h1 (Eq.cong (T.%C2%1 a1) e))
//!   else No (e => h0 (Eq.cong (T.%C2%0 a0) e))
//! …   -- one equation for each constructor
//! T.%decEq r s = No (T.%differ r s rfl)
//!
//! instance T.%instDecEq : [a : _] -> [auto decEq: DecEq a] -> DecEq (T a) :=
//!   { decide = T.%decEq }
//! ```
//!
//! The last equation covers every pair of different constructors: the case
//! tree checks it once for each, where the tags are two different numbers,
//! so `rfl` proves `Nat.equal` of them is `False`. (That's n² - n checks for
//! n constructors, which is why the proof is in `T.%differ`, checked once.)
//! A field of type `T a` is decided by calling `T.%decEq` on it (structural
//! recursion) through `Decidable.elim`; any other data field with `if h:`,
//! which finds its `DecEq` instance, the dictionaries in scope among the
//! candidates.
//!
//! With proof fields, the proof that equal data gives equal values goes in
//! two steps. First, for any proofs `z` of the proof fields' types (with
//! `a`'s data), `C a… = C a…[z]`: the `J`s above, along `DecEq.uniqueEq`'s
//! equations. Then each data field's `J` carries the claim for all proofs
//! along `h`, its type changing with the field: the motive is
//! `y q => (z: P … y …) -> C a… = C b0 … y a… z`. At the end it's applied
//! to the `b`s' proofs.
//!
//! Generating eagerly, when `T` is declared, is simpler than on first use,
//! which would mean elaborating new definitions in the middle of the one
//! using `==`.
//!
//! Names generated here contain `%`, which source can't write, so they never
//! clash with the user's.

use std::rc::Rc;

use crate::kernel;
use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{eval, force, quote, unused};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, interfaces};

/// How `==` (or a derived `Ord`) treats one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Field {
    /// It's `T` again: a recursive call.
    Recursive,
    /// Its type has an instance of the interface: `DecEq`, which
    /// `if h : x = y` finds, or `Ord`.
    Decided,
    /// A proof of an equation in a type with a `DecEq` instance: not
    /// compared.
    Proof,
}

/// What a derived `==` (or `Ord`) for a data type is made from.
pub(crate) struct Plan {
    /// Which parameters (types) take a dictionary: those fields use.
    pub(crate) deciders: Vec<bool>,
    /// For each constructor, each field's.
    pub(crate) fields: Vec<Vec<Field>>,
}

impl Elaborator {
    /// After data type or record `d` is admitted: its `DecEq` instance, if
    /// one can be derived, or else why not.
    pub(crate) fn derive_data_eq(&mut self, d: DataId) -> Result<()> {
        // Nor for a type the compiler declared, whose constructors' names
        // source can't write: an ability's operations (`effects.rs`).
        let data = self.globals.data(d);
        let generated = !data.record && data.ctors.iter().any(|c| c.name.starts_with('%'));
        if self.loading_prelude || generated || interfaces::dec_eq(self).is_none() {
            return Ok(());
        }
        if self.declares_dec_eq() {
            return Ok(());
        }
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(());
        };
        let plan = match self.field_plan(d, dec_eq, "`==`")? {
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
            for (k, field) in plan.fields[c].iter().enumerate() {
                match field {
                    Field::Proof => self.derive_proof_type(d, c, k)?,
                    _ => self.derive_field(d, c, k)?,
                }
            }
        }
        self.clear_metas();
        let source = self.eq_source(d, &plan);
        let mut result = match source.differ {
            Some((signature, equation)) => self.definition(&signature, &[equation]),
            None => Ok(()),
        };
        for (signature, equations) in [source.dec_eq, source.instance] {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&signature, &equations));
        }
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

    /// Whether the module item being checked (a data type) has a `DecEq`
    /// instance declared by its module, by the names in the module's
    /// instance declarations (§5.11).
    fn declares_dec_eq(&self) -> bool {
        let (Some(item), Some(dec_eq)) = (self.module.item, interfaces::dec_eq(self)) else {
            return false;
        };
        self.module.items.iter().any(|i| {
            i.instance
                && i.interface == Some(Global::Data(dec_eq))
                && i.head == Some(Global::Unchecked(item))
        })
    }

    /// Whether `==` can be derived for `d`, and how; or why not. The same
    /// for a derived `Ord` (`derive_ord.rs`), with `interface` the one whose
    /// instances data fields need (proof fields always need `DecEq`), and
    /// `label` what the notes call it.
    pub(crate) fn field_plan(
        &mut self,
        d: DataId,
        interface: DataId,
        label: &str,
    ) -> Result<std::result::Result<Plan, String>> {
        let g = &self.globals;
        let data = g.data(d);
        let name = data.name.to_string();
        let np = data.params.len();
        if data.group.len() > 1 {
            return Ok(Err(format!(
                "`{name}` is defined together with other types, which {label} isn't derived for yet"
            )));
        }
        if data.sort == Sort::Prop {
            return Ok(Err(format!("`{name}` is a proposition")));
        }
        if !data.indices.is_empty() {
            return Ok(Err(format!(
                "`{name}` has indices, which {label} isn't derived for yet"
            )));
        }
        if data.ctors.is_empty() {
            return Ok(Err(format!("`{name}` has no constructors")));
        }
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = data.params.iter().map(|(_, t)| is_type(t)).collect();
        // Each field, classified; the types to find instances for are
        // checked below.
        let mut deciders = vec![false; np];
        let mut fields = Vec::new();
        // Each with whether it's a proof field's carrier (needing `DecEq`).
        let mut to_decide: Vec<(Value, String, bool)> = Vec::new();
        for ctor in &data.ctors {
            let mut kinds: Vec<Field> = Vec::new();
            for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                let what = format!("the field `{field}` of `{}`", ctor.name);
                let what = if data.record {
                    format!("its field `{field}`")
                } else {
                    what
                };
                // The parameters mentioned, at levels `0..np` of a term
                // under `i` fields.
                let mentioned = |t: &Term, under: usize| -> Vec<usize> {
                    (0..np).filter(|j| t.mentions(under + np - 1 - j)).collect()
                };
                if ctor.field_erased[i] {
                    if ctor.field_sorts[i] != Sort::Prop {
                        return Ok(Err(format!(
                            "{what} is a type, which {label} can't compare"
                        )));
                    }
                    if (0..i).any(|j| kinds[j] == Field::Proof && ty.mentions(i - 1 - j)) {
                        return Ok(Err(format!(
                            "the type of {what} mentions an earlier proof field, which {label} \
                             isn't derived for yet"
                        )));
                    }
                    // The field's type with the parameters and the fields
                    // before it as variables.
                    let env: Vec<Value> = (0..np + i).map(Value::var).collect();
                    let value = force(g, eval(g, &env, ty)?)?;
                    let Value::Eq(carrier, _, _) = value else {
                        return Ok(Err(format!(
                            "{what} is a proof of something other than an equation, and two \
                             values equal in their data can still differ there"
                        )));
                    };
                    let carrier_term = quote(g, np + i, &carrier)?;
                    if carrier_term
                        .subterms()
                        .any(|(t, _)| matches!(t, Term::Data(e, _) if *e == d))
                    {
                        return Ok(Err(format!(
                            "{what} is an equation in a type that mentions `{name}`, and \
                             telling its proofs apart would need `==` on `{name}` itself"
                        )));
                    }
                    if (0..i).any(|j| carrier_term.mentions(j)) {
                        return Ok(Err(format!(
                            "{what} is an equation in a type that depends on other fields, \
                             which {label} isn't derived for yet"
                        )));
                    }
                    for j in mentioned(&carrier_term, i) {
                        deciders[j] |= param_is_type[j];
                    }
                    to_decide.push(((*carrier).clone(), what, true));
                    kinds.push(Field::Proof);
                    continue;
                }
                if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                    return Ok(Err(format!(
                        "the type of {what} depends on an earlier field, which {label} isn't \
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
                        "{what} contains `{name}` inside another type, which {label} isn't \
                         derived for yet"
                    )));
                }
                for j in mentioned(ty, i) {
                    deciders[j] |= param_is_type[j];
                }
                kinds.push(Field::Decided);
                to_decide.push((value, what, false));
            }
            fields.push(kinds);
        }
        // Every type to decide needs an instance, given one for each
        // parameter that's a type.
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(Err("there's no prelude".into()));
        };
        let interface_name = |e: &Self, i: DataId| e.globals.data(i).name.to_string();
        let names = (
            interface_name(self, interface),
            interface_name(self, dec_eq),
        );
        self.clear_metas();
        let span = self.globals.data(d).span;
        let params: Vec<(Name, Term)> = self.globals.data(d).params.clone();
        let mut why = None;
        {
            let mut cx = Ctx::new(self, span);
            for (x, ty) in &params {
                let ty = cx.eval(ty)?;
                cx.bind_hidden(x.clone(), ty);
            }
            for (j, is_type) in param_is_type.iter().enumerate() {
                if *is_type {
                    cx.bind_hidden(
                        format!("%dict{j}").as_str().into(),
                        Value::Data(interface, vec![Value::var(j)]),
                    );
                }
            }
            for (ty, what, carrier) in to_decide {
                let (needed, needed_name) = if carrier {
                    (dec_eq, &names.1)
                } else {
                    (interface, &names.0)
                };
                let goal = Value::Data(needed, vec![ty.clone()]);
                if let Some(e) = interfaces::findable(&mut cx, &goal)? {
                    let mut reason = format!(
                        "{what} has type `{}`, which has no `{needed_name}` instance (when \
                         `{name}` was declared)",
                        cx.show(&ty)
                    );
                    if e.code != "E-INSTANCE-NONE" {
                        reason = format!("{reason}: {}", e.message);
                    }
                    why = Some(reason);
                    break;
                }
            }
        }
        self.clear_metas();
        Ok(match why {
            Some(why) => Err(why),
            None => Ok(Plan { deciders, fields }),
        })
    }

    /// Declares `T.%tag : [params] -> T params -> Nat`.
    pub(crate) fn derive_tag(&mut self, d: DataId) -> Result<()> {
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
                body: Some(Rc::new(Term::Nat(Rc::new(BigUint::from(c))))),
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
                    body: Some(Rc::new(body)),
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

    /// Declares `T.%C%P%k : (params) -> (fields before k) -> Prop`, the type
    /// of proof field `k` of `C`, all its arguments explicit.
    pub(crate) fn derive_proof_type(&mut self, d: DataId, c: usize, k: usize) -> Result<()> {
        let data = self.globals.data(d);
        let ctor = &data.ctors[c];
        let binders: Vec<(Name, Term)> = data
            .params
            .iter()
            .chain(&ctor.fields[..k])
            .cloned()
            .collect();
        let mut ty = Term::Sort(Sort::Prop);
        let mut body = ctor.fields[k].1.clone();
        for (x, t) in binders.iter().rev() {
            ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(t.clone()), Rc::new(ty));
            body = Term::Lam(x.clone(), Icit::Explicit, Rc::new(body));
        }
        let member = format!("%{}%P%{k}", ctor.name);
        let name: Name = format!("{}.{member}", data.name).into();
        let span = data.span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        let key = Self::member_key(&self.data_key(d), &member);
        self.scope.insert(&key, Global::Def(id), span, false);
        Ok(())
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

    /// The source of `T.%differ` (with two constructors or more), of
    /// `T.%decEq` and of `T.%instDecEq`.
    fn eq_source(&self, d: DataId, plan: &Plan) -> Source {
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
        let pi = |x: &str, implicit: bool, auto: bool, dom: Expr, cod: Expr| Expr::Pi {
            names: vec![n(x)],
            implicit,
            auto,
            dom: Box::new(dom),
            cod: Box::new(cod),
            span,
        };
        let signature = |name: &ast::Name, ty: Expr, instance: bool| Decl::Signature {
            name: name.clone(),
            ty,
            theorem: false,
            export: false,
            synonym: false,
            instance,
            span,
        };
        let decidable = |p: Expr| apps(var("Std.Decidable"), vec![p]);
        let np = data.params.len();
        let param = |j: usize| format!("%p{j}");
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let h = |k: usize| format!("%h{k}");
        let dec_eq = format!("{ty_name}.%decEq");
        let deciders: Vec<usize> = (0..np).filter(|j| plan.deciders[*j]).collect();
        // The dictionaries' names: `decEq`, or one per parameter after it
        // (`decEqA` for `a`) when there are several.
        let dict = |j: usize| {
            if deciders.len() == 1 {
                "decEq".to_string()
            } else {
                let p = data.params[j].0.to_string();
                let mut chars = p.chars();
                match chars.next() {
                    Some(c) => format!("decEq{}{}", c.to_uppercase(), chars.as_str()),
                    None => format!("decEq{j}"),
                }
            }
        };
        // [%p0 : _] -> … -> [auto decEq : Std.DecEq %p0] -> … -> rest
        let with_params = |rest: Expr, dicts: bool| {
            let mut ty = rest;
            if dicts {
                for &j in deciders.iter().rev() {
                    let dom = apps(var("Std.DecEq"), vec![var(&param(j))]);
                    ty = pi(&dict(j), true, true, dom, ty);
                }
            }
            for j in (0..np).rev() {
                ty = pi(&param(j), true, false, Expr::Hole(span), ty);
            }
            ty
        };
        // An `auto` parameter is given by name (docs/proposals/interfaces.md
        // §7.5): `T %p0 [ord := %p1]`.
        let this = apps(
            var(&ty_name),
            (0..np)
                .map(|j| {
                    if data.auto_params.get(j) == Some(&true) {
                        Expr::NamedArg(n(&data.params[j].0), Box::new(var(&param(j))), span)
                    } else {
                        var(&param(j))
                    }
                })
                .collect(),
        );

        // T.%decEq : … -> (%r %s : T %p0 …) -> Decidable (%r = %s)
        let ty = with_params(
            Expr::Pi {
                names: vec![n("%r"), n("%s")],
                implicit: false,
                auto: false,
                dom: Box::new(this.clone()),
                cod: Box::new(decidable(eq(var("%r"), var("%s")))),
                span,
            },
            true,
        );
        let name = n(&dec_eq);
        let dec_eq_signature = signature(&name, ty, false);

        let mut equations = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let ctor_name = format!("{ty_name}.{}", ctor.name);
            let kinds = &plan.fields[c];
            let count = ctor.fields.len();
            let pattern = |f: &dyn Fn(usize) -> String| {
                Pattern::Ctor(
                    n(&ctor_name),
                    (0..count).map(|k| Pattern::Var(n(&f(k)))).collect(),
                    span,
                )
            };
            let data_fields: Vec<usize> =
                (0..count).filter(|k| kinds[*k] != Field::Proof).collect();
            let is_proof: Vec<bool> = kinds.iter().map(|k| *k == Field::Proof).collect();
            let proof = fields_equal(
                span,
                &ty_name,
                &ctor.name,
                &is_proof,
                np,
                &this,
                &a,
                &b,
                &|k| var(&h(k)),
            );
            let mut body = apps(var("Std.Decidable.Yes"), vec![proof]);
            for &k in data_fields.iter().rev() {
                let field = format!("{ty_name}.%{}%{k}", ctor.name);
                let cong = apps(
                    var("Std.Eq.cong"),
                    vec![apps(var(&field), vec![var(&a(k))]), var("%e")],
                );
                let refute = lam(&["%e"], apps(var(&h(k)), vec![cong]));
                let no = apps(var("Std.Decidable.No"), vec![refute]);
                body = match kinds[k] {
                    Field::Recursive => apps(
                        var("Std.Decidable.elim"),
                        vec![
                            apps(var(&dec_eq), vec![var(&a(k)), var(&b(k))]),
                            lam(&[&h(k)], body),
                            lam(&[&h(k)], no),
                        ],
                    ),
                    _ => Expr::If {
                        binder: Some(n(&h(k))),
                        cond: Box::new(eq(var(&a(k)), var(&b(k)))),
                        then: Box::new(body),
                        otherwise: Box::new(no),
                        span,
                    },
                };
            }
            equations.push(Decl::Equation {
                name: name.clone(),
                patterns: vec![pattern(&a), pattern(&b)],
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
            // T.%differ : [%p0 : _] -> … -> (%r %s : T %p0 …) ->
            //   Nat.equal (T.%tag %r) (T.%tag %s) = False -> Not (%r = %s)
            // T.%differ %r %s %t %e = Nat.equalFalse (T.%tag %r) (T.%tag %s) %t (Eq.cong T.%tag %e)
            let tag = format!("{ty_name}.%tag");
            let tag_of = |x: &str| apps(var(&tag), vec![var(x)]);
            let differ_name = n(&format!("{ty_name}.%differ"));
            let unequal = eq(
                apps(var("Std.Nat.equal"), vec![tag_of("%r"), tag_of("%s")]),
                var("Std.Bool.False"),
            );
            let ty = with_params(
                Expr::Pi {
                    names: vec![n("%r"), n("%s")],
                    implicit: false,
                    auto: false,
                    dom: Box::new(this.clone()),
                    cod: Box::new(Expr::Arrow(
                        Box::new(unequal),
                        Box::new(apps(var("Std.Not"), vec![eq(var("%r"), var("%s"))])),
                    )),
                    span,
                },
                false,
            );
            let cong = apps(var("Std.Eq.cong"), vec![var(&tag), var("%e")]);
            let rhs = apps(
                var("Std.Nat.equalFalse"),
                vec![tag_of("%r"), tag_of("%s"), var("%t"), cong],
            );
            differ = Some((
                signature(&differ_name, ty, false),
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
            equations.push(Decl::Equation {
                name: name.clone(),
                patterns: vec![Pattern::Var(n("%r")), Pattern::Var(n("%s"))],
                rhs: Some(apps(var("Std.Decidable.No"), vec![refute])),
                arm: None,
                span,
            });
        }
        // instance T.%instDecEq : … -> Std.DecEq (T %p0 …) := { decide = T.%decEq }
        let instance_name = n(&format!("{ty_name}.%instDecEq"));
        let instance_ty = with_params(apps(var("Std.DecEq"), vec![this.clone()]), true);
        let instance = (
            signature(&instance_name, instance_ty, true),
            vec![Decl::Equation {
                name: instance_name,
                patterns: Vec::new(),
                rhs: Some(Expr::Record {
                    base: None,
                    fields: vec![(n("decide"), var(&dec_eq))],
                    span,
                }),
                arm: None,
                span,
            }],
        );
        Source {
            differ,
            dec_eq: (dec_eq_signature, equations),
            instance,
        }
    }
}

/// A proof of `(C %a0 … : this) = C %b0 …` for constructor `ctor` of the
/// type named `ty_name` (as source names it), given `h(k): %ak = %bk` for
/// each data field; `is_proof` says which fields are proofs, and
/// `T.%C%P%k` must be declared for each. First, for proofs `%z…` of the
/// proof fields' types: `C %a… = C %a…[%z…]`, along `DecEq.uniqueEq`'s
/// equations. Then each data field's `J`, the claim for all proofs carried
/// along: `y q => (%z: P …) -> C %a… = C %b… y %a… %z…`; at the end it's
/// applied to the `%b`s' proofs. Shared by derived `DecEq` and `Ord`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fields_equal(
    span: Span,
    ty_name: &str,
    ctor: &str,
    is_proof: &[bool],
    np: usize,
    this: &Expr,
    a: &dyn Fn(usize) -> String,
    b: &dyn Fn(usize) -> String,
    h: &dyn Fn(usize) -> Expr,
) -> Expr {
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
    let pi = |x: &str, dom: Expr, cod: Expr| Expr::Pi {
        names: vec![n(x)],
        implicit: false,
        auto: false,
        dom: Box::new(dom),
        cod: Box::new(cod),
        span,
    };
    let param = |j: usize| format!("%p{j}");
    let z = |k: usize| format!("%z{k}");
    let count = is_proof.len();
    let ctor_name = format!("{ty_name}.{ctor}");
    let proofs: Vec<usize> = (0..count).filter(|k| is_proof[*k]).collect();
    let data_fields: Vec<usize> = (0..count).filter(|k| !is_proof[*k]).collect();
    // `C x0 … xn`, the left side annotated for the parameters the fields
    // don't determine.
    let built =
        |field: &dyn Fn(usize) -> Expr| apps(var(&ctor_name), (0..count).map(field).collect());
    let left = Expr::Ann(
        Box::new(built(&|j| var(&a(j)))),
        Box::new(this.clone()),
        span,
    );
    // A proof field's type, from the fields before it.
    let proof_type = |k: usize, field: &dyn Fn(usize) -> Expr| {
        let helper = format!("{ty_name}.%{ctor}%P%{k}");
        let mut args: Vec<Expr> = (0..np).map(|j| var(&param(j))).collect();
        args.extend((0..k).map(field));
        apps(var(&helper), args)
    };
    let mut proof = var("rfl");
    for (i, &p) in proofs.iter().enumerate() {
        let right = built(&|j| {
            if is_proof[j] {
                match proofs.iter().position(|q| *q == j) {
                    Some(at) if at < i => var(&z(j)),
                    Some(at) if at == i => var("%w"),
                    _ => var(&a(j)),
                }
            } else {
                var(&a(j))
            }
        });
        let motive = lam(&["%w", "%e"], eq(left.clone(), right));
        let unique = apps(var("Std.DecEq.uniqueEq"), vec![var(&a(p)), var(&z(p))]);
        proof = apps(var("J"), vec![motive, proof, unique]);
    }
    if !proofs.is_empty() {
        let names: Vec<String> = proofs.iter().map(|p| z(*p)).collect();
        let names: Vec<&str> = names.iter().map(String::as_str).collect();
        proof = lam(&names, proof);
    }
    for (i, &k) in data_fields.iter().enumerate() {
        let value = |j: usize| -> Expr {
            if is_proof[j] {
                var(&z(j))
            } else {
                match data_fields.iter().position(|q| *q == j) {
                    Some(at) if at < i => var(&b(j)),
                    Some(at) if at == i => var("%y"),
                    _ => var(&a(j)),
                }
            }
        };
        let mut claim = eq(left.clone(), built(&value));
        for &p in proofs.iter().rev() {
            claim = pi(&z(p), proof_type(p, &value), claim);
        }
        let motive = lam(&["%y", "%q"], claim);
        proof = apps(var("J"), vec![motive, proof, h(k)]);
    }
    if !proofs.is_empty() {
        // `J` takes exactly three arguments, so the claim for all proofs is
        // annotated, then applied to the `b`s' proofs.
        let value = |j: usize| -> Expr { if is_proof[j] { var(&z(j)) } else { var(&b(j)) } };
        let mut claim = eq(left.clone(), built(&value));
        for &p in proofs.iter().rev() {
            claim = pi(&z(p), proof_type(p, &value), claim);
        }
        proof = Expr::Ann(Box::new(proof), Box::new(claim), span);
        proof = apps(proof, proofs.iter().map(|p| var(&b(*p))).collect());
    }
    proof
}

/// The source [`Elaborator::eq_source`] generates.
struct Source {
    differ: Option<(Decl, Decl)>,
    dec_eq: (Decl, Vec<Decl>),
    instance: (Decl, Vec<Decl>),
}
