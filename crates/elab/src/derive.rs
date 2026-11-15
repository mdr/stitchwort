//! A derived `DecEq` instance for data types and records declared in a
//! program: `T.%instDecEq`, made from `T.%same`, a `Bool` test of equality
//! on `T`, and proofs that it is right (docs/proposals/interfaces.md §5.11, D164,
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
//!   with the same parameters, or `T` inside `List`, `Option` and pairs (a
//!   nested type, below), or has a `DecEq` instance, given one for each
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
//! - with two constructors or more, `T.%C2%k%at`, `T.%view`, `T.%eta` and
//!   `T.%etaAt` ([`Elaborator::derive_rebuild`]): field `k` of a value known
//!   to be a `C2`, and the proof that a value whose tag is a number `c` is
//!   constructor `c` of those fields;
//! - and, as source:
//!
//! ```text
//! T.%same : [a : _] -> [auto decEq: DecEq a] -> (r : T a) -> (s : T a) -> Bool
//! T.%same C1 s = Nat.equal 0 (T.%tag s)   -- a constructor without data fields
//! T.%same (C2 a0 a1) s = Nat.equal 1 (T.%tag s) &&
//!   (DecEq.decide a0 (T.%C2%0 a0 s)).holds && (DecEq.decide a1 (T.%C2%1 a1 s)).holds
//! …   -- one equation for each constructor
//!
//! T.%sameSound : … -> (r : T a) -> (s : T a) -> T.%same r s = True -> r = s
//! T.%sameSound (C2 a0 a1) s h =
//!   let e : T.%tag s = 1 := Eq.sym (DecEq.tagsSame 1 (T.%tag s) h)
//!   let b0 := T.%C2%0%at s e; let b1 := T.%C2%1%at s e
//!   let v : (DecEq.decide a0 b0).holds && (DecEq.decide a1 b1).holds = True :=
//!     J (y q => T.%same (C2 a0 a1) y = True) h (Eq.sym (T.%etaAt s 1 e))
//!   Eq.trans (Decidable.sound (… : Decidable (C2 a0 a1 = C2 b0 b1)) v) (T.%etaAt s 1 e)
//!
//! T.%sameComplete : … -> (r : T a) -> (s : T a) -> r = s -> T.%same r s = True
//! T.%sameComplete (C2 a0 a1) s e =
//!   J (y q => T.%same (C2 a0 a1) y = True) (Decidable.complete (… : Decidable (C2 a0 a1 = C2 a0 a1)) rfl) e
//!
//! T.%decide : … -> (r : T a) -> (s : T a) -> Decidable (r = s)
//! T.%decide r s = { holds = T.%same r s, sound = T.%sameSound r s, complete = T.%sameComplete r s }
//!
//! instance T.%instDecEq : [a : _] -> [auto decEq: DecEq a] -> DecEq (T a) :=
//!   { decide = T.%decide }
//! ```
//!
//! The test comes first, as in a hand-written instance (docs/proposals/
//! decidable-record.md §5.3): `r == s` is `(T.%decide r s).holds`, so
//! `T.%same r s`, which on two constructors computes to their fields'
//! tests joined by `&&`, the later
//! ones run only once the earlier ones hold: `({ x = a, y = c }: Point) ==
//! { x = b, y = d }` is `a == b && c == d` by `rfl`. A field of type `T a`
//! is tested by `T.%same` on it (structural recursion); any other data
//! field by the `holds` of `DecEq.decide`, which finds its instance, the
//! dictionaries in scope among the candidates. The proofs are erased, so a
//! run builds none of them.
//!
//! The proofs state each constructor's decision once, from `Decidable.map`
//! and `andThen` over the fields' decisions (a field of type `T a` has one
//! made of `T.%same` and the proofs), so that its `holds` is exactly the
//! test, and take its `sound` and `complete`. With one constructor both
//! values are matched (`T.%same (C a0 a1) (C b0 b1)`). With more, only the
//! first is, and the second's fields are read by projection, once the tags
//! agree: `T.%etaAt s c e` turns `s`, whose tag is `c`, into the constructor
//! `c` of its fields, so each equation's proof is about two values of one
//! constructor. Matching both values would make a case tree of n² leaves
//! for n constructors, each checked; this is n leaves (docs/proposals/
//! derived-equality.md §5.6). `T.%sameSound` and `T.%sameComplete` are
//! defined after `T.%same` and together, since their types mention it.
//!
//! With proof fields, the proof that equal data gives equal values goes in
//! two steps. First, for any proofs `z` of the proof fields' types (with
//! `a`'s data), `C a… = C a…[z]`: the `J`s above, along `DecEq.uniqueEq`'s
//! equations. Then each data field's `J` carries the claim for all proofs
//! along `h`, its type changing with the field: the motive is
//! `y q => (z: P … y …) -> C a… = C b0 … y a… z`. At the end it's applied
//! to the `b`s' proofs.
//!
//! A nested type (docs/proposals/nested-data-types.md §10, stage 2), `type
//! Packet = | Number (value: Nat) | Packets (items: List Packet)`, can't
//! pass `T.%same` to `List`'s instance: termination refuses an unsaturated
//! recursive function, as it refuses `map`. Instead each container `T` is
//! in, found by [`Elaborator::members`] (`List Packet`; for `List (List
//! T)` both lists; for `Option (T, Nat)` the option and the pair), is a
//! *member*, numbered from 1, with the same generated functions under
//! `T.%m1%`: `T.%m1%type` (its type, so source can name it),
//! `T.%m1%tag`, `T.%m1%Cons%0`, `T.%m1%view`, `T.%m1%same` and its two
//! proofs, made as
//! for a data type whose fields are its constructors' with the container's
//! arguments: `T.%m1%same (Cons a0 a1) (Cons b0 b1)` tests `a0` by
//! `T.%same` and `a1` by itself. The `same`s are defined together (so are
//! the proofs), and
//! every call is on a part of an argument. Only `List`, `Option` and `Pair`
//! are looked into; `T` inside another type (`Vec`, a type of the program,
//! an earlier group) gets the note naming it. A container's equality is
//! structural like its own instance's, and its `Ord` (`derive_ord.rs`),
//! constructors then fields, is the order of `List`'s, `Option`'s and
//! `Pair`'s own instances.
//!
//! Generating eagerly, when `T` is declared, is simpler than on first use,
//! which would mean elaborating new definitions in the middle of the one
//! using `==`.
//!
//! Names generated here contain `%`, which source can't write, so they never
//! clash with the user's.

use std::rc::Rc;
use stitchwort_core::Ev;

use crate::kernel;
use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{eval, force, quote, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Bracket, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, interfaces};

/// How `==` (or a derived `Ord`) treats one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Field {
    /// It's `T` again (member 0), or a container of `T` the derivers know
    /// (member `m`, [`Plan::nested`]`[m - 1]`): a call to that member's
    /// function, defined together with `T`'s.
    Recursive(usize),
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
    /// For each container `T` is nested in (members 1 and on), each of its
    /// constructors' fields.
    pub(crate) nested: Vec<Nested>,
}

impl Plan {
    /// Member `m`'s fields: `T`'s for 0, else its container's.
    pub(crate) fn member_fields(&self, m: usize) -> &[Vec<Field>] {
        if m == 0 {
            &self.fields
        } else {
            &self.nested[m - 1].fields
        }
    }
}

/// A container a nested type is in, as the derivers see it: `List Packet`
/// in `type Packet = … | Packets (items: List Packet)`.
pub(crate) struct Nested {
    /// `List`, `Option` or `Pair`, with its arguments.
    pub(crate) member: Member,
    /// For each of its constructors, each field's.
    pub(crate) fields: Vec<Vec<Field>>,
}

/// A type a derived instance has a function for: `T` itself (member 0), or
/// a container of `T` that one of `T`'s fields, or another member's, has as
/// its type (`List Packet`, `List (List Packet)`, `Option (Packet, Nat)`
/// and the pair in it). Each member after `T` gets its own function, defined
/// together with `T`'s, so that every call is on a part of the argument:
/// passing `T`'s function to `List`'s instance would be refused as `map` is.
pub(crate) struct Member {
    /// `T`, or `List`, `Option` or `Pair`.
    pub(crate) data: DataId,
    /// Its arguments, with `T`'s parameters as the variables `0..np`.
    pub(crate) args: Vec<Value>,
    /// For a container, the field of `T` it's in, as notes name it (`the
    /// field `items` of `Packets``).
    pub(crate) origin: String,
}

/// Which of `members` has type `ty` (with `T`'s parameters as the
/// variables `0..np`), if any.
pub(crate) fn member_of(
    g: &Ev,
    np: usize,
    members: &[Member],
    ty: &Value,
) -> Result<Option<usize>> {
    for (m, member) in members.iter().enumerate() {
        if stitchwort_core::value::conv(g, np, ty, &member.ty())? {
            return Ok(Some(m));
        }
    }
    Ok(None)
}

impl Member {
    /// Its type, with `T`'s parameters as the variables `0..np`.
    pub(crate) fn ty(&self) -> Value {
        Value::Data(self.data, self.args.clone().into())
    }
}

/// The source-name prefix of member `m`'s generated names in `T`'s
/// namespace: `T.%` for `T` itself (`T.%same`, `T.%tag`), `T.%m1%` for the
/// first container (`T.%m1%same`, `T.%m1%tag`, `T.%m1%Cons%0`).
pub(crate) fn member_prefix(ty_name: &str, m: usize) -> String {
    if m == 0 {
        format!("{ty_name}.%")
    } else {
        format!("{ty_name}.%m{m}%")
    }
}

/// The containers the derivers look into.
fn known_container(g: &Ev, e: DataId) -> bool {
    [Builtin::List, Builtin::Option, Builtin::Pair]
        .iter()
        .any(|b| g.env.registry().data(*b) == Some(e))
}

impl Elaborator {
    /// After data type or record `d` is admitted: its `DecEq` instance, if
    /// one can be derived, or else why not.
    pub(crate) fn derive_data_eq(&mut self, d: DataId) -> Result<()> {
        // Nor for a type the compiler declared, whose constructors' names
        // source can't write: an ability's operations (`effects.rs`).
        let data = self.kernel.data(d);
        let generated = !data.record() && data.ctors().iter().any(|c| c.name.starts_with('%'));
        if self.unit.loading_prelude || generated || interfaces::dec_eq(self).is_none() {
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
                self.tables.no_eq.insert(&self.session.owners, d, why);
                return Ok(());
            }
        };
        let ctors = self.kernel.data(d).ctors().len();
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
        for (m, nested) in plan.nested.iter().enumerate() {
            self.derive_member_helpers(d, m + 1, &nested.member, true)?;
        }
        self.clear_metas();
        let source = self.eq_source(d, &plan);
        let mut result = self.derive_rebuild(d, &plan);
        self.clear_metas();
        result = result.and_then(|()| self.definitions(&source.tests));
        self.clear_metas();
        result = result.and_then(|()| self.definitions(&source.proofs));
        let (signature, equations) = source.decide;
        self.clear_metas();
        result = result.and_then(|()| self.definition(&signature, &equations));
        let (signature, equations) = source.instance;
        self.clear_metas();
        result = result.and_then(|()| self.definition(&signature, &equations));
        for (signature, equations) in source.readings {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&signature, &equations));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if e.code == "E-RESOURCE" => return Err(e),
            Err(e) => {
                self.tables.no_eq.insert(
                    &self.session.owners,
                    d,
                    format!("deriving it failed: {}", e.message),
                );
            }
        }
        Ok(())
    }

    /// `T` (member 0) and the containers of it that its fields have as
    /// types, and theirs, in the order they're found (constructors, then
    /// fields, then the next member's); or why not: `T` inside a container
    /// the derivers don't know (a `Vec`, a type of the program, an earlier
    /// group), named, with `label` what the note calls the derivation.
    /// Fields the plans refuse anyway (proofs, types, functions, a type
    /// that depends on an earlier field) are passed over. Every deriver
    /// finds the same members, in the same order, so `T.%m1%type` means one
    /// thing.
    pub(crate) fn members(
        &self,
        d: DataId,
        label: &str,
    ) -> Result<std::result::Result<Vec<Member>, String>> {
        let g = &self.ev();
        let data = g.data(d);
        let name = data.name().to_string();
        let np = data.params().len();
        let mut members = vec![Member {
            data: d,
            args: (0..np).map(Value::var).collect(),
            origin: String::new(),
        }];
        let mut next = 0;
        while next < members.len() {
            let here = &members[next];
            let (container, args) = (here.data, here.args.clone());
            for ctor in g.data(container).ctors() {
                for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                    if ctor.field_erased[i] || (0..i).any(|j| ty.mentions(i - 1 - j)) {
                        continue;
                    }
                    let env: Vec<Value> = args
                        .iter()
                        .cloned()
                        .chain((0..i).map(|_| unused()))
                        .collect();
                    let value = force(g, eval(g, &env, ty)?)?;
                    if matches!(value, Value::Pi(..)) {
                        continue;
                    }
                    let term = quote(g, np, &value)?;
                    if !term
                        .subterms()
                        .any(|(t, _)| matches!(t, Term::Data(e, _) if *e == d))
                    {
                        continue;
                    }
                    if member_of(g, np, &members, &value)?.is_some() {
                        continue;
                    }
                    let what = if next > 0 {
                        members[next].origin.clone()
                    } else if data.record() {
                        format!("its field `{field}`")
                    } else {
                        format!("the field `{field}` of `{}`", ctor.name)
                    };
                    match &value {
                        Value::Data(e, args) if known_container(g, *e) => {
                            members.push(Member {
                                data: *e,
                                args: args.to_vec(),
                                origin: what,
                            });
                        }
                        other => {
                            let inside = match other {
                                Value::Data(e, _) => format!("`{}`", g.data(*e).name()),
                                _ => "another type".to_string(),
                            };
                            return Ok(Err(format!(
                                "{what} contains `{name}` inside {inside}, and {label} is \
                                 derived for a type inside `List`, `Option` and pairs only"
                            )));
                        }
                    }
                }
            }
            next += 1;
        }
        Ok(Ok(members))
    }

    /// Whether the module item being checked (a data type) has a `DecEq`
    /// instance declared by its module, by the names in the module's
    /// instance declarations (§5.11).
    fn declares_dec_eq(&self) -> bool {
        let (Some(item), Some(dec_eq)) = (self.unit.module.item, interfaces::dec_eq(self)) else {
            return false;
        };
        self.unit.module.items.iter().any(|i| {
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
        self.field_plan_for(d, interface, label, true)
    }

    /// [`Self::field_plan`], where `compare` says whether data fields are
    /// compared (needing instances, and not functions). The generated
    /// extensionality lemma (`derive_ext.rs`) only states `x.f = y.f` for
    /// them, so it leaves those requirements out and keeps the rest.
    pub(crate) fn field_plan_for(
        &mut self,
        d: DataId,
        interface: DataId,
        label: &str,
        compare: bool,
    ) -> Result<std::result::Result<Plan, String>> {
        let g = &self.ev();
        let data = g.data(d);
        let name = data.name().to_string();
        let np = data.params().len();
        if data.group().len() > 1 {
            return Ok(Err(format!(
                "`{name}` is defined together with other types, which {label} isn't derived for yet"
            )));
        }
        if data.sort() == Sort::Prop {
            return Ok(Err(format!("`{name}` is a proposition")));
        }
        if !data.indices().is_empty() {
            return Ok(Err(format!(
                "`{name}` has indices, which {label} isn't derived for yet"
            )));
        }
        if data.ctors().is_empty() {
            return Ok(Err(format!("`{name}` has no constructors")));
        }
        // `T` and the containers it's nested in, when fields are compared.
        let members = if compare {
            match self.members(d, label)? {
                Ok(members) => members,
                Err(why) => return Ok(Err(why)),
            }
        } else {
            Vec::new()
        };
        let g = &self.ev();
        let data = g.data(d);
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = data.params().iter().map(|(_, t)| is_type(t)).collect();
        // Each field, classified; the types to find instances for are
        // checked below.
        let mut deciders = vec![false; np];
        let mut fields = Vec::new();
        // Each with whether it's a proof field's carrier (needing `DecEq`).
        let mut to_decide: Vec<(Value, String, bool)> = Vec::new();
        for ctor in data.ctors() {
            let mut kinds: Vec<Field> = Vec::new();
            for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                let what = format!("the field `{field}` of `{}`", ctor.name);
                let what = if data.record() {
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
                if compare && matches!(value, Value::Pi(..)) {
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
                    kinds.push(Field::Recursive(0));
                    continue;
                }
                if compare
                    && ty
                        .subterms()
                        .any(|(t, _)| matches!(t, Term::Data(e, _) if *e == d))
                {
                    match member_of(g, np, &members, &value)? {
                        Some(m) => kinds.push(Field::Recursive(m)),
                        None => {
                            return Ok(Err(format!(
                                "{what} contains `{name}` inside another type, which {label} \
                                 isn't derived for yet"
                            )));
                        }
                    }
                    continue;
                }
                kinds.push(Field::Decided);
                if compare {
                    for j in mentioned(ty, i) {
                        deciders[j] |= param_is_type[j];
                    }
                    to_decide.push((value, what, false));
                }
            }
            fields.push(kinds);
        }
        // The containers' fields: a member again, or data with an instance.
        let mut nested = Vec::new();
        for member in members.iter().skip(1) {
            let container = g.data(member.data);
            let mut member_fields = Vec::new();
            for ctor in container.ctors() {
                let mut kinds = Vec::new();
                for (i, (_, ty)) in ctor.fields.iter().enumerate() {
                    let what = &member.origin;
                    if ctor.field_erased[i] || (0..i).any(|j| ty.mentions(i - 1 - j)) {
                        return Ok(Err(format!(
                            "{what} has `{name}` inside `{}`, whose fields {label} can't compare",
                            container.name()
                        )));
                    }
                    let env: Vec<Value> = member
                        .args
                        .iter()
                        .cloned()
                        .chain((0..i).map(|_| unused()))
                        .collect();
                    let value = force(g, eval(g, &env, ty)?)?;
                    if matches!(value, Value::Pi(..)) {
                        return Ok(Err(format!(
                            "{what} has a function inside `{}`, and functions can't be compared",
                            container.name()
                        )));
                    }
                    if let Some(m) = member_of(g, np, &members, &value)? {
                        kinds.push(Field::Recursive(m));
                        continue;
                    }
                    let term = quote(g, np, &value)?;
                    for j in 0..np {
                        if term.mentions(np - 1 - j) {
                            deciders[j] |= param_is_type[j];
                        }
                    }
                    kinds.push(Field::Decided);
                    to_decide.push((value, what.clone(), false));
                }
                member_fields.push(kinds);
            }
            nested.push(member_fields);
        }
        // Every type to decide needs an instance, given one for each
        // parameter that's a type.
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(Err("there's no prelude".into()));
        };
        let interface_name = |e: &Self, i: DataId| e.kernel.data(i).name().to_string();
        let names = (
            interface_name(self, interface),
            interface_name(self, dec_eq),
        );
        self.clear_metas();
        let span = self.kernel.data(d).span();
        let params: Vec<(Name, Term)> = self.kernel.data(d).params().to_vec();
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
                        Value::Data(interface, vec![Value::var(j)].into()),
                    );
                }
            }
            for (ty, what, carrier) in to_decide {
                let (needed, needed_name) = if carrier {
                    (dec_eq, &names.1)
                } else {
                    (interface, &names.0)
                };
                let goal = Value::Data(needed, vec![ty.clone()].into());
                if let Some(e) = interfaces::findable(&mut cx, &goal)? {
                    let mut reason = format!(
                        "{what} has type `{}`, which has no `{needed_name}` instance (when \
                         `{name}` was declared)",
                        cx.show(&ty)
                    );
                    if e.code != "E-INSTANCE-NONE" {
                        reason = format!("{reason}: {}", e.message);
                    }
                    // R4: a quotient's equality is never derived from its
                    // representatives.
                    if needed == dec_eq && crate::quot::is_quotient_type(&ty) {
                        reason = format!("{reason}; {}", crate::quot::NO_DERIVED_EQ);
                    }
                    why = Some(reason);
                    break;
                }
            }
        }
        self.clear_metas();
        Ok(match why {
            Some(why) => Err(why),
            None => Ok(Plan {
                deciders,
                fields,
                nested: members
                    .into_iter()
                    .skip(1)
                    .zip(nested)
                    .map(|(member, fields)| Nested { member, fields })
                    .collect(),
            }),
        })
    }

    /// Declares `T.%tag : [params] -> T params -> Nat`.
    pub(crate) fn derive_tag(&mut self, d: DataId) -> Result<()> {
        self.derive_tag_in(d, d, "%tag")
    }

    /// The containers' helpers for member `m` of `T` (`d`), unless declared
    /// already: `T.%m{m}%type`, its type, a definition of `T`'s parameters
    /// (explicit) so source can name it; `T.%m{m}%tag` with two
    /// constructors or more; and, with `fields`, `T.%m{m}%C%k` for each
    /// field. The last two are over the container's own parameters, as
    /// `T.%tag` and `T.%C%k` are over `T`'s.
    pub(crate) fn derive_member_helpers(
        &mut self,
        d: DataId,
        m: usize,
        member: &Member,
        fields: bool,
    ) -> Result<()> {
        let prefix = format!("%m{m}%");
        let ty_member = format!("{prefix}type");
        if !self.has_member(d, &ty_member) {
            let data = self.kernel.data(d);
            let np = data.params().len();
            let mut body = quote(&self.ev(), np, &member.ty())?;
            let mut ty = Term::Sort(data.sort());
            for (x, t) in data.params().iter().rev() {
                ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(t.clone()), Rc::new(ty));
                body = Term::Lam(x.clone(), Icit::Explicit, Rc::new(body));
            }
            let name: Name = format!("{}.{ty_member}", data.name()).into();
            let span = data.span();
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
            let key = Self::member_key(&self.data_key(d), &ty_member);
            self.scope.insert(&key, Global::Def(id), span, false);
        }
        let container = self.kernel.data(member.data);
        let ctors: Vec<usize> = container.ctors().iter().map(|c| c.fields.len()).collect();
        let tag = format!("{prefix}tag");
        if ctors.len() > 1 && !self.has_member(d, &tag) {
            self.derive_tag_in(d, member.data, &tag)?;
        }
        if fields {
            for (c, count) in ctors.iter().enumerate() {
                for k in 0..*count {
                    let name = format!(
                        "{prefix}{}%{k}",
                        self.kernel.data(member.data).ctors()[c].name
                    );
                    if !self.has_member(d, &name) {
                        self.derive_field_in(d, member.data, &prefix, c, k)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Declares `T.member : [params] -> D params -> Nat`, for `D` (`d`) `T`
    /// itself or a container of it.
    fn derive_tag_in(&mut self, owner: DataId, d: DataId, member: &str) -> Result<()> {
        let Some(nat) = self.kernel.env.registry().data(Builtin::Nat) else {
            return Ok(());
        };
        let data = self.kernel.data(d);
        let np = data.params().len();
        let params: Vec<Term> = (0..np).map(|k| Term::Var(np - 1 - k)).collect();
        let ty = Term::Pi(
            "r".into(),
            Icit::Explicit,
            Rc::new(Term::data(d, params)),
            Rc::new(Term::data(nat, Vec::new())),
        );
        let branches: Vec<Branch> = data
            .ctors()
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
        self.declare_member(owner, d, member, ty, body)
    }

    /// Declares `T.%C%k : [params] -> A -> T params -> A`: field `k` of a
    /// `C`, or the first argument for another constructor.
    pub(crate) fn derive_field(&mut self, d: DataId, c: usize, k: usize) -> Result<()> {
        self.derive_field_in(d, d, "%", c, k)
    }

    /// [`Self::derive_field`] for `D` (`d`), `T` itself or a container of
    /// it, named `T.{prefix}C%k` in `T`'s (`owner`'s) namespace.
    fn derive_field_in(
        &mut self,
        owner: DataId,
        d: DataId,
        prefix: &str,
        c: usize,
        k: usize,
    ) -> Result<()> {
        let g = &self.ev();
        let data = g.data(d);
        let np = data.params().len();
        let ctor = &data.ctors()[c];
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
            .ctors()
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
        let member = format!("{prefix}{}%{k}", ctor.name);
        self.declare_member(owner, d, &member, ty, body)
    }

    /// The definition `T.member` in `T`'s (`owner`'s) namespace.
    fn member_def(&self, owner: DataId, member: &str) -> Option<DefId> {
        let key = Self::member_key(&self.data_key(owner), member);
        match self.scope.get(&key) {
            Some((Global::Def(id), _)) => Some(id),
            _ => None,
        }
    }

    /// `def` applied to the parameters `0..np` of a context `depth` deep,
    /// as implicit arguments: how a member over `D`'s parameters is called.
    fn at_params(def: DefId, np: usize, depth: usize) -> Term {
        (0..np).fold(Term::Def(def), |f, j| {
            Term::app_icit(f, Term::Var(depth - 1 - j), Icit::Implicit)
        })
    }

    /// Declares `T.{prefix}C%k%at : [params] -> (s : D params) -> T.{prefix}tag
    /// s = c -> A`, field `k` of `s`, known to be a `C` (constructor `c`):
    /// for any other constructor the equation of the tags is refuted. A
    /// field's type that mentions earlier fields mentions `C%j%at s h` for
    /// them. For `D` (`d`) `T` itself or a container of it, in `T`'s
    /// (`owner`'s) namespace; every earlier field's must be declared.
    fn derive_at_in(
        &mut self,
        owner: DataId,
        d: DataId,
        prefix: &str,
        c: usize,
        k: usize,
    ) -> Result<()> {
        let reg = self.kernel.env.registry();
        let (Some(nat), Some(absurd), Some(exfalso), Some(unequal)) = (
            reg.data(Builtin::Nat),
            reg.def(Builtin::VoidAbsurd),
            reg.def(Builtin::VoidExfalso),
            reg.def(Builtin::NatNeq),
        ) else {
            return Ok(());
        };
        let Some(tag) = self.member_def(owner, &format!("{prefix}tag")) else {
            return Ok(());
        };
        let ctor_name = self.kernel.data(d).ctors()[c].name.clone();
        let earlier: Vec<DefId> = (0..k)
            .map(|j| self.member_def(owner, &format!("{prefix}{ctor_name}%{j}%at")))
            .collect::<Option<_>>()
            .expect("earlier fields' `at`s are declared first");
        let g = &self.ev();
        let data = g.data(d);
        let np = data.params().len();
        let ctor = &data.ctors()[c];
        // The field's type, in the context `params, s, h`.
        let here: Vec<Value> = (0..np + 2).map(Value::var).collect();
        let mut env: Vec<Value> = (0..np).map(Value::var).collect();
        for &at in &earlier {
            let call = Term::app(
                Term::app(Self::at_params(at, np, np + 2), Term::Var(1)),
                Term::Var(0),
            );
            env.push(eval(g, &here, &call)?);
        }
        let field = eval(g, &env, &ctor.fields[k].1)?;
        let prop = ctor.field_sorts[k] == Sort::Prop;
        let params: Vec<Term> = (0..np).map(|j| Term::Var(np - 1 - j)).collect();
        let tag_of_s = Term::app(Self::at_params(tag, np, np + 1), Term::Var(0));
        let ty = Term::Pi(
            "s".into(),
            Icit::Explicit,
            Rc::new(Term::data(d, params)),
            Rc::new(Term::Pi(
                "h".into(),
                Icit::Explicit,
                Rc::new(Term::Eq(
                    Some(Rc::new(Term::data(nat, Vec::new()))),
                    Rc::new(tag_of_s),
                    Rc::new(Term::Nat(Rc::new(BigUint::from(c)))),
                )),
                Rc::new(quote(g, np + 2, &field)?),
            )),
        );
        let mut branches = Vec::new();
        for (other, o) in data.ctors().iter().enumerate() {
            let n = o.fields.len();
            let body = if other == c {
                Term::Var(n - 1 - k)
            } else {
                // `Nat.equalFalse other c rfl h : Void`, `h` read as `other = c`.
                let number = |x: usize| Term::Nat(Rc::new(BigUint::from(x)));
                let refuted = Term::app(
                    Term::app(
                        Term::app(Term::app(Term::Def(unequal), number(other)), number(c)),
                        Term::Refl,
                    ),
                    Term::Var(n),
                );
                let elim = if prop { exfalso } else { absurd };
                Term::app(
                    Term::app_icit(
                        Term::Def(elim),
                        quote(g, np + 2 + n, &field)?,
                        Icit::Implicit,
                    ),
                    refuted,
                )
            };
            branches.push(Branch {
                body: Some(Rc::new(body)),
                names: o.fields.iter().map(|(x, _)| x.clone()).collect(),
            });
        }
        let body = Term::Lam(
            "s".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "h".into(),
                Icit::Explicit,
                Rc::new(Term::Case(1, d, branches.into())),
            )),
        );
        let member = format!("{prefix}{ctor_name}%{k}%at");
        self.declare_member(owner, d, &member, ty, body)
    }

    /// Declares `T.{prefix}view : [params] -> (s : D params) -> (t : Nat) ->
    /// T.{prefix}tag s = t -> D params`: for `t` the position of a
    /// constructor `C`, `C` of `C%0%at s h …`; else `s`. So `view s t h`
    /// computes to a constructor whenever `t` is a number, whatever `s` is,
    /// and `T.{prefix}etaAt` proves it is `s`. Every field's `at` must be
    /// declared.
    fn derive_view_in(&mut self, owner: DataId, d: DataId, prefix: &str) -> Result<()> {
        let Some(nat) = self.kernel.env.registry().data(Builtin::Nat) else {
            return Ok(());
        };
        let Some(tag) = self.member_def(owner, &format!("{prefix}tag")) else {
            return Ok(());
        };
        let data = self.kernel.data(d);
        let np = data.params().len();
        let shapes: Vec<(Name, usize)> = data
            .ctors()
            .iter()
            .map(|c| (c.name.clone(), c.fields.len()))
            .collect();
        let params =
            |depth: usize| -> Vec<Term> { (0..np).map(|j| Term::Var(depth - 1 - j)).collect() };
        let nat_ty = || Rc::new(Term::data(nat, Vec::new()));
        let tag_of_s = Term::app(Self::at_params(tag, np, np + 2), Term::Var(1));
        let ty = Term::Pi(
            "s".into(),
            Icit::Explicit,
            Rc::new(Term::data(d, params(np))),
            Rc::new(Term::Pi(
                "t".into(),
                Icit::Explicit,
                nat_ty(),
                Rc::new(Term::Pi(
                    "h".into(),
                    Icit::Explicit,
                    Rc::new(Term::Eq(
                        Some(nat_ty()),
                        Rc::new(tag_of_s),
                        Rc::new(Term::Var(0)),
                    )),
                    Rc::new(Term::data(d, params(np + 3))),
                )),
            )),
        );
        // In the context `params, s, t, h`.
        let mut arms = Vec::new();
        for (c, (name, count)) in shapes.iter().enumerate() {
            let mut fields = Vec::new();
            for k in 0..*count {
                let at = self
                    .member_def(owner, &format!("{prefix}{name}%{k}%at"))
                    .expect("every field's `at` is declared first");
                fields.push(Term::app(
                    Term::app(Self::at_params(at, np, np + 3), Term::Var(2)),
                    Term::Var(0),
                ));
            }
            arms.push(NumArm {
                value: Rc::new(BigUint::from(c)),
                body: Rc::new(Term::ctor(d, c, fields)),
            });
        }
        let body = ["s", "t", "h"].iter().rev().fold(
            Term::NumCase(1, arms.into(), Rc::new(Term::Var(2))),
            |body, x| Term::Lam((*x).into(), Icit::Explicit, Rc::new(body)),
        );
        self.declare_member(owner, d, &format!("{prefix}view"), ty, body)
    }

    /// For each member of `T` (`d`) with two constructors or more, what the
    /// derived tests and orders compare a value's fields with when its tag
    /// is known, unless declared already: `T.{prefix}C%k%at` for every field,
    /// `T.{prefix}view`, and, as source, `T.{prefix}eta` and
    /// `T.{prefix}etaAt`:
    ///
    /// ```text
    /// T.%eta : [%p0 : _] -> … -> (%s : T %p0 …) -> T.%view %s (T.%tag %s) rfl = %s
    /// T.%eta (C %a0 …) = rfl   -- one equation for each constructor
    ///
    /// T.%etaAt : … -> (%s : T %p0 …) -> (%t : Nat) -> (%h : T.%tag %s = %t) -> T.%view %s %t %h = %s
    /// T.%etaAt %s %t %h = J (%y %q => T.%view %s %y %q = %s) (T.%eta %s) %h
    /// ```
    ///
    /// Each is linear in the number of constructors: `etaAt` at a number
    /// `k` turns any `s` whose tag is `k` into a constructor, so a proof
    /// about `C %a…` and `s` needs to match only the first.
    pub(crate) fn derive_rebuild(&mut self, d: DataId, plan: &Plan) -> Result<()> {
        for m in 0..=plan.nested.len() {
            let (matched, prefix) = if m == 0 {
                (d, "%".to_string())
            } else {
                (plan.nested[m - 1].member.data, format!("%m{m}%"))
            };
            let shapes: Vec<(String, usize)> = self
                .kernel
                .data(matched)
                .ctors()
                .iter()
                .map(|c| (c.name.to_string(), c.fields.len()))
                .collect();
            if shapes.len() < 2 {
                continue;
            }
            for (c, (name, count)) in shapes.iter().enumerate() {
                for k in 0..*count {
                    if !self.has_member(d, &format!("{prefix}{name}%{k}%at")) {
                        self.derive_at_in(d, matched, &prefix, c, k)?;
                    }
                }
            }
            if !self.has_member(d, &format!("{prefix}view")) {
                self.derive_view_in(d, matched, &prefix)?;
            }
            if !self.has_member(d, &format!("{prefix}etaAt")) {
                for definition in self.eta_source(d, plan, m) {
                    self.clear_metas();
                    self.definition(&definition.0, &definition.1)?;
                }
                self.clear_metas();
            }
        }
        Ok(())
    }

    /// The source of member `m`'s `eta` and `etaAt` ([`Self::derive_rebuild`]).
    fn eta_source(&self, d: DataId, plan: &Plan, m: usize) -> Vec<(Decl, Vec<Decl>)> {
        let data = self.kernel.data(d);
        let ty_name = self.relative_to_root(data.name());
        let s = crate::derive_ord::Src { span: data.span() };
        let np = data.params().len();
        let prefix = member_prefix(&ty_name, m);
        let (matched, ctor_prefix, this) = if m == 0 {
            (d, ty_name.clone(), s.this(&ty_name, data))
        } else {
            let container = plan.nested[m - 1].member.data;
            (
                container,
                self.kernel.data(container).path().to_string(),
                s.app(
                    s.var(&format!("{prefix}type")),
                    (0..np).map(|j| s.var(&format!("%p{j}"))).collect(),
                ),
            )
        };
        let with_params = |mut ty: Expr| {
            for j in (0..np).rev() {
                ty = s.pi(&[&format!("%p{j}")], true, false, Expr::Hole(s.span), ty);
            }
            ty
        };
        let (eta, eta_at, view, tag) = (
            format!("{prefix}eta"),
            format!("{prefix}etaAt"),
            format!("{prefix}view"),
            format!("{prefix}tag"),
        );
        let call = |f: &str, args: Vec<Expr>| s.app(s.var(f), args);
        let eta_ty = with_params(s.pi(
            &["%s"],
            false,
            false,
            this.clone(),
            s.eq(
                call(
                    &view,
                    vec![s.var("%s"), call(&tag, vec![s.var("%s")]), s.var("rfl")],
                ),
                s.var("%s"),
            ),
        ));
        let eta_equations = self
            .kernel
            .data(matched)
            .ctors()
            .iter()
            .map(|ctor| {
                let pattern = Pattern::Ctor(
                    s.n(&format!("{ctor_prefix}.{}", ctor.name)),
                    (0..ctor.fields.len())
                        .map(|k| Pattern::Var(s.n(&format!("%a{k}"))))
                        .collect(),
                    s.span,
                );
                s.equation(&eta, vec![pattern], s.var("rfl"))
            })
            .collect();
        let tag_is = s.eq(call(&tag, vec![s.var("%s")]), s.var("%t"));
        let at_ty = with_params(s.pi(
            &["%s"],
            false,
            false,
            this,
            s.pi(
                &["%t"],
                false,
                false,
                s.var("Std.Nat"),
                s.pi(
                    &["%h"],
                    false,
                    false,
                    tag_is,
                    s.eq(
                        call(&view, vec![s.var("%s"), s.var("%t"), s.var("%h")]),
                        s.var("%s"),
                    ),
                ),
            ),
        ));
        let motive = s.lam(
            &["%y", "%q"],
            s.eq(
                call(&view, vec![s.var("%s"), s.var("%y"), s.var("%q")]),
                s.var("%s"),
            ),
        );
        let at_body = call(
            "J",
            vec![motive, call(&eta, vec![s.var("%s")]), s.var("%h")],
        );
        let vars = |xs: &[&str]| xs.iter().map(|x| Pattern::Var(s.n(x))).collect::<Vec<_>>();
        vec![
            (s.signature(&eta, eta_ty, false), eta_equations),
            (
                s.signature(&eta_at, at_ty, false),
                vec![s.equation(&eta_at, vars(&["%s", "%t", "%h"]), at_body)],
            ),
        ]
    }

    /// Declares `T.%C%P%k : (params) -> (fields before k) -> Prop`, the type
    /// of proof field `k` of `C`, all its arguments explicit.
    pub(crate) fn derive_proof_type(&mut self, d: DataId, c: usize, k: usize) -> Result<()> {
        let data = self.kernel.data(d);
        let ctor = &data.ctors()[c];
        let binders: Vec<(Name, Term)> = data
            .params()
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
        let name: Name = format!("{}.{member}", data.name()).into();
        let span = data.span();
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
        let key = Self::member_key(&self.data_key(d), &member);
        self.scope.insert(&key, Global::Def(id), span, false);
        Ok(())
    }

    /// Adds `T.member` in `T`'s (`owner`'s) namespace, of type `[params] ->
    /// ty`, with body `[params] -> body`, the parameters `d`'s (`T`'s, or a
    /// container's).
    fn declare_member(
        &mut self,
        owner: DataId,
        d: DataId,
        member: &str,
        ty: Term,
        body: Term,
    ) -> Result<()> {
        let data = self.kernel.data(d);
        let (mut ty, mut body) = (ty, body);
        for (x, t) in data.params().iter().rev() {
            ty = Term::Pi(x.clone(), Icit::Implicit, Rc::new(t.clone()), Rc::new(ty));
            body = Term::Lam(x.clone(), Icit::Implicit, Rc::new(body));
        }
        let owner_data = self.kernel.data(owner);
        let name: Name = format!("{}.{member}", owner_data.name()).into();
        let span = owner_data.span();
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
        let key = Self::member_key(&self.data_key(owner), member);
        self.scope.insert(&key, Global::Def(id), span, false);
        Ok(())
    }

    /// The source of `T.%same`, its proofs and `T.%instDecEq`; for a nested
    /// type, also `T.%m1%same` and its proofs for each container it's in,
    /// the `same`s defined together.
    fn eq_source(&self, d: DataId, plan: &Plan) -> Source {
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
            decreasing: None,
            opaque: false,
            unfolding: Vec::new(),
            defaults: Vec::new(),
            attrs: Vec::new(),
            syntax_error: None,
            span,
        };
        let np = data.params().len();
        let param = |j: usize| format!("%p{j}");
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let same_of = |m: usize| format!("{}same", member_prefix(&ty_name, m));
        let sound_of = |m: usize| format!("{}sameSound", member_prefix(&ty_name, m));
        let complete_of = |m: usize| format!("{}sameComplete", member_prefix(&ty_name, m));
        let deciders: Vec<usize> = (0..np).filter(|j| plan.deciders[*j]).collect();
        // The dictionaries' names: `decEq`, or one per parameter after it
        // (`decEqA` for `a`) when there are several.
        let dict = |j: usize| {
            if deciders.len() == 1 {
                "decEq".to_string()
            } else {
                let p = data.params()[j].0.to_string();
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

        let mut tests = Vec::new();
        let mut proofs = Vec::new();
        let mut readings = Vec::new();
        for m in 0..=plan.nested.len() {
            let prefix = member_prefix(&ty_name, m);
            // The type matched on, how source names its constructors, and
            // the member's type: `T %p0 …`, or `T.%m1%type %p0 …`.
            let (matched, ctor_prefix, this) = if m == 0 {
                (d, ty_name.clone(), this.clone())
            } else {
                let container = plan.nested[m - 1].member.data;
                (
                    container,
                    self.kernel.data(container).path().to_string(),
                    apps(
                        var(&format!("{prefix}type")),
                        (0..np).map(|j| var(&param(j))).collect(),
                    ),
                )
            };
            let ctors = self.kernel.data(matched).ctors();
            let member_fields = plan.member_fields(m);

            // T.%same : … -> (%r %s : T %p0 …) -> Bool, and its two proofs.
            let pair = |cod: Expr| {
                with_params(
                    Expr::Pi {
                        names: vec![n("%r"), n("%s")],
                        implicit: false,
                        auto: false,
                        dom: Box::new(this.clone()),
                        cod: Box::new(cod),
                        span,
                    },
                    true,
                )
            };
            let same_name = n(&same_of(m));
            let sound_name = n(&sound_of(m));
            let complete_name = n(&complete_of(m));
            let same_test = apps(var(&same_name.text), vec![var("%r"), var("%s")]);
            let is_true = eq(same_test, var("Std.Bool.True"));
            let same_signature = signature(&same_name, pair(var("Std.Bool")), false);
            let sound_signature = signature(
                &sound_name,
                pair(Expr::Arrow(
                    Box::new(is_true.clone()),
                    Box::new(eq(var("%r"), var("%s"))),
                )),
                false,
            );
            let complete_signature = signature(
                &complete_name,
                pair(Expr::Arrow(
                    Box::new(eq(var("%r"), var("%s"))),
                    Box::new(is_true),
                )),
                false,
            );

            let mut same_equations = Vec::new();
            let mut sound_equations = Vec::new();
            let mut complete_equations = Vec::new();
            for (c, ctor) in ctors.iter().enumerate() {
                let ctor_name = format!("{ctor_prefix}.{}", ctor.name);
                let kinds = &member_fields[c];
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
                let last = data_fields.len().saturating_sub(1);
                // Data field `k`'s equation, from `%q`, the conjunction of
                // all of them: `And.left (And.right … %q)`.
                let part = |k: usize| {
                    let i = data_fields.iter().position(|&j| j == k).unwrap_or(0);
                    let mut x = var("%q");
                    for _ in 0..i {
                        x = apps(var("Std.And.right"), vec![x]);
                    }
                    if i < last {
                        x = apps(var("Std.And.left"), vec![x]);
                    }
                    x
                };
                // The test: the fields' tests joined by `&&`, each run
                // only once those before it hold; `y(k)` is what `%ak` is
                // compared with.
                let test = |k: usize, y: &dyn Fn(usize) -> Expr| match kinds[k] {
                    Field::Recursive(target) => apps(var(&same_of(target)), vec![var(&a(k)), y(k)]),
                    _ => apps(
                        var("Std.Decidable.holds"),
                        vec![apps(var("Std.DecEq.decide"), vec![var(&a(k)), y(k)])],
                    ),
                };
                let tests = |y: &dyn Fn(usize) -> Expr| {
                    let mut fields = data_fields.iter().rev();
                    let Some(&k) = fields.next() else {
                        return var("Std.Bool.True");
                    };
                    fields.fold(test(k, y), |rest, &k| {
                        Expr::Binary(BinOp::And, Box::new(test(k, y)), Box::new(rest))
                    })
                };
                // The decision that `C %a… = C %b…`, with `b` the names of
                // the right side's fields, stated, so the proofs' types are
                // known. Its `holds` is the test.
                let whole = |b: &dyn Fn(usize) -> String| {
                    let proof = fields_equal(
                        span,
                        &ctor_name,
                        &format!("{prefix}{}", ctor.name),
                        &is_proof,
                        np,
                        &this,
                        &a,
                        b,
                        &part,
                        &|j| format!("%p{j}"),
                    );
                    // The decision of one field, for the proofs (which are
                    // erased): a recursive field's is made from `T.%same`
                    // and its two proofs, called on a part of the argument.
                    let decision = |k: usize| match kinds[k] {
                        Field::Recursive(target) => {
                            let call = |f: String, x: &str| {
                                apps(var(&f), vec![var(&a(k)), var(&b(k)), var(x)])
                            };
                            Expr::Record {
                                base: None,
                                fields: vec![
                                    (
                                        n("holds"),
                                        apps(var(&same_of(target)), vec![var(&a(k)), var(&b(k))]),
                                    ),
                                    (n("sound"), lam(&["%x"], call(sound_of(target), "%x"))),
                                    (n("complete"), lam(&["%x"], call(complete_of(target), "%x"))),
                                ],
                                span,
                            }
                        }
                        _ => apps(var("Std.DecEq.decide"), vec![var(&a(k)), var(&b(k))]),
                    };
                    let cong = |k: usize| {
                        let field = format!("{prefix}{}%{k}", ctor.name);
                        apps(
                            var("Std.Eq.cong"),
                            vec![apps(var(&field), vec![var(&a(k))]), var("%e")],
                        )
                    };
                    let whole = if data_fields.is_empty() {
                        apps(var("Std.Decidable.yes"), vec![proof])
                    } else {
                        let mut all = decision(data_fields[last]);
                        let mut equal = cong(data_fields[last]);
                        for &k in data_fields[..last].iter().rev() {
                            all = apps(
                                var("Std.Decidable.andThen"),
                                vec![decision(k), lam(&["%u"], all)],
                            );
                            equal = apps(var("Std.And.Both"), vec![cong(k), equal]);
                        }
                        apps(
                            var("Std.Decidable.map"),
                            vec![all, lam(&["%q"], proof), lam(&["%e"], equal)],
                        )
                    };
                    let applied = |f: &dyn Fn(usize) -> String| {
                        apps(var(&ctor_name), (0..count).map(|k| var(&f(k))).collect())
                    };
                    let claim = apps(
                        var("Std.Decidable"),
                        vec![eq(
                            Expr::Ann(Box::new(applied(&a)), Box::new(this.clone()), span),
                            applied(b),
                        )],
                    );
                    Expr::Ann(Box::new(whole), Box::new(claim), span)
                };
                let equation =
                    |name: &ast::Name, patterns: Vec<Pattern>, rhs: Expr| Decl::Equation {
                        guard: None,
                        name: name.clone(),
                        patterns,
                        rhs: Some(rhs),
                        arm: None,
                        span,
                    };
                let with = |second: Pattern, extra: Option<&str>| {
                    let mut patterns = vec![pattern(&a), second];
                    patterns.extend(extra.map(|x| Pattern::Var(n(x))));
                    patterns
                };
                if ctors.len() == 1 {
                    let both = |extra| with(pattern(&b), extra);
                    let by_b = |k: usize| var(&b(k));
                    same_equations.push(equation(&same_name, both(None), tests(&by_b)));
                    sound_equations.push(equation(
                        &sound_name,
                        both(Some("%h")),
                        apps(var("Std.Decidable.sound"), vec![whole(&b), var("%h")]),
                    ));
                    complete_equations.push(equation(
                        &complete_name,
                        both(Some("%e")),
                        apps(var("Std.Decidable.complete"), vec![whole(&b), var("%e")]),
                    ));
                    continue;
                }
                // Two constructors or more: the tags first, then the fields
                // of the first value with the second's, by projection. The
                // proofs turn the second into a `C` by `T.%etaAt`.
                let number = Expr::Num(BigUint::from(c), span);
                let tag = format!("{prefix}tag");
                let tag_s = apps(var(&tag), vec![var("%s")]);
                let projected = |k: usize| {
                    let field = format!("{prefix}{}%{k}", ctor.name);
                    apps(var(&field), vec![var(&a(k)), var("%s")])
                };
                let tags_equal = apps(var("Std.Nat.equal"), vec![number.clone(), tag_s.clone()]);
                let rhs = if data_fields.is_empty() {
                    tags_equal
                } else {
                    Expr::Binary(
                        BinOp::And,
                        Box::new(tags_equal),
                        Box::new(tests(&projected)),
                    )
                };
                let second = || Pattern::Var(n("%s"));
                same_equations.push(equation(&same_name, with(second(), None), rhs));
                // T.%sameSound (C %a0 …) %s %h =
                //   let %e : T.%tag %s = c := Eq.sym (DecEq.tagsSame c (T.%tag %s) %h)
                //   let %b0 := T.%C%0%at %s %e …
                //   let %v := J (%y %q => T.%same (C %a0 …) %y = True) %h (Eq.sym (T.%etaAt %s c %e))
                //   Eq.trans (Decidable.sound (… : Decidable (C %a0 … = C %b0 …)) %v) (T.%etaAt %s c %e)
                let first = Expr::Ann(
                    Box::new(apps(
                        var(&ctor_name),
                        (0..count).map(|k| var(&a(k))).collect(),
                    )),
                    Box::new(this.clone()),
                    span,
                );
                let same_as = |y: &str| {
                    lam(
                        &[y, "%q"],
                        eq(
                            apps(var(&same_name.text), vec![first.clone(), var(y)]),
                            var("Std.Bool.True"),
                        ),
                    )
                };
                let eta_at = apps(
                    var(&format!("{prefix}etaAt")),
                    vec![var("%s"), number.clone(), var("%e")],
                );
                let tags_same = if data_fields.is_empty() {
                    apps(
                        var("Std.Nat.equalSound"),
                        vec![number.clone(), tag_s.clone(), var("%h")],
                    )
                } else {
                    apps(
                        var("Std.DecEq.tagsSame"),
                        vec![number.clone(), tag_s.clone(), var("%h")],
                    )
                };
                let viewed = apps(
                    var("J"),
                    vec![
                        same_as("%y"),
                        var("%h"),
                        apps(var("Std.Eq.sym"), vec![eta_at.clone()]),
                    ],
                );
                let mut body = apps(
                    var("Std.Eq.trans"),
                    vec![
                        apps(var("Std.Decidable.sound"), vec![whole(&b), var("%v")]),
                        eta_at,
                    ],
                );
                let by_b = |k: usize| var(&b(k));
                let viewed_ty = eq(tests(&by_b), var("Std.Bool.True"));
                body = let_in(span, "%v", Some(viewed_ty), viewed, body);
                for k in (0..count).rev() {
                    let field = format!("{prefix}{}%{k}%at", ctor.name);
                    body = let_in(
                        span,
                        &b(k),
                        None,
                        apps(var(&field), vec![var("%s"), var("%e")]),
                        body,
                    );
                }
                body = let_in(
                    span,
                    "%e",
                    Some(eq(tag_s.clone(), number.clone())),
                    apps(var("Std.Eq.sym"), vec![tags_same]),
                    body,
                );
                sound_equations.push(equation(&sound_name, with(second(), Some("%h")), body));
                // T.%sameComplete (C %a0 …) %s %e =
                //   J (%y %q => T.%same (C %a0 …) %y = True) (Decidable.complete (… : Decidable (C %a0 … = C %a0 …)) rfl) %e
                let refl = apps(var("Std.Decidable.complete"), vec![whole(&a), var("rfl")]);
                complete_equations.push(equation(
                    &complete_name,
                    with(second(), Some("%e")),
                    apps(var("J"), vec![same_as("%y"), refl, var("%e")]),
                ));
            }
            tests.push((same_signature, same_equations));
            proofs.push((sound_signature, sound_equations));
            proofs.push((complete_signature, complete_equations));
            // The test's two readings (§5.4), from its two proofs; the
            // negative one by `Decidable.refute` and `toBoolOfNot` on the
            // decision the instance is made of.
            let as_reading = |name: &ast::Name, ty: Expr, body: Expr| {
                let mut sig = signature(name, ty, false);
                if let Decl::Signature { theorem, attrs, .. } = &mut sig {
                    *theorem = true;
                    attrs.push(ast::Attribute {
                        name: n("reading"),
                        arg: None,
                        span,
                    });
                }
                let equation = Decl::Equation {
                    guard: None,
                    name: name.clone(),
                    patterns: Vec::new(),
                    rhs: Some(lam(&["%r", "%s"], body)),
                    arm: None,
                    span,
                };
                (sig, vec![equation])
            };
            let iff = |a: Expr, b: Expr| apps(var("Std.Iff"), vec![a, b]);
            let record = |fields: Vec<(&str, Expr)>| Expr::Record {
                base: None,
                fields: fields.into_iter().map(|(f, e)| (n(f), e)).collect(),
                span,
            };
            let by_pair = |f: String| apps(var(&f), vec![var("%r"), var("%s")]);
            let test = by_pair(same_name.text.clone());
            let decision = Expr::Ann(
                Box::new(record(vec![
                    ("holds", by_pair(same_of(m))),
                    ("sound", by_pair(sound_of(m))),
                    ("complete", by_pair(complete_of(m))),
                ])),
                Box::new(apps(var("Std.Decidable"), vec![eq(var("%r"), var("%s"))])),
                span,
            );
            readings.push(as_reading(
                &n(&format!("{prefix}sameReads")),
                pair(iff(
                    eq(test.clone(), var("Std.Bool.True")),
                    eq(var("%r"), var("%s")),
                )),
                record(vec![
                    ("forward", by_pair(sound_of(m))),
                    ("backward", by_pair(complete_of(m))),
                ]),
            ));
            let refute = apps(
                var("Std.Decidable.refute"),
                vec![decision.clone(), var("%e")],
            );
            let to_bool = apps(var("Std.Decidable.toBoolOfNot"), vec![decision, var("%n")]);
            readings.push(as_reading(
                &n(&format!("{prefix}sameReadsFalse")),
                pair(iff(
                    eq(test, var("Std.Bool.False")),
                    Expr::Binary(BinOp::Ne, Box::new(var("%r")), Box::new(var("%s"))),
                )),
                record(vec![
                    ("forward", lam(&["%e"], refute)),
                    ("backward", lam(&["%n"], to_bool)),
                ]),
            ));
        }
        // T.%decide : … -> (%r %s : T %p0 …) -> Std.Decidable (%r = %s) :=
        //   { holds = T.%same %r %s, sound = T.%sameSound %r %s, complete = … }
        // A definition of its own, as `Nat.decEq` is, rather than a lambda in
        // the instance: `r == s` is then the call `(T.%decide r s).holds`, kept
        // folded, so it prints as `r == s` and is compared with another `==`
        // by its arguments. Inlined, `r == s` would compute to `T.%same r s`,
        // which on a record unfolds to its fields' tests: a `match h: r == s`
        // would give `h` that type, in which `DecEq.sound h` can't find `r`
        // and `s`.
        let by = |f: String| apps(var(&f), vec![var("%r"), var("%s")]);
        let decision = Expr::Record {
            base: None,
            fields: vec![
                (n("holds"), by(same_of(0))),
                (n("sound"), by(sound_of(0))),
                (n("complete"), by(complete_of(0))),
            ],
            span,
        };
        let decide_name = n(&format!("{ty_name}.%decide"));
        let decide_ty = with_params(
            Expr::Pi {
                names: vec![n("%r"), n("%s")],
                implicit: false,
                auto: false,
                dom: Box::new(this.clone()),
                cod: Box::new(apps(var("Std.Decidable"), vec![eq(var("%r"), var("%s"))])),
                span,
            },
            true,
        );
        let decide = (
            signature(&decide_name, decide_ty, false),
            vec![Decl::Equation {
                guard: None,
                name: decide_name.clone(),
                patterns: vec![Pattern::Var(n("%r")), Pattern::Var(n("%s"))],
                rhs: Some(decision),
                arm: None,
                span,
            }],
        );
        // instance T.%instDecEq : … -> Std.DecEq (T %p0 …) := { decide = T.%decide }
        let instance_name = n(&format!("{ty_name}.%instDecEq"));
        let instance_ty = with_params(apps(var("Std.DecEq"), vec![this.clone()]), true);
        let instance = (
            signature(&instance_name, instance_ty, true),
            vec![Decl::Equation {
                guard: None,
                name: instance_name,
                patterns: Vec::new(),
                rhs: Some(Expr::Record {
                    base: None,
                    fields: vec![(n("decide"), var(&decide_name.text))],
                    span,
                }),
                arm: None,
                span,
            }],
        );
        Source {
            tests,
            proofs,
            decide,
            instance,
            readings,
        }
    }
}

/// A proof of `(C %a0 … : this) = C %b0 …` for the constructor source names
/// `ctor_name` (`T.C`), given `h(k): %ak = %bk` for
/// each data field; `is_proof` says which fields are proofs, and
/// `{helper}%P%k` (`T.%C%P%k`) must be declared for each. First, for proofs `%z…` of the
/// proof fields' types: `C %a… = C %a…[%z…]`, along `DecEq.uniqueEq`'s
/// equations. Then each data field's `J`, the claim for all proofs carried
/// along: `y q => (%z: P …) -> C %a… = C %b… y %a… %z…`; at the end it's
/// applied to the `%b`s' proofs. Shared by derived `DecEq` and `Ord`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn fields_equal(
    span: Span,
    ctor_name: &str,
    helper: &str,
    is_proof: &[bool],
    np: usize,
    this: &Expr,
    a: &dyn Fn(usize) -> String,
    b: &dyn Fn(usize) -> String,
    h: &dyn Fn(usize) -> Expr,
    param: &dyn Fn(usize) -> String,
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
    let z = |k: usize| format!("%z{k}");
    let count = is_proof.len();
    let proofs: Vec<usize> = (0..count).filter(|k| is_proof[*k]).collect();
    let data_fields: Vec<usize> = (0..count).filter(|k| !is_proof[*k]).collect();
    // `C x0 … xn`, the left side annotated for the parameters the fields
    // don't determine.
    let built =
        |field: &dyn Fn(usize) -> Expr| apps(var(ctor_name), (0..count).map(field).collect());
    let left = Expr::Ann(
        Box::new(built(&|j| var(&a(j)))),
        Box::new(this.clone()),
        span,
    );
    // A proof field's type, from the fields before it.
    let proof_type = |k: usize, field: &dyn Fn(usize) -> Expr| {
        let helper = format!("{helper}%P%{k}");
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

/// `let x : ty := value` then `body`, in generated source.
pub(crate) fn let_in(span: Span, x: &str, ty: Option<Expr>, value: Expr, body: Expr) -> Expr {
    Expr::Let {
        name: ast::Name {
            text: x.to_string(),
            span,
        },
        ty: ty.map(Box::new),
        value: Box::new(value),
        body: Box::new(body),
        span,
    }
}

/// The source [`Elaborator::eq_source`] generates.
struct Source {
    /// `T.%same`, then each container's, defined together.
    tests: Vec<(Decl, Vec<Decl>)>,
    /// `T.%sameSound` and `T.%sameComplete`, then each container's, defined
    /// together after the tests, which their types mention.
    proofs: Vec<(Decl, Vec<Decl>)>,
    /// `T.%decide`, the decision made of `T.%same` and its proofs.
    decide: (Decl, Vec<Decl>),
    instance: (Decl, Vec<Decl>),
    /// `T.%sameReads` and `T.%sameReadsFalse`, then each container's: the
    /// readings of the tests, filed once the instance is.
    readings: Vec<(Decl, Vec<Decl>)>,
}
