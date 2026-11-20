//! A derived `DecEq` instance for data types and records declared in a
//! program: `T.%instDecEq`, made from `T.%same`, a `Bool` test of equality
//! on `T`, and proofs that it is right (docs/proposals/interfaces.md §5.11, D164,
//! D179). `==`, `!=`, `if h: x = y` and `auto` then find it as any instance.
//! Both are generated as source, naming the library through `Std.` paths,
//! and elaborated like any definition, so the kernel checks them and
//! nothing in the kernel changes.
//!
//! It's derived when `T` is declared, for every type it can be: one with
//! constructors (not a proposition, without indices) whose fields are
//!
//! - data that doesn't depend on earlier fields and is either `T` itself or
//!   a type defined together with it, with the same parameters, or one of
//!   those inside an earlier data type without indices (a nested type,
//!   below), or has a `DecEq` instance, given one for each parameter that's
//!   a type; or
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
//! The core's types are skipped: they come before `DecEq`. So is a type
//! whose module declares its own `DecEq` instance (§5.11: it replaces the
//! derived one), as far as the module's names say before anything is
//! checked.
//!
//! Types defined together (`Expr`, `Item`, `Statement`, `Body` of a syntax
//! tree) are derived together, once the last of them is admitted
//! (docs/proposals/derived-equality.md §5.3): one plan for the group, whose
//! *roots* are its types, then one block of tests (`Expr.%same`,
//! `Item.%same`, …) and one of proofs, all defined together, and each type's
//! `decide`, instance and readings. A type of the group whose module writes
//! its own instance gets none derived, but its `%same` is still made, for
//! the others to call. If any type's fields can't be compared, the whole
//! group gets none, and the note names the field.
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
//! T.%sameIff : … -> (r : T a) -> (s : T a) -> Iff (T.%same r s = True) (r = s)
//! T.%sameIff (C2 a0 a1) s =
//!   let k : T.%tag s = 1 -> Iff (T.%same (C2 a0 a1) s = True) (C2 a0 a1 = s) := e =>
//!     let b0 := T.%C2%0%at s e; let b1 := T.%C2%1%at s e
//!     J (y q => Iff (T.%same (C2 a0 a1) y = True) (C2 a0 a1 = y))
//!       (let d := (… : Decidable (C2 a0 a1 = C2 b0 b1)); { forward = Decidable.sound d, backward = Decidable.complete d })
//!       (T.%etaAt s 1 e)
//!   { forward = h => (k (Eq.sym (DecEq.tagsSame 1 (T.%tag s) h))).forward h,
//!     backward = x => (k (Eq.sym (Eq.cong T.%tag x))).backward x }
//!
//! T.%sameSound r s h = (T.%sameIff r s).forward h
//! T.%sameComplete r s e = (T.%sameIff r s).backward e
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
//! The proofs state each constructor's decision once, in `T.%sameIff`, so
//! that its `holds` is exactly the test, and take its `sound` and
//! `complete` (a field of type `T a` is decided by `T.%same` and its
//! `T.%sameIff`). A constructor whose fields are all data is decided as
//! the equality of its fields paired up, `MkPair a0 (MkPair a1 …)`, by
//! `Pair.decMk` a field at a time, and carried back to `C a… = C b…` by
//! `Eq.cong` of `T.%C%unpack` and `T.%C%pack` ([`Elaborator::
//! derive_tuple_in`]); with proof fields, by `Decidable.andThen` and the
//! `J`s below. Reading each field's equation out of one conjunction
//! instead, `And.left (And.right^k q)`, made the proofs cubic in the
//! fields: 16.9 M steps for a record of 16 (SW-3719,
//! docs/proposals/derived-instances-rethink.md). With one constructor both
//! values are matched (`T.%same (C a0 a1) (C b0 b1)`). With more, only the
//! first is, and the second's fields are read by projection, once the tags
//! agree: `T.%etaAt s c e` turns `s`, whose tag is `c`, into the constructor
//! `c` of its fields, so each equation's proof is about two values of one
//! constructor. Matching both values would make a case tree of n² leaves
//! for n constructors, each checked; this is n leaves (docs/proposals/
//! derived-equality.md §5.6). The `T.%sameIff`s are defined after the
//! `T.%same`s and together, since their types mention them, then each
//! `T.%sameSound` and `T.%sameComplete`.
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
//! recursive function, as it refuses `map`. Instead each container a root
//! is in, found by [`Elaborator::members`] (`List Packet`; for `List (List
//! T)` both lists; for `Option (T, Nat)` the option and the pair; a
//! program's `Spaced Statement`), is a *member*, named in the namespace of
//! the root whose field first led to it and numbered from 1 there, with
//! the same generated functions under `T.%m1%`: `T.%m1%type` (its type, so
//! source can name it), `T.%m1%tag`, `T.%m1%Cons%0`, `T.%m1%Cons%0%at`,
//! `T.%m1%view`, `T.%m1%eta`, `T.%m1%etaAt`, `T.%m1%same` and its
//! proofs, made as for a data type whose fields are its constructors' with
//! the container's arguments: `T.%m1%same (Cons a0 a1) (Cons b0 b1)` tests
//! `a0` by `T.%same` and `a1` by itself. The `same`s are defined together
//! (so are the proofs), and every call is on a part of an argument. Any
//! earlier data type without indices is looked into (§5.4); `T` inside a
//! `Vec`, or a quotient, gets the note naming it. For `==` any container is
//! right, since any two decisions of `x = y` agree. An `Ord`
//! (`derive_ord.rs`) or `Show` must agree with the container's own, so it's
//! derived only through `List`, `Option`, `Pair` (whose instances in the
//! core are constructors then fields) and types whose instance is derived
//! too.
//!
//! Generating eagerly, when `T` is declared, is simpler than on first use,
//! which would mean elaborating new definitions in the middle of the one
//! using `==`.
//!
//! Names generated here contain `%`, which source can't write, so they never
//! clash with the user's.

use std::rc::Rc;
use stitchwort_core::Ev;

use crate::check::quote_internal;
use crate::kernel;
use num_bigint::BigUint;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Decl, Expr, NeForm, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, interfaces};
use stitchwort_syntax::Diagnostic;

/// How `==` (or a derived `Ord`) treats one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Field {
    /// It's a type of the group again, or a container of one the derivers
    /// look into: member `m` of [`Plan::members`], a call to that member's
    /// function, defined together with the group's.
    Recursive(usize),
    /// Its type has an instance of the interface: `DecEq`, which
    /// `if h : x = y` finds, or `Ord`.
    Decided,
    /// A proof of an equation in a type with a `DecEq` instance: not
    /// compared.
    Proof,
}

/// What a derived `==` (or `Ord`) for a group of data types is made from:
/// one type, or the types defined together with it.
pub(crate) struct Plan {
    /// Which parameters (types) take a dictionary: those fields use. The
    /// group's types share their parameters.
    pub(crate) deciders: Vec<bool>,
    /// The group's types (the first [`Plan::roots`]), then the containers
    /// they're nested in.
    pub(crate) members: Vec<Member>,
    /// For each member, for each of its constructors, each field's.
    pub(crate) fields: Vec<Vec<Vec<Field>>>,
    /// How many of the members are the group's types.
    pub(crate) roots: usize,
}

impl Plan {
    /// Member `m`'s fields.
    pub(crate) fn member_fields(&self, m: usize) -> &[Vec<Field>] {
        &self.fields[m]
    }
}

/// A type a derived instance has a function for: a type of the group (a
/// *root*: `T` itself, or a type defined together with it), or a container
/// of one that a root's field, or another member's, has as its type (`List
/// Packet`, `List (List Packet)`, `Option (Packet, Nat)` and the pair in it,
/// a `Spaced Statement` of the program's own `Spaced`). Each member gets its
/// own function, all defined together, so that every call is on a part of
/// the argument: passing `T`'s function to `List`'s instance would be
/// refused as `map` is.
pub(crate) struct Member {
    /// The type: a root, or a container.
    pub(crate) data: DataId,
    /// Its arguments, with the group's parameters as the variables `0..np`.
    pub(crate) args: Vec<Value>,
    /// For a container, the field it's in, as notes name it (`the field
    /// `items` of `Packets``).
    pub(crate) origin: String,
    /// The root whose namespace its generated names are in: itself for a
    /// root; for a container, the root whose field first led to it.
    pub(crate) owner: DataId,
    /// Its generated names' prefix in the owner's namespace: `%` for a root
    /// (`T.%same`), `%m1%` for the first container of an owner (`T.%m1%same`,
    /// `T.%m1%tag`, `T.%m1%Cons%0`).
    pub(crate) prefix: String,
}

/// Which of `members` has type `ty` (with the group's parameters as the
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
    /// Its type, with the group's parameters as the variables `0..np`.
    pub(crate) fn ty(&self) -> Value {
        Value::Data(self.data, self.args.clone().into())
    }

    /// Whether it's a type of the group, not a container.
    pub(crate) fn is_root(&self) -> bool {
        self.data == self.owner && self.prefix == "%"
    }
}

/// The containers whose own `Ord` and `Show` instances (written in the
/// core) are the ones a member built from their constructors gives:
/// constructors in order, then fields; `[x, y]`, `(x, y)`, `Some x`.
fn known_container(g: &Ev, e: DataId) -> bool {
    [Builtin::List, Builtin::Option, Builtin::Pair]
        .iter()
        .any(|b| g.env.registry().data(*b) == Some(e))
}

/// How a note names a field of a type of a group of `group_len`: `its field
/// `x``, in a record alone; else the record or constructor it's in, with a
/// sum's constructor qualified by its type, since a group's notes are read
/// beside other types' (`Guard.When`).
pub(crate) fn field_origin(
    data: &stitchwort_core::globals::Data,
    ctor: &stitchwort_core::globals::Ctor,
    field: &str,
    group_len: usize,
) -> String {
    match (data.record(), group_len) {
        (true, 1) => format!("its field `{field}`"),
        (true, _) => format!("the field `{field}` of `{}`", data.name()),
        (false, 1) => format!("the field `{field}` of `{}`", ctor.name),
        (false, _) => format!("the field `{field}` of `{}.{}`", data.name(), ctor.name),
    }
}

/// Whether a term mentions one of the group's types.
pub(crate) fn mentions_group(term: &Term, group: &[DataId]) -> bool {
    term.subterms()
        .any(|(t, _)| matches!(t, Term::Data(e, _) if group.contains(e)))
}

/// Which derived instance a refusal is about.
#[derive(Clone, Copy)]
pub(crate) enum Derivation {
    Eq,
    Ord,
    Show,
}

impl Elaborator {
    /// The types of `d`'s group, and for each whether its module declares
    /// its own instance of `interface`, which the group's derivation leaves
    /// alone.
    pub(crate) fn group_and_own(&self, d: DataId, interface: DataId) -> (Vec<DataId>, Vec<bool>) {
        let group: Vec<DataId> = self.kernel.data(d).group().to_vec();
        let own = group
            .iter()
            .map(|&r| self.declares_instance_for(r, interface))
            .collect();
        (group, own)
    }

    /// Records `why` as the reason `which` isn't derived, for each type of
    /// the group without its own instance.
    pub(crate) fn refuse_group(
        &mut self,
        which: Derivation,
        group: &[DataId],
        own: &[bool],
        why: &str,
    ) {
        let owners = &self.session.owners;
        let table = match which {
            Derivation::Eq => &mut self.tables.no_eq,
            Derivation::Ord => &mut self.tables.no_ord,
            Derivation::Show => &mut self.tables.no_show,
        };
        for (&r, own) in group.iter().zip(own) {
            if !own {
                table.insert(owners, r, why.to_string());
            }
        }
    }

    /// After data type or record `d` is admitted: its `DecEq` instance, if
    /// one can be derived, or else why not. The types of a group are
    /// derived together, once the last of them is admitted, each getting
    /// its instance unless its module declares one.
    pub(crate) fn derive_data_eq(&mut self, d: DataId) -> Result<()> {
        // Nor for a type the compiler declared, whose constructors' names
        // source can't write: an ability's operations (`effects.rs`).
        let data = self.kernel.data(d);
        let generated = !data.record() && data.ctors().iter().any(|c| c.name.starts_with('%'));
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(());
        };
        if generated || data.group().last() != Some(&d) {
            return Ok(());
        }
        let (group, own) = self.group_and_own(d, dec_eq);
        if own.iter().all(|x| *x) {
            return Ok(());
        }
        let refuse = |e: &mut Self, why: String| e.refuse_group(Derivation::Eq, &group, &own, &why);
        let plan = match self.field_plan(d, dec_eq, "`==`")? {
            Ok(plan) => plan,
            Err(why) => {
                refuse(self, why);
                return Ok(());
            }
        };
        for (ri, &r) in group.iter().enumerate() {
            let ctors = self.kernel.data(r).ctors().len();
            if ctors > 1 {
                self.derive_tag(r)?;
            }
            for c in 0..ctors {
                for (k, field) in plan.fields[ri][c].iter().enumerate() {
                    match field {
                        Field::Proof => self.derive_proof_type(r, c, k)?,
                        _ => self.derive_field(r, c, k)?,
                    }
                }
                self.derive_tuple_in(r, r, "%", c)?;
            }
        }
        for member in &plan.members[plan.roots..] {
            self.derive_member_helpers(member, true)?;
        }
        self.clear_metas();
        let source = self.eq_source(&plan);
        let mut result = self.derive_rebuild(&plan);
        self.clear_metas();
        result = result.and_then(|()| self.definitions(&source.tests));
        self.clear_metas();
        result = result.and_then(|()| self.definitions(&source.proofs));
        for (signature, equations) in &source.laws {
            self.clear_metas();
            result = result.and_then(|()| self.definition(signature, equations));
        }
        for (ri, (decide, instance)) in source.instances.into_iter().enumerate() {
            if own[ri] {
                continue;
            }
            for (signature, equations) in [decide, instance] {
                self.clear_metas();
                result = result.and_then(|()| self.definition(&signature, &equations));
            }
        }
        for (signature, equations) in source.readings {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&signature, &equations));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => refuse(self, format!("deriving it failed: {}", e.message)),
        }
        Ok(())
    }

    /// The types of `d`'s group (`d` alone, or the types defined together
    /// with it) and the containers of them that their fields have as types,
    /// and theirs, in the order they're found (the roots, then for each
    /// member its constructors' fields, then the next member's); or why
    /// not, with `label` what the note calls the derivation. A container is
    /// any earlier data type without indices that isn't a proposition: its
    /// member is built from its constructors. For `==` that is always right,
    /// since any two decisions of `x = y` agree. An order or a display must
    /// agree with the container's own instance, so with `instance` (the
    /// derived instance's member, `%instOrd`), a container other than
    /// `List`, `Option` and pairs must have that derived instance, not one
    /// its module wrote. Fields the plans refuse anyway (proofs, types,
    /// functions, a type that depends on an earlier field) are passed over.
    /// Every deriver finds the same members, in the same order, so
    /// `T.%m1%type` means one thing.
    pub(crate) fn members(
        &self,
        d: DataId,
        label: &str,
        instance: Option<&str>,
    ) -> Result<std::result::Result<Vec<Member>, String>> {
        let g = &self.ev();
        let group: Vec<DataId> = g.data(d).group().to_vec();
        let np = g.data(d).params().len();
        let mut members: Vec<Member> = group
            .iter()
            .map(|&r| Member {
                data: r,
                args: (0..np).map(Value::var).collect(),
                origin: String::new(),
                owner: r,
                prefix: "%".into(),
            })
            .collect();
        // How many containers each root owns so far.
        let mut owned: Vec<usize> = vec![0; group.len()];
        let mut next = 0;
        while next < members.len() {
            let here = &members[next];
            let (container, args, owner) = (here.data, here.args.clone(), here.owner);
            let root = next < group.len();
            let root_data = g.data(container);
            for ctor in root_data.ctors() {
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
                    let term = quote_internal(g, np, &value)?;
                    if !mentions_group(&term, &group) {
                        continue;
                    }
                    if member_of(g, np, &members, &value)?.is_some() {
                        continue;
                    }
                    let what = if !root {
                        members[next].origin.clone()
                    } else {
                        field_origin(root_data, ctor, field, group.len())
                    };
                    let inner = group
                        .iter()
                        .find(|r| mentions_group(&term, std::slice::from_ref(*r)))
                        .map(|r| g.data(*r).name().to_string())
                        .unwrap_or_default();
                    let refused =
                        |why: String| -> Result<std::result::Result<Vec<Member>, String>> {
                            Ok(Err(format!("{what} contains `{inner}` inside {why}")))
                        };
                    let Value::Data(e, cargs) = &value else {
                        return refused(format!(
                            "another type, and {label} is derived only through data types"
                        ));
                    };
                    let inside = g.data(*e);
                    let cname = inside.name().to_string();
                    // The kernel refuses this first (`E-POSITIVITY`: a group's
                    // type used inside another with different parameters), so
                    // it isn't reached today; kept as a guard against the
                    // member list growing without end.
                    if group.contains(e) {
                        return refused(format!(
                            "`{cname}` with other arguments, which {label} isn't derived for"
                        ));
                    }
                    if !inside.indices().is_empty() {
                        return refused(format!(
                            "`{cname}`, which has indices, and {label} is derived only through \
                             types without them"
                        ));
                    }
                    if inside.sort() == Sort::Prop {
                        return refused(format!("`{cname}`, which is a proposition"));
                    }
                    if let Some(instance) = instance
                        && !known_container(g, *e)
                        && !self.has_member(*e, instance)
                    {
                        // Which of the two reasons it is: an instance that
                        // exists although `%instOrd` doesn't was written, and
                        // otherwise the deriver's own reason, if it kept one.
                        let (interface, refusal) = if instance == "%instOrd" {
                            (interfaces::ord(self), self.tables.no_ord.get(e))
                        } else {
                            (interfaces::show(self), self.tables.no_show.get(e))
                        };
                        let wrote = interface.is_some_and(|i| self.has_written_instance(*e, i));
                        let why = if wrote {
                            "its module wrote one".to_string()
                        } else if let Some(reason) = refusal {
                            format!("it has none, since {reason}")
                        } else {
                            "it has none".to_string()
                        };
                        return refused(format!(
                            "`{cname}`, whose {label} isn't derived ({why}): {label} is derived \
                             through another type only when that type's is, so that the two agree"
                        ));
                    }
                    let owner_index = group.iter().position(|r| *r == owner).unwrap_or(0);
                    owned[owner_index] += 1;
                    members.push(Member {
                        data: *e,
                        args: cargs.to_vec(),
                        origin: what,
                        owner,
                        prefix: format!("%m{}%", owned[owner_index]),
                    });
                }
            }
            next += 1;
        }
        Ok(Ok(members))
    }

    /// Whether `==` can be derived for `d`'s group, and how; or why not.
    /// The same for a derived `Ord` (`derive_ord.rs`), with `interface` the
    /// one whose instances data fields need (proof fields always need
    /// `DecEq`), and `label` what the notes call it.
    pub(crate) fn field_plan(
        &mut self,
        d: DataId,
        interface: DataId,
        label: &str,
    ) -> Result<std::result::Result<Plan, String>> {
        let instance = if Some(interface) == interfaces::dec_eq(self) {
            None
        } else {
            Some("%instOrd")
        };
        self.field_plan_for(d, interface, label, true, instance)
    }

    /// [`Self::field_plan`], where `compare` says whether data fields are
    /// compared (needing instances, and not functions), and `instance` is
    /// what [`Self::members`] needs of a container. The generated
    /// extensionality lemma (`derive_ext.rs`) only states `x.f = y.f` for
    /// them, so it leaves those requirements out and keeps the rest, for
    /// `d` alone.
    pub(crate) fn field_plan_for(
        &mut self,
        d: DataId,
        interface: DataId,
        label: &str,
        compare: bool,
        instance: Option<&str>,
    ) -> Result<std::result::Result<Plan, String>> {
        let g = &self.ev();
        let group: Vec<DataId> = if compare {
            g.data(d).group().to_vec()
        } else {
            vec![d]
        };
        let np = g.data(d).params().len();
        for &r in &group {
            let data = g.data(r);
            let name = data.name().to_string();
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
        }
        // The group's types and the containers they're nested in, when
        // fields are compared.
        let members = if compare {
            match self.members(d, label, instance)? {
                Ok(members) => members,
                Err(why) => return Ok(Err(why)),
            }
        } else {
            vec![Member {
                data: d,
                args: (0..np).map(Value::var).collect(),
                origin: String::new(),
                owner: d,
                prefix: "%".into(),
            }]
        };
        let g = &self.ev();
        let first = g.data(d);
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = first.params().iter().map(|(_, t)| is_type(t)).collect();
        // Each field, classified; the types to find instances for are
        // checked below.
        let mut deciders = vec![false; np];
        let mut fields: Vec<Vec<Vec<Field>>> = Vec::new();
        // Each with whether it's a proof field's carrier (needing `DecEq`).
        let mut to_decide: Vec<(Value, String, bool)> = Vec::new();
        for &r in &group {
            let data = g.data(r);
            let mut root_fields = Vec::new();
            for ctor in data.ctors() {
                let mut kinds: Vec<Field> = Vec::new();
                for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                    let what = field_origin(data, ctor, field, group.len());
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
                                "the type of {what} mentions an earlier proof field, which \
                                 {label} isn't derived for yet"
                            )));
                        }
                        // The field's type with the parameters and the
                        // fields before it as variables.
                        let env: Vec<Value> = (0..np + i).map(Value::var).collect();
                        let value = force(g, eval(g, &env, ty)?)?;
                        let Value::Eq(carrier, _, _) = value else {
                            return Ok(Err(format!(
                                "{what} is a proof of something other than an equation, and \
                                 two values equal in their data can still differ there"
                            )));
                        };
                        let carrier_term = quote_internal(g, np + i, &carrier)?;
                        if let Some(&m) = group
                            .iter()
                            .find(|m| mentions_group(&carrier_term, std::slice::from_ref(*m)))
                        {
                            let name = g.data(m).name();
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
                            "the type of {what} depends on an earlier field, which {label} \
                             isn't derived for yet"
                        )));
                    }
                    // The field's type with the parameters as variables
                    // `0..np`.
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
                        Term::Data(e, args) => group.iter().position(|r| r == e).filter(|_| {
                            args.iter().enumerate().all(|(j, a)| {
                                matches!(a.strip_loc(), Term::Var(v) if *v == i + np - 1 - j)
                            })
                        }),
                        _ => None,
                    };
                    if let Some(m) = direct {
                        kinds.push(Field::Recursive(m));
                        continue;
                    }
                    if compare && mentions_group(ty, &group) {
                        match member_of(g, np, &members, &value)? {
                            Some(m) => kinds.push(Field::Recursive(m)),
                            None => {
                                return Ok(Err(format!(
                                    "{what} contains a type of the group inside another type, \
                                     which {label} isn't derived for yet"
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
                root_fields.push(kinds);
            }
            fields.push(root_fields);
        }
        // The containers' fields: a member again, or data with an instance.
        for member in members.iter().skip(group.len()) {
            let container = g.data(member.data);
            let mut member_fields = Vec::new();
            for ctor in container.ctors() {
                let mut kinds = Vec::new();
                for (i, (_, ty)) in ctor.fields.iter().enumerate() {
                    let what = &member.origin;
                    let inner = || {
                        group
                            .iter()
                            .find(|r| {
                                quote_internal(g, np, &member.ty())
                                    .is_ok_and(|t| mentions_group(&t, std::slice::from_ref(*r)))
                            })
                            .map(|r| g.data(*r).name().to_string())
                            .unwrap_or_default()
                    };
                    let container_name = container.name();
                    if ctor.field_erased[i] {
                        // As a root's proof field: an equation in a type
                        // with `DecEq` that doesn't depend on the other
                        // fields is left out; two values equal in their
                        // data can't differ there.
                        let in_container = |why: &str| {
                            Ok(Err(format!(
                                "{what} has `{}` inside `{container_name}`, whose proof field \
                                 {why}",
                                inner()
                            )))
                        };
                        if ctor.field_sorts[i] != Sort::Prop {
                            return in_container(&format!(
                                "is a type, which {label} can't compare"
                            ));
                        }
                        if (0..i).any(|j| kinds[j] == Field::Proof && ty.mentions(i - 1 - j)) {
                            return in_container(&format!(
                                "mentions an earlier proof field, which {label} isn't derived \
                                 for yet"
                            ));
                        }
                        let env: Vec<Value> = member
                            .args
                            .iter()
                            .cloned()
                            .chain((0..i).map(|j| Value::var(np + j)))
                            .collect();
                        let Value::Eq(carrier, _, _) = force(g, eval(g, &env, ty)?)? else {
                            return in_container(&format!(
                                "is a proof of something other than an equation, which {label} \
                                 can't tell apart"
                            ));
                        };
                        let carrier_term = quote_internal(g, np + i, &carrier)?;
                        if mentions_group(&carrier_term, &group) {
                            return in_container(&format!(
                                "is an equation in a type that mentions the group, and \
                                 {label} isn't derived for that"
                            ));
                        }
                        if (0..i).any(|j| carrier_term.mentions(j)) {
                            return in_container(&format!(
                                "is an equation in a type that depends on other fields, which \
                                 {label} isn't derived for yet"
                            ));
                        }
                        for j in 0..np {
                            if carrier_term.mentions(np + i - 1 - j) {
                                deciders[j] |= param_is_type[j];
                            }
                        }
                        to_decide.push(((*carrier).clone(), what.clone(), true));
                        kinds.push(Field::Proof);
                        continue;
                    }
                    if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                        return Ok(Err(format!(
                            "{what} has `{}` inside `{container_name}`, whose fields {label} \
                             can't compare",
                            inner(),
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
                    let term = quote_internal(g, np, &value)?;
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
            fields.push(member_fields);
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
        let name = self.kernel.data(d).name().to_string();
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
                    // The field's instance has an error: note it so a use of
                    // this type's instance waits for it, rather than saying
                    // "no instance" (SW-3078).
                    if e.code == "E-FAILED-DEPENDENCY" {
                        cx.e.note_derive_waiting(&group, interface);
                    }
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
        let roots = group.len();
        Ok(match why {
            Some(why) => Err(why),
            None => Ok(Plan {
                deciders,
                members,
                fields,
                roots,
            }),
        })
    }

    /// Declares `T.%tag : [params] -> T params -> Nat`.
    pub(crate) fn derive_tag(&mut self, d: DataId) -> Result<()> {
        self.derive_tag_in(d, d, "%tag")
    }

    /// A container member's helpers, unless declared already, in its
    /// owner `T`'s namespace under its prefix (`T.%m1%`): `T.%m1%type`, its
    /// type, a definition of the group's parameters (explicit) so source
    /// can name it; `T.%m1%tag` with two constructors or more; and, with
    /// `fields`, `T.%m1%C%k` for each field. The last two are over the
    /// container's own parameters, as `T.%tag` and `T.%C%k` are over `T`'s.
    pub(crate) fn derive_member_helpers(&mut self, member: &Member, fields: bool) -> Result<()> {
        let (d, prefix) = (member.owner, member.prefix.as_str());
        let ty_member = format!("{prefix}type");
        if !self.has_member(d, &ty_member) {
            let data = self.kernel.data(d);
            let np = data.params().len();
            let mut body = quote_internal(&self.ev(), np, &member.ty())?;
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
                    let ctor = &self.kernel.data(member.data).ctors()[c];
                    let name = format!("{prefix}{}%{k}", ctor.name);
                    if ctor.field_erased[k] {
                        // A proof field has no accessor, only its type.
                        let proof = format!("{prefix}{}%P%{k}", ctor.name);
                        if !self.has_member(d, &proof) {
                            self.derive_member_proof_type(member, c, k, &proof)?;
                        }
                    } else if !self.has_member(d, &name) {
                        self.derive_field_in(d, member.data, prefix, c, k)?;
                    }
                }
                self.derive_tuple_in(d, member.data, prefix, c)?;
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
        // An erased (proof or type) field has no value to read: its type
        // here would be a term over variables that aren't there, and the
        // accessor would be malformed. Callers give those `%P%` types
        // instead (`derive_proof_type`, `derive_member_proof_type`).
        if ctor.field_erased[k] {
            return Err(Diagnostic::error(
                "E-INTERNAL",
                format!(
                    "internal error: no accessor for the erased field {k} of `{}`",
                    ctor.name
                ),
            )
            .with_note("this is a bug in the compiler, not in your program"));
        }
        let env: Vec<Value> = (0..np)
            .map(Value::var)
            .chain((0..k).map(|_| unused()))
            .collect();
        let field = eval(g, &env, &ctor.fields[k].1)?;
        let params: Vec<Term> = (0..np).map(|j| Term::Var(np - j)).collect();
        let ty = Term::Pi(
            "default".into(),
            Icit::Explicit,
            Rc::new(quote_internal(g, np, &field)?),
            Rc::new(Term::Pi(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::data(d, params)),
                Rc::new(quote_internal(g, np + 2, &field)?),
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

    /// Declares, for constructor `c` of `D` (`d`, `T` itself or a container
    /// of it) whose fields are all data, its fields as nested pairs and
    /// back, in `T`'s (`owner`'s) namespace:
    ///
    /// ```text
    /// T.{prefix}C%unpack : [params] -> Pair A0 (Pair A1 … An) -> D params   -- C x0 … xn
    /// T.{prefix}C%pack : [params] -> (default : Pair A0 …) -> D params -> Pair A0 …
    /// ```
    ///
    /// `pack` gives the fields of a `C` and `default` for another
    /// constructor. With `Std.Pair.decMk`, they let derived proofs decide
    /// `C a… = C b…` as the equality of two tuples, carried back by one
    /// `Eq.cong` each way, instead of a conjunction read field by field
    /// (docs/proposals/derived-instances-rethink.md §3.2). Nothing is
    /// declared for a constructor without fields or with an erased one, or
    /// before the core's `Pair` exists.
    pub(crate) fn derive_tuple_in(
        &mut self,
        owner: DataId,
        d: DataId,
        prefix: &str,
        c: usize,
    ) -> Result<()> {
        let Some(pair) = self.kernel.env.registry().data(Builtin::Pair) else {
            return Ok(());
        };
        let g = &self.ev();
        let data = g.data(d);
        let np = data.params().len();
        let ctor = &data.ctors()[c];
        let n = ctor.fields.len();
        let unpack_name = format!("{prefix}{}%unpack", ctor.name);
        let pack_name = format!("{prefix}{}%pack", ctor.name);
        if n == 0 || ctor.field_erased.iter().any(|e| *e) || self.has_member(owner, &unpack_name) {
            return Ok(());
        }
        // Field `k`'s type, which mentions only the parameters (a data
        // field doesn't depend on earlier fields), at `depth`.
        let mut fields = Vec::with_capacity(n);
        for k in 0..n {
            let env: Vec<Value> = (0..np)
                .map(Value::var)
                .chain((0..k).map(|_| unused()))
                .collect();
            fields.push(eval(g, &env, &ctor.fields[k].1)?);
        }
        let tuple = |depth: usize| -> Result<Term> {
            let mut ty = quote_internal(g, depth, &fields[n - 1])?;
            for k in (0..n - 1).rev() {
                ty = Term::data(pair, vec![quote_internal(g, depth, &fields[k])?, ty]);
            }
            Ok(ty)
        };
        let params =
            |depth: usize| -> Vec<Term> { (0..np).map(|j| Term::Var(depth - 1 - j)).collect() };
        // unpack: in the context `params, p`, each pair is matched in turn,
        // adding its first part and the rest; the last part is the rest.
        let unpack_ty = Term::Pi(
            "p".into(),
            Icit::Explicit,
            Rc::new(tuple(np)?),
            Rc::new(Term::data(d, params(np + 1))),
        );
        let mut levels = Vec::with_capacity(n);
        let mut rest = np;
        let mut depth = np + 1;
        for _ in 0..n - 1 {
            levels.push(depth);
            rest = depth + 1;
            depth += 2;
        }
        levels.push(rest);
        let mut body = Term::ctor(
            d,
            c,
            levels.iter().map(|l| Term::Var(depth - 1 - l)).collect(),
        );
        for k in (0..n - 1).rev() {
            depth -= 2;
            let scrutinee = if k == 0 { np } else { depth - 1 };
            body = Term::Case(
                depth - 1 - scrutinee,
                pair,
                Rc::from([Branch {
                    names: vec![format!("x{k}").into(), "rest".into()],
                    body: Some(Rc::new(body)),
                }]),
            );
        }
        let unpack_body = Term::Lam("p".into(), Icit::Explicit, Rc::new(body));
        // pack: in the context `params, default, r`, a `C`'s fields paired
        // up, or `default`.
        let pack_ty = Term::Pi(
            "default".into(),
            Icit::Explicit,
            Rc::new(tuple(np)?),
            Rc::new(Term::Pi(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::data(d, params(np + 1))),
                Rc::new(tuple(np + 2)?),
            )),
        );
        let branches: Vec<Branch> = data
            .ctors()
            .iter()
            .enumerate()
            .map(|(other, o)| {
                let m = o.fields.len();
                let body = if other == c {
                    let mut t = Term::Var(0);
                    for k in (0..n - 1).rev() {
                        t = Term::ctor(pair, 0, vec![Term::Var(n - 1 - k), t]);
                    }
                    t
                } else {
                    Term::Var(m + 1)
                };
                Branch {
                    body: Some(Rc::new(body)),
                    names: o.fields.iter().map(|(x, _)| x.clone()).collect(),
                }
            })
            .collect();
        let pack_body = Term::Lam(
            "default".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::Case(0, d, branches.into())),
            )),
        );
        self.declare_member(owner, d, &unpack_name, unpack_ty, unpack_body)?;
        self.declare_member(owner, d, &pack_name, pack_ty, pack_body)
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
            reg.def(Builtin::VoidImpossible),
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
                Rc::new(quote_internal(g, np + 2, &field)?),
            )),
        );
        let mut branches = Vec::new();
        for (other, o) in data.ctors().iter().enumerate() {
            let n = o.fields.len();
            let body = if other == c {
                Term::Var(n - 1 - k)
            } else {
                // `Nat.equalFalse other c byComputing h : Void`, `h` read as `other = c`.
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
                        quote_internal(g, np + 2 + n, &field)?,
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
    pub(crate) fn derive_rebuild(&mut self, plan: &Plan) -> Result<()> {
        // Everything `at` and `view` are built from, checked once: a missing
        // one skips the whole rebuild, since each generator below expects
        // the earlier pieces to be declared.
        let reg = self.kernel.env.registry();
        if reg.data(Builtin::Nat).is_none()
            || reg.def(Builtin::VoidAbsurd).is_none()
            || reg.def(Builtin::VoidImpossible).is_none()
            || reg.def(Builtin::NatNeq).is_none()
        {
            return Ok(());
        }
        for (m, member) in plan.members.iter().enumerate() {
            let (d, matched, prefix) = (member.owner, member.data, member.prefix.clone());
            let shapes: Vec<(String, usize)> = self
                .kernel
                .data(matched)
                .ctors()
                .iter()
                .map(|c| (c.name.to_string(), c.fields.len()))
                .collect();
            if shapes.len() < 2 || self.member_def(d, &format!("{prefix}tag")).is_none() {
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
                for definition in self.eta_source(plan, m) {
                    self.clear_metas();
                    self.definition(&definition.0, &definition.1)?;
                }
                self.clear_metas();
            }
        }
        Ok(())
    }

    /// The source-name prefix of `member`'s generated names: `T.%` for a
    /// root `T` (`T.%same`, `T.%tag`), `T.%m1%` for its first container
    /// (`T.%m1%same`, `T.%m1%tag`, `T.%m1%Cons%0`).
    pub(crate) fn member_names(&self, member: &Member) -> String {
        let owner = self.relative_to_root(self.kernel.data(member.owner).name());
        format!("{owner}.{}", member.prefix)
    }

    /// A member's type matched on, how source names its constructors, and
    /// its type as source: `T %p0 …` for a root, `T.%m1%type %p0 …` for a
    /// container.
    pub(crate) fn member_shape(
        &self,
        s: &crate::derive_ord::Src,
        member: &Member,
    ) -> (DataId, String, Expr) {
        let data = self.kernel.data(member.data);
        if member.is_root() {
            let ty_name = self.relative_to_root(data.name());
            let this = s.this(&ty_name, data);
            (member.data, ty_name, this)
        } else {
            let np = self.kernel.data(member.owner).params().len();
            let this = s.app(
                s.var(&format!("{}type", self.member_names(member))),
                (0..np).map(|j| s.var(&format!("%p{j}"))).collect(),
            );
            // `Std.List`, or a program's type as this module writes it.
            let written = if data.path().starts_with("Std.") {
                data.path().to_string()
            } else {
                self.relative_to_root(data.name())
            };
            (member.data, written, this)
        }
    }

    /// The source of member `m`'s `eta` and `etaAt` ([`Self::derive_rebuild`]).
    fn eta_source(&self, plan: &Plan, m: usize) -> Vec<(Decl, Vec<Decl>)> {
        let data = self.kernel.data(plan.members[0].data);
        let s = crate::derive_ord::Src { span: data.span() };
        let np = data.params().len();
        let prefix = self.member_names(&plan.members[m]);
        let (matched, ctor_prefix, this) = self.member_shape(&s, &plan.members[m]);
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
                    vec![
                        s.var("%s"),
                        call(&tag, vec![s.var("%s")]),
                        s.var("byComputing"),
                    ],
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
                s.equation(&eta, vec![pattern], s.var("byComputing"))
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

    /// Declares `T.%m1%C%P%k : (group params) -> (fields before k) -> Prop`,
    /// the type of a container member's proof field `k` of constructor `c`,
    /// named `proof`: the container's own fields, at the member's arguments.
    fn derive_member_proof_type(
        &mut self,
        member: &Member,
        c: usize,
        k: usize,
        proof: &str,
    ) -> Result<()> {
        let g = &self.ev();
        let owner = g.data(member.owner);
        let np = owner.params().len();
        let ctor = &g.data(member.data).ctors()[c];
        let at = |i: usize| -> Result<Term> {
            let env: Vec<Value> = member
                .args
                .iter()
                .cloned()
                .chain((0..i).map(|j| Value::var(np + j)))
                .collect();
            Ok(quote_internal(
                g,
                np + i,
                &eval(g, &env, &ctor.fields[i].1)?,
            )?)
        };
        let mut binders: Vec<(Name, Term)> = owner.params().to_vec();
        for i in 0..k {
            binders.push((ctor.fields[i].0.clone(), at(i)?));
        }
        let mut ty = Term::Sort(Sort::Prop);
        let mut body = at(k)?;
        for (x, t) in binders.iter().rev() {
            ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(t.clone()), Rc::new(ty));
            body = Term::Lam(x.clone(), Icit::Explicit, Rc::new(body));
        }
        let name: Name = format!("{}.{proof}", owner.name()).into();
        let span = owner.span();
        let data_key = self.data_key(member.owner);
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
        let key = Self::member_key(&data_key, proof);
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

    /// The source of `T.%same`, its proofs and `T.%instDecEq` for each type
    /// `T` of the group; for a nested type, also `T.%m1%same` and its
    /// proofs for each container it's in, the `same`s defined together.
    fn eq_source(&self, plan: &Plan) -> Source {
        let data = self.kernel.data(plan.members[0].data);
        let span = data.span();
        let src = crate::derive_ord::Src { span };
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
            name: n(x),
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
        let names: Vec<String> = plan.members.iter().map(|m| self.member_names(m)).collect();
        let same_of = |m: usize| format!("{}same", names[m]);
        let sound_of = |m: usize| format!("{}sameSound", names[m]);
        let complete_of = |m: usize| format!("{}sameComplete", names[m]);
        let iff_of = |m: usize| format!("{}sameIff", names[m]);
        let iff = |a: Expr, b: Expr| apps(var("Std.Iff"), vec![a, b]);
        let record = |fields: Vec<(&str, Expr)>| Expr::Record {
            base: None,
            fields: fields.into_iter().map(|(f, e)| (n(f), e)).collect(),
            span,
        };
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
        let mut tests = Vec::new();
        let mut proofs = Vec::new();
        let mut laws = Vec::new();
        let mut readings = Vec::new();
        for (m, prefix) in names.iter().enumerate() {
            let prefix = prefix.clone();
            // The type matched on, how source names its constructors, and
            // the member's type: `T %p0 …`, or `T.%m1%type %p0 …`.
            let (matched, ctor_prefix, this) = self.member_shape(&src, &plan.members[m]);
            let ctors = self.kernel.data(matched).ctors();
            let member_fields = plan.member_fields(m);

            // T.%same : … -> (%r %s : T %p0 …) -> Bool, and its two proofs.
            let pair = |cod: Expr| {
                with_params(
                    ["%s", "%r"].into_iter().fold(cod, |cod, who| Expr::Pi {
                        name: n(who),
                        implicit: false,
                        auto: false,
                        dom: Box::new(this.clone()),
                        cod: Box::new(cod),
                        span,
                    }),
                    true,
                )
            };
            let same_name = n(&same_of(m));
            let sound_name = n(&sound_of(m));
            let complete_name = n(&complete_of(m));
            let iff_name = n(&iff_of(m));
            let same_test = apps(var(&same_name.text), vec![var("%r"), var("%s")]);
            let is_true = eq(same_test, var("Std.Bool.True"));
            let same_signature = signature(&same_name, pair(var("Std.Bool")), false);
            let iff_signature = signature(
                &iff_name,
                pair(iff(is_true.clone(), eq(var("%r"), var("%s")))),
                false,
            );
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
            let mut iff_equations = Vec::new();
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
                let tupled = self.has_member(
                    plan.members[m].owner,
                    &format!("{}{}%unpack", plan.members[m].prefix, ctor.name),
                );
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
                            let call = |f: &str, x: &str| {
                                let law = apps(var(&iff_of(target)), vec![var(&a(k)), var(&b(k))]);
                                apps(var(f), vec![law, var(x)])
                            };
                            Expr::Record {
                                base: None,
                                fields: vec![
                                    (
                                        n("holds"),
                                        apps(var(&same_of(target)), vec![var(&a(k)), var(&b(k))]),
                                    ),
                                    (n("sound"), lam(&["%x"], call("Std.Iff.forward", "%x"))),
                                    (n("complete"), lam(&["%x"], call("Std.Iff.backward", "%x"))),
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
                    // `C %a… = C %b…` as `MkPair %a0 (MkPair %a1 …) = MkPair %b0 …`,
                    // decided by `Pair.decMk` a field at a time and carried
                    // back by `T.%C%unpack`, when the constructor has them.
                    let tuple = |x: &dyn Fn(usize) -> String, from: usize| {
                        let mut t = var(&x(data_fields[last]));
                        for &k in data_fields[from..last].iter().rev() {
                            t = apps(var("Std.Pair.MkPair"), vec![var(&x(k)), t]);
                        }
                        t
                    };
                    let unpack = format!("{prefix}{}%unpack", ctor.name);
                    let whole = if data_fields.is_empty() {
                        apps(var("Std.Decidable.yes"), vec![proof])
                    } else if tupled {
                        let mut all = decision(data_fields[last]);
                        for (i, &k) in data_fields[..last].iter().enumerate().rev() {
                            all = apps(
                                var("Std.Pair.decMk"),
                                vec![
                                    var(&a(k)),
                                    var(&b(k)),
                                    tuple(&a, i + 1),
                                    tuple(b, i + 1),
                                    decision(k),
                                    all,
                                ],
                            );
                        }
                        let pack = apps(
                            var(&format!("{prefix}{}%pack", ctor.name)),
                            vec![tuple(&a, 0)],
                        );
                        let cong =
                            |f: Expr| lam(&["%e"], apps(var("Std.Eq.cong"), vec![f, var("%e")]));
                        apps(
                            var("Std.Decidable.map"),
                            vec![all, cong(var(&unpack)), cong(pack)],
                        )
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
                // Both directions from one decision `%d` of `C %a… = C %b…`.
                let both_ways = |b: &dyn Fn(usize) -> String| {
                    let laws = record(vec![
                        ("forward", apps(var("Std.Decidable.sound"), vec![var("%d")])),
                        (
                            "backward",
                            apps(var("Std.Decidable.complete"), vec![var("%d")]),
                        ),
                    ]);
                    let_in(span, "%d", None, whole(b), laws)
                };
                if ctors.len() == 1 {
                    let both = |extra| with(pattern(&b), extra);
                    let by_b = |k: usize| var(&b(k));
                    same_equations.push(equation(&same_name, both(None), tests(&by_b)));
                    iff_equations.push(equation(&iff_name, both(None), both_ways(&b)));
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
                // T.%sameIff (C %a0 …) %s =
                //   let %k : T.%tag %s = c -> Iff (T.%same (C %a0 …) %s = True) (C %a0 … = %s) := %e =>
                //     let %b0 := T.%C%0%at %s %e …
                //     J (%y %q => Iff (T.%same (C %a0 …) %y = True) (C %a0 … = %y))
                //       (let %d := (… : Decidable (C %a0 … = C %b0 …)); { forward = Decidable.sound %d, … })
                //       (T.%etaAt %s c %e)
                //   { forward = %h => (%k (Eq.sym (DecEq.tagsSame c (T.%tag %s) %h))).forward %h,
                //     backward = %x => (%k (Eq.sym (Eq.cong T.%tag %x))).backward %x }
                let first = Expr::Ann(
                    Box::new(apps(
                        var(&ctor_name),
                        (0..count).map(|k| var(&a(k))).collect(),
                    )),
                    Box::new(this.clone()),
                    span,
                );
                let claim = |y: Expr| {
                    iff(
                        eq(
                            apps(var(&same_name.text), vec![first.clone(), y.clone()]),
                            var("Std.Bool.True"),
                        ),
                        eq(first.clone(), y),
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
                let mut at_c = apps(
                    var("J"),
                    vec![lam(&["%y", "%q"], claim(var("%y"))), both_ways(&b), eta_at],
                );
                for k in (0..count).rev() {
                    let field = format!("{prefix}{}%{k}%at", ctor.name);
                    at_c = let_in(
                        span,
                        &b(k),
                        None,
                        apps(var(&field), vec![var("%s"), var("%e")]),
                        at_c,
                    );
                }
                let at_c_ty = Expr::Arrow(
                    Box::new(eq(tag_s.clone(), number.clone())),
                    Box::new(claim(var("%s"))),
                );
                let flipped = |e: Expr| apps(var("Std.Eq.flipped"), vec![e]);
                let tag_of_x = apps(
                    var("Std.Eq.cong"),
                    vec![lam(&["%z"], apps(var(&tag), vec![var("%z")])), var("%x")],
                );
                let direction = |field: &str, tags: Expr, x: &str| {
                    let law = apps(var(field), vec![apps(var("%k"), vec![flipped(tags)])]);
                    lam(&[x], apps(law, vec![var(x)]))
                };
                let body = record(vec![
                    ("forward", direction("Std.Iff.forward", tags_same, "%h")),
                    ("backward", direction("Std.Iff.backward", tag_of_x, "%x")),
                ]);
                let body = let_in(span, "%k", Some(at_c_ty), lam(&["%e"], at_c), body);
                iff_equations.push(equation(&iff_name, with(second(), None), body));
            }
            tests.push((same_signature, same_equations));
            proofs.push((iff_signature, iff_equations));
            // T.%sameSound %r %s %h = (T.%sameIff %r %s).forward %h, and
            // T.%sameComplete likewise.
            let by_iff = |name: &ast::Name, sig: Decl, field: &str, x: &str| {
                let law = apps(
                    var(field),
                    vec![apps(var(&iff_name.text), vec![var("%r"), var("%s")])],
                );
                let equation = Decl::Equation {
                    guard: None,
                    name: name.clone(),
                    patterns: ["%r", "%s", x].iter().map(|v| Pattern::Var(n(v))).collect(),
                    rhs: Some(apps(law, vec![var(x)])),
                    arm: None,
                    span,
                };
                (sig, vec![equation])
            };
            laws.push(by_iff(
                &sound_name,
                sound_signature,
                "Std.Iff.forward",
                "%h",
            ));
            laws.push(by_iff(
                &complete_name,
                complete_signature,
                "Std.Iff.backward",
                "%e",
            ));
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
                    Expr::Binary(
                        BinOp::Ne(NeForm::Unicode),
                        Box::new(var("%r")),
                        Box::new(var("%s")),
                    ),
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
        let mut instances = Vec::new();
        for m in 0..plan.roots {
            let (_, ty_name, this) = self.member_shape(&src, &plan.members[m]);
            let decision = Expr::Record {
                base: None,
                fields: vec![
                    (n("holds"), by(same_of(m))),
                    (n("sound"), by(sound_of(m))),
                    (n("complete"), by(complete_of(m))),
                ],
                span,
            };
            let decide_name = n(&format!("{ty_name}.%decide"));
            let decide_ty = with_params(
                ["%s", "%r"].into_iter().fold(
                    apps(var("Std.Decidable"), vec![eq(var("%r"), var("%s"))]),
                    |cod, who| Expr::Pi {
                        name: n(who),
                        implicit: false,
                        auto: false,
                        dom: Box::new(this.clone()),
                        cod: Box::new(cod),
                        span,
                    },
                ),
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
            let instance_ty = with_params(apps(var("Std.DecEq"), vec![this]), true);
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
            instances.push((decide, instance));
        }
        Source {
            tests,
            proofs,
            laws,
            instances,
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
        name: n(x),
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
    let mut proof = var("byComputing");
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

/// A signature and its equations.
type Definition = (Decl, Vec<Decl>);

/// The source [`Elaborator::eq_source`] generates.
struct Source {
    /// `T.%same`, then each container's, defined together.
    tests: Vec<(Decl, Vec<Decl>)>,
    /// `T.%sameIff`, then each container's, defined together after the
    /// tests, which their types mention.
    proofs: Vec<(Decl, Vec<Decl>)>,
    /// `T.%sameSound` and `T.%sameComplete`, then each container's: the two
    /// directions of `T.%sameIff`.
    laws: Vec<(Decl, Vec<Decl>)>,
    /// For each type `T` of the group: `T.%decide`, the decision made of
    /// `T.%same` and its proofs, and `T.%instDecEq`.
    instances: Vec<(Definition, Definition)>,
    /// `T.%sameReads` and `T.%sameReadsFalse`, then each container's: the
    /// readings of the tests, filed once the instance is.
    readings: Vec<(Decl, Vec<Decl>)>,
}
