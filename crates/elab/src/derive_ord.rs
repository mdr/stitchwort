//! A derived `Ord` instance for data types and records declared in a
//! program (docs/proposals/interfaces.md §5.11, stage 7): `T.%instOrd`,
//! `Ord.fromCompare` of `T.%compare` and its three laws. Generated as source,
//! like the derived `DecEq` (`derive.rs`) and `Show` (`derive_show.rs`), and
//! elaborated like any definition, so the kernel checks the proofs.
//!
//! The order is lexicographic: constructors in the order they're declared
//! (by `T.%tag`, their position), then the data fields in order. Proof fields
//! are left out (D179), as for `DecEq`. It's derived where `DecEq` is, with
//! `Ord` for the data fields instead (a field of type `T` itself is a
//! recursive call), and `[auto ord: Ord a]` for each parameter that's a type
//! the fields use; `Ord`'s `eq` is `T`'s own `DecEq` instance. When `T`'s
//! module declares that instance by hand, `Ord` is derived once the instance
//! is checked (`derive_pending_ord`), so it is known to whatever is checked
//! after it. Why not is kept for the note when an `Ord` is needed for `T`.
//!
//! The laws are put together from lemmas in the core, proved once
//! (`Ordering.thenPairEqual`, `Ordering.thenFlip`, `Ord.thenTrans`,
//! `Ordering.tagsTrans`, …): each constructor's case follows its fields, one
//! lemma per field. `equal` proves the fields' nested pairs equal and
//! carries that back with `T.%C%unpack`, as `==` does (`derive.rs`); a
//! constructor with proof fields uses `Ordering.thenEqual` and `J`s instead.
//! `trans`, and `equal` with two constructors or more, find each field's
//! `Ord` instance once, `let %o0 := Ord.instanceFor %a0`, and pass it by
//! name (`[ord := %o0]`): found again under each field's hypotheses, the
//! search cost more with every field. With two constructors or more the tags are compared
//! first, and the fields only for the same constructor, so only the first
//! value is matched and each law has one equation per constructor, not one
//! per pair (docs/proposals/derived-equality.md §5.6). For
//! `type T a = | C1 … | C2 x y | …`, with `x: Nat` and `y: T a`:
//!
//! ```text
//! T.%compare : [a : _] -> [auto ord: Ord a] -> (%r %s : T a) -> Ordering
//! T.%compare r s = if Nat.equal (T.%tag r) (T.%tag s) then T.%fields r s else Nat.compare (T.%tag r) (T.%tag s)
//! T.%fields (C2 a0 a1) s = Ordering.andThen (Ord.compare a0 (T.%C2%0 a0 s)) (T.%compare a1 (T.%C2%1 a1 s))
//! …   -- one equation for each constructor
//!
//! T.%equal : … -> (%r %s : T a) -> T.%compare r s = Equal -> r = s
//! T.%flip : … -> (%r %s : T a) -> T.%compare s r = Ordering.flip (T.%compare r s)
//! T.%trans : … -> (%r %s %u : T a) -> T.%compare r s = Less -> T.%compare s u = Less -> T.%compare r u = Less
//!
//! instance T.%instOrd : … -> Ord (T a) := Ord.fromCompare T.%compare T.%equal T.%flip T.%trans
//! ```
//!
//! `if`, not `Ordering.andThen` of the tags' comparison, so a run compares
//! the fields only when the tags are equal. `Ordering.tagsEqual`,
//! `tagsFlip` and `tagsTrans` deal with the tags: where they differ,
//! `Nat.compare`'s laws decide; where they're equal, the law's equation
//! for `C2 a0 a1` is given `T.%tag s = 1` (and `T.%tag u = 1`), and
//! `T.%etaAt` (`derive.rs`) turns `s` into `C2 b0 b1`, its fields read by
//! `T.%C2%k%at`, so the fields' laws apply as when both values are matched.
//! With one constructor both values are matched, as `T.%compare (C a0 a1)
//! (C b0 b1)`. An enumeration (no fields at all) is just its tags:
//! `T.%compare r s = Nat.compare (T.%tag r) (T.%tag s)`, with `Nat`'s laws,
//! and `equal` is `T.%etaAt` of `Nat.compareEqual`.
//!
//! A nested type gets `T.%m1%compare` and its laws for each container it's
//! in, as `DecEq` does (`derive.rs`), each kind defined together with `T`'s:
//! `List`'s constructors in order (`Nil` first) then its fields is
//! `List.compareLex`, and likewise `Option.compareWith` and
//! `Pair.compareWith`, so a nested list compares as a list. Through another
//! container it's derived only when the container's `Ord` is derived too,
//! which is the same order. Types defined together are derived together,
//! unless one of them has its own `Ord` or `DecEq`.

use stitchwort_core::DataId;
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Bracket, Decl, Expr, Pattern};

use num_bigint::BigUint;

use crate::derive::{Derivation, Field, Plan, fields_equal, let_in};
use crate::module::Status;
use crate::{Elaborator, Global, Result, interfaces};

type Definition = (Decl, Vec<Decl>);

impl Elaborator {
    /// After data type or record `d` is admitted, and its `DecEq` derived:
    /// its `Ord` instance, if one can be derived, or else why not. The
    /// types of a group are derived together, once the last of them is
    /// admitted.
    pub(crate) fn derive_data_ord(&mut self, d: DataId) -> Result<()> {
        let data = self.kernel.data(d);
        let generated = !data.record() && data.ctors().iter().any(|c| c.name.starts_with('%'));
        let (Some(ord), Some(dec_eq)) = (interfaces::ord(self), interfaces::dec_eq(self)) else {
            return Ok(());
        };
        if generated || data.group().last() != Some(&d) {
            return Ok(());
        }
        let (group, own) = self.group_and_own(d, ord);
        if own.iter().all(|x| *x) {
            return Ok(());
        }
        let refuse =
            |e: &mut Self, why: String| e.refuse_group(Derivation::Ord, &group, &own, &why);
        // `Ord`'s `eq` is `T`'s `DecEq` instance, found when the instance is
        // built.
        if let Some(why) = group.iter().find_map(|r| self.tables.no_eq.get(r)) {
            let why = format!("`Ord` needs `==`, which isn't derived for it: {why}");
            refuse(self, why);
            return Ok(());
        }
        // A type's own `DecEq` instance is checked after the types it uses,
        // and `Ord`'s `eq` is that instance: only that type's `Ord`
        // instance waits for it (`derive_pending_ord`), a single type's
        // whole derivation too, since nothing else needs it.
        let mut waiting = vec![false; group.len()];
        if group.len() > 1 {
            // The derived orders of the group call each other's, so one
            // written by hand would leave them disagreeing with it.
            for (&r, &own_ord) in group.iter().zip(&own) {
                if own_ord {
                    let why = format!(
                        "`{}`, defined together with it, has its module's own `Ord` instance, \
                         which the derived orders of the group can't use; declare `Ord` for \
                         the others too",
                        self.kernel.data(r).name()
                    );
                    refuse(self, why);
                    return Ok(());
                }
            }
            for (ri, &r) in group.iter().enumerate() {
                waiting[ri] = self.declares_instance_for(r, dec_eq);
            }
        } else if self.declares_instance_of(dec_eq) {
            if let Some(item) = self.unit.module.item {
                self.unit.module.ord_after_dec_eq.insert(item, d);
            }
            self.tables.no_ord.insert(
                &self.session.owners,
                d,
                "its module's own `DecEq` instance, which `Ord` needs, uses this, so it isn't \
                 checked yet here; declare an `Ord` instance too"
                    .into(),
            );
            return Ok(());
        }
        for (&r, _) in group.iter().zip(&waiting).filter(|(_, w)| **w) {
            if let Some(item) = self.item_of(r) {
                self.unit.module.ord_after_dec_eq.insert(item, r);
            }
            self.tables.no_ord.insert(
                &self.session.owners,
                r,
                "its module's own `DecEq` instance, which `Ord` needs, uses this, so it isn't \
                 checked yet here; declare an `Ord` instance too"
                    .into(),
            );
        }
        self.derive_ord_with_eq(d, &waiting)
    }

    /// After the items of `component` are checked: `Ord` for each data type
    /// whose own `DecEq` instance is among them, if that instance checked.
    pub(crate) fn derive_pending_ord(&mut self, component: &[usize]) -> Result<()> {
        let Some(dec_eq) = interfaces::dec_eq(self) else {
            return Ok(());
        };
        for &instance in component {
            let info = &self.unit.module.items[instance];
            if !info.instance || info.interface != Some(Global::Data(dec_eq)) {
                continue;
            }
            let Some(Global::Unchecked(data_item)) = info.head else {
                continue;
            };
            let Some(d) = self.unit.module.ord_after_dec_eq.remove(&data_item) else {
                continue;
            };
            let status = self.unit.module.items[instance].status;
            if status != Status::Checked {
                let what = if status == Status::Unfinished {
                    "isn't finished: it, or something it uses, has an open goal (`?`)"
                } else {
                    "didn't check"
                };
                let why = format!(
                    "`Ord` needs `==`, and its module's own `DecEq` instance `{}` {what}",
                    self.unit.module.items[instance].name
                );
                self.tables.no_ord.insert(&self.session.owners, d, why);
                continue;
            }
            // A group whose orders weren't derived keeps its reason.
            if self.kernel.data(d).group().len() > 1 && !self.has_member(d, "%compare") {
                continue;
            }
            self.tables.no_ord.remove(&self.session.owners, &d);
            let item = self.unit.module.item.replace(data_item);
            let result = if self.kernel.data(d).group().len() > 1 {
                self.unnoted(|e| e.derive_ord_instance(d))
            } else {
                self.unnoted(|e| e.derive_ord_with_eq(d, &[false]))
            };
            self.unit.module.item = item;
            result?;
        }
        Ok(())
    }

    /// `Ord` for `d`'s group, using its `DecEq` instances, which are known
    /// by now, except for the types with `waiting` set (one per type of the
    /// group), whose own are still to be checked: their `%instOrd` is left
    /// for [`Self::derive_ord_instance`].
    fn derive_ord_with_eq(&mut self, d: DataId, waiting: &[bool]) -> Result<()> {
        let Some(ord) = interfaces::ord(self) else {
            return Ok(());
        };
        let group: Vec<DataId> = self.kernel.data(d).group().to_vec();
        let plan = match self.field_plan(d, ord, "`Ord`")? {
            Ok(plan) => plan,
            Err(why) => {
                for &r in &group {
                    self.tables
                        .no_ord
                        .insert(&self.session.owners, r, why.clone());
                }
                return Ok(());
            }
        };
        // The helpers `DecEq` declares, in case it didn't (its module wrote
        // its own instance).
        for (ri, &r) in group.iter().enumerate() {
            let ctors = self.kernel.data(r).ctors().len();
            if ctors > 1 && !self.has_member(r, "%tag") {
                self.derive_tag(r)?;
            }
            for c in 0..ctors {
                for (k, field) in plan.fields[ri][c].iter().enumerate() {
                    let name = format!("%{}%", self.kernel.data(r).ctors()[c].name);
                    if *field == Field::Proof {
                        if !self.has_member(r, &format!("{name}P%{k}")) {
                            self.derive_proof_type(r, c, k)?;
                        }
                    } else if ctors > 1 && !self.has_member(r, &format!("{name}{k}")) {
                        self.derive_field(r, c, k)?;
                    }
                }
            }
        }
        for member in &plan.members[plan.roots..] {
            self.derive_member_helpers(member, true)?;
        }
        let mut result = self.derive_rebuild(&plan);
        for definitions in self.ord_source(&plan, waiting) {
            self.clear_metas();
            result = result.and_then(|()| self.definitions(&definitions));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => {
                for &r in &group {
                    self.tables.no_ord.insert(
                        &self.session.owners,
                        r,
                        format!("deriving it failed: {}", e.message),
                    );
                }
            }
        }
        Ok(())
    }

    /// `T.%instOrd` for the type `d` of a group whose derived orders are
    /// declared, once its own `DecEq` instance is checked.
    fn derive_ord_instance(&mut self, d: DataId) -> Result<()> {
        let Some(ord) = interfaces::ord(self) else {
            return Ok(());
        };
        let group: Vec<DataId> = self.kernel.data(d).group().to_vec();
        let Some(at) = group.iter().position(|r| *r == d) else {
            return Ok(());
        };
        let plan = match self.field_plan(d, ord, "`Ord`")? {
            Ok(plan) => plan,
            Err(_) => return Ok(()),
        };
        let definition = self.ord_instance_source(&plan, at);
        self.clear_metas();
        let result = self.definitions(&[definition]);
        self.clear_metas();
        match result {
            Ok(()) => Ok(()),
            Err(e) if crate::undo::fatal(&e) => Err(e),
            Err(e) => {
                self.tables.no_ord.insert(
                    &self.session.owners,
                    d,
                    format!("deriving it failed: {}", e.message),
                );
                Ok(())
            }
        }
    }

    /// The module item that declares data type `d`, found by its key.
    fn item_of(&self, d: DataId) -> Option<usize> {
        if self.kernel.data(d).group().len() == 1 {
            return self.unit.module.item;
        }
        let key = self.data_key(d);
        self.unit
            .module
            .item_keys
            .iter()
            .find(|(_, k)| **k == key)
            .map(|(i, _)| *i)
    }

    /// Whether `T.member` is declared.
    pub(crate) fn has_member(&self, d: DataId, member: &str) -> bool {
        let key = Self::member_key(&self.data_key(d), member);
        self.scope.get(&key).is_some()
    }

    /// The source of `T.%compare` (with `T.%fields`), `T.%equal`,
    /// `T.%flip`, `T.%trans` and `T.%instOrd`, in that order, as groups of
    /// definitions admitted together, for each type `T` of the group. For a
    /// nested type, each container it's in gets its own `T.%m1%compare` and
    /// the rest, in the group of `T`'s.
    fn ord_source(&self, plan: &Plan, waiting: &[bool]) -> Vec<Vec<Definition>> {
        let mut groups: Vec<Vec<Definition>> = vec![Vec::new(); 4];
        for m in 0..plan.members.len() {
            for (kind, definition) in self.ord_member_source(plan, m) {
                groups[kind].push(definition);
            }
        }
        for m in (0..plan.roots).filter(|m| !waiting.get(*m).copied().unwrap_or(false)) {
            groups.push(vec![self.ord_instance_source(plan, m)]);
        }
        groups
    }

    /// `T.%instOrd`, for root `m` of the plan.
    fn ord_instance_source(&self, plan: &Plan, m: usize) -> Definition {
        let data = self.kernel.data(plan.members[0].data);
        let s = Src { span: data.span() };
        let (_, ty_name, this) = self.member_shape(&s, &plan.members[m]);
        let member = |m: &str| format!("{ty_name}.%{m}");
        let with_params = ord_params(&s, data, plan);
        // instance T.%instOrd : … -> Std.Ord (T %p0 …) :=
        //   Std.Ord.fromCompare T.%compare T.%equal T.%flip T.%trans
        let instance = format!("{ty_name}.%instOrd");
        let ty = with_params(s.app(s.var("Std.Ord"), vec![this]));
        let body = s.app(
            s.var("Std.Ord.fromCompare"),
            ["compare", "equal", "flip", "trans"]
                .iter()
                .map(|x| s.var(&member(x)))
                .collect(),
        );
        (
            s.signature(&instance, ty, true),
            vec![s.equation(&instance, Vec::new(), body)],
        )
    }

    /// Member `m`'s `compare` (with `fields`, for two constructors or more,
    /// not all without fields) (0), `equal` (1), `flip` (2) and `trans` (3),
    /// each with its kind.
    fn ord_member_source(&self, plan: &Plan, m: usize) -> Vec<(usize, Definition)> {
        let data = self.kernel.data(plan.members[0].data);
        let s = Src { span: data.span() };
        let np = data.params().len();
        let names: Vec<String> = plan.members.iter().map(|m| self.member_names(m)).collect();
        let prefix = names[m].clone();
        // The type matched on, how source names its constructors, and the
        // member's type: `T %p0 …`, or `T.%m1%type %p0 …`.
        let (matched, ctor_prefix, this) = self.member_shape(&s, &plan.members[m]);
        let ctor_list = self.kernel.data(matched).ctors();
        let member_fields = plan.member_fields(m);
        let ctors = ctor_list.len();
        let enumeration = ctors > 1 && ctor_list.iter().all(|c| c.fields.is_empty());
        let tagged = ctors > 1 && !enumeration;
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let c = |k: usize| format!("%c{k}");
        let of = |t: usize, f: &str| format!("{}{f}", names[t]);
        let (compare, fields_of, equal, flip, trans) = (
            of(m, "compare"),
            of(m, "fields"),
            of(m, "equal"),
            of(m, "flip"),
            of(m, "trans"),
        );
        let with_params = ord_params(&s, data, plan);
        let values =
            |names: &[&str], cod: Expr| with_params(s.pi(names, false, false, this.clone(), cod));
        let call =
            |f: &str, args: &[&str]| s.app(s.var(f), args.iter().map(|x| s.var(x)).collect());
        let tag_name = format!("{prefix}tag");
        let tag = |x: &str| call(&tag_name, &[x]);
        let tags = |f: &str, xs: &[&str]| s.app(s.var(f), xs.iter().map(|x| tag(x)).collect());
        let ordering = |c: &str| s.var(&format!("Std.Ordering.{c}"));
        let less = || ordering("Less");
        let equation =
            |name: &str, patterns: Vec<Pattern>, rhs: Expr| s.equation(name, patterns, rhs);
        let vars = |xs: &[&str]| xs.iter().map(|x| Pattern::Var(s.n(x))).collect::<Vec<_>>();
        let ctor_pattern = |ctor: usize, f: &dyn Fn(usize) -> String| {
            let ct = &ctor_list[ctor];
            Pattern::Ctor(
                s.n(&format!("{ctor_prefix}.{}", ct.name)),
                (0..ct.fields.len())
                    .map(|k| Pattern::Var(s.n(&f(k))))
                    .collect(),
                s.span,
            )
        };
        // `(C %a0 … : T %p0 …)`, constructor `ctor` of the `a`s.
        let first = |ctor: usize| {
            let ct = &ctor_list[ctor];
            Expr::Ann(
                Box::new(s.app(
                    s.var(&format!("{ctor_prefix}.{}", ct.name)),
                    (0..ct.fields.len()).map(|k| s.var(&a(k))).collect(),
                )),
                Box::new(this.clone()),
                s.span,
            )
        };
        let number = |ctor: usize| Expr::Num(BigUint::from(ctor), s.span);
        // The data fields of each constructor, in order.
        let data_fields: Vec<Vec<usize>> = member_fields
            .iter()
            .map(|kinds| {
                (0..kinds.len())
                    .filter(|k| kinds[*k] != Field::Proof)
                    .collect()
            })
            .collect();
        // The member a field is, if it is one.
        let recursive = |ctor: usize, k: usize| match member_fields[ctor][k] {
            Field::Recursive(t) => Some(t),
            _ => None,
        };
        // `f [ord := %ok]`: `f` given field `k`'s `Ord` instance, bound by
        // `with_instances`.
        let by_instance = |f: &str, k: usize| {
            let instance = Expr::NamedArg(
                s.n("ord"),
                Box::new(s.var(&format!("%o{k}"))),
                s.span,
                Bracket::Square,
            );
            s.app(s.var(f), vec![instance])
        };
        // `let %ok := Ord.instanceFor %ak` around `body`, for each field of
        // `ctor` compared by its `Ord` instance.
        let with_instances = |ctor: usize, body: Expr| {
            data_fields[ctor].iter().rev().fold(body, |body, &k| {
                if matches!(member_fields[ctor][k], Field::Recursive(_)) {
                    return body;
                }
                let instance = s.app(s.var("Std.Ord.instanceFor"), vec![s.var(&format!("%a{k}"))]);
                let_in(s.span, &format!("%o{k}"), None, instance, body)
            })
        };
        // Field `k`'s comparison of `x` and `y`.
        let cmp_by =
            |ctor: usize, k: usize, x: Expr, y: Expr, named: bool| match member_fields[ctor][k] {
                Field::Recursive(t) => s.app(s.var(&of(t, "compare")), vec![x, y]),
                _ if named => s.app(by_instance("Std.Ord.compare", k), vec![x, y]),
                _ => s.app(s.var("Std.Ord.compare"), vec![x, y]),
            };
        // The comparison of the data fields of `ctor`: `x(k)` with `y(k)`.
        let chain_by =
            |ctor: usize, x: &dyn Fn(usize) -> Expr, y: &dyn Fn(usize) -> Expr, named: bool| {
                let mut result: Option<Expr> = None;
                for &k in data_fields[ctor].iter().rev() {
                    let here = cmp_by(ctor, k, x(k), y(k), named);
                    result = Some(match result {
                        None => here,
                        Some(rest) => s.app(s.var("Std.Ordering.andThen"), vec![here, rest]),
                    });
                }
                result.unwrap_or_else(|| ordering("Equal"))
            };
        let chain = |ctor: usize, x: &dyn Fn(usize) -> Expr, y: &dyn Fn(usize) -> Expr| {
            chain_by(ctor, x, y, false)
        };
        let va = |k: usize| s.var(&a(k));
        let vb = |k: usize| s.var(&b(k));
        let signature = |name: &str, ty: Expr| s.signature(name, ty, false);
        let mut out: Vec<(usize, Definition)> = Vec::new();

        // Each constructor's part of the laws, once `b` (and `c`) name the
        // fields of the values compared with the `a`s, as the same
        // constructor: `equal` from `%f`, the comparison's `Equal`; `flip`;
        // and `trans` from `h1` and `h2`.
        let equal_fields = |ctor: usize, f: &str| {
            let fields = &data_fields[ctor];
            let count = fields.len();
            let field_law = |k: usize| match recursive(ctor, k) {
                Some(target) => call(&of(target, "equal"), &[&a(k), &b(k)]),
                None if tagged => s.app(
                    by_instance("Std.Ord.equal", k),
                    vec![s.var(&a(k)), s.var(&b(k))],
                ),
                None => call("Std.Ord.equal", &[&a(k), &b(k)]),
            };
            // With the constructor's fields as nested pairs (`T.%C%unpack`,
            // `derive.rs`): the pairs' equality, a field at a time by
            // `Ordering.thenPairEqual`, carried back by one `Eq.cong`.
            let unpack = format!("{prefix}{}%unpack", ctor_list[ctor].name);
            let tupled = self.has_member(
                plan.members[m].owner,
                &format!("{}{}%unpack", plan.members[m].prefix, ctor_list[ctor].name),
            );
            if count > 0 && tupled {
                // Ordering.thenPairEqual %f (law0 %a0 %b0) (%g1 => Ordering.thenPairEqual %g1 … (%gn => lawn %an %bn %gn))
                let h = |t: usize| {
                    if t == 0 {
                        f.to_string()
                    } else {
                        format!("%g{t}")
                    }
                };
                let mut pairs = s.app(field_law(fields[count - 1]), vec![s.var(&h(count - 1))]);
                for t in (0..count - 1).rev() {
                    pairs = s.app(
                        s.var("Std.Ordering.thenPairEqual"),
                        vec![
                            s.var(&h(t)),
                            field_law(fields[t]),
                            s.lam(&[&h(t + 1)], pairs),
                        ],
                    );
                }
                let tuple = |x: &dyn Fn(usize) -> String| {
                    let mut t = s.var(&x(fields[count - 1]));
                    for &k in fields[..count - 1].iter().rev() {
                        t = s.app(s.var("Std.Pair.MkPair"), vec![s.var(&x(k)), t]);
                    }
                    t
                };
                let pairs = Expr::Ann(
                    Box::new(pairs),
                    Box::new(s.eq(tuple(&a), tuple(&b))),
                    s.span,
                );
                return s.app(s.var("Std.Eq.cong"), vec![s.var(&unpack), pairs]);
            }
            // The proof that field `fields[t]`'s comparison is `Equal`,
            // from the whole comparison's, by `Ordering.thenEqual`.
            let mut rest = s.var(f);
            let mut equals: Vec<Expr> = Vec::new();
            for t in 0..count {
                if t + 1 == count {
                    equals.push(rest.clone());
                } else {
                    let split = s.app(s.var("Std.Ordering.thenEqual"), vec![rest.clone()]);
                    equals.push(s.app(s.var("Std.And.left"), vec![split.clone()]));
                    rest = s.app(s.var("Std.And.right"), vec![split]);
                }
            }
            let is_proof: Vec<bool> = member_fields[ctor]
                .iter()
                .map(|f| *f == Field::Proof)
                .collect();
            let field_equal = |k: usize| {
                let t = fields.iter().position(|q| *q == k).expect("a data field");
                let law = match recursive(ctor, k) {
                    Some(target) => of(target, "equal"),
                    None => "Std.Ord.equal".to_string(),
                };
                s.app(call(&law, &[&a(k), &b(k)]), vec![equals[t].clone()])
            };
            let ctor_name = &ctor_list[ctor].name;
            fields_equal(
                s.span,
                &format!("{ctor_prefix}.{ctor_name}"),
                &format!("{prefix}{ctor_name}"),
                &is_proof,
                np,
                &this,
                &a,
                &b,
                &field_equal,
                &|j| format!("%p{j}"),
            )
        };
        let flip_fields = |ctor: usize| {
            let mut proof: Option<Expr> = None;
            for &k in data_fields[ctor].iter().rev() {
                let law = match recursive(ctor, k) {
                    Some(target) => of(target, "flip"),
                    None => "Std.Ord.flip".to_string(),
                };
                let here = call(&law, &[&a(k), &b(k)]);
                proof = Some(match proof {
                    None => here,
                    Some(rest) => s.app(s.var("Std.Ordering.thenFlip"), vec![here, rest]),
                });
            }
            proof.unwrap_or_else(|| s.var("byComputing"))
        };
        let trans_fields = |ctor: usize, h1: Expr, h2: Expr| {
            let fields = &data_fields[ctor];
            let count = fields.len();
            // From position `t` on, given `h1` and `h2` for the rest.
            let mut proof: Option<Box<dyn Fn(Expr, Expr) -> Expr + '_>> = None;
            for t in (0..count).rev() {
                let k = fields[t];
                let (ak, bk, ck) = (a(k), b(k), c(k));
                let (p, q) = (format!("%p{t}"), format!("%q{t}"));
                let next = proof.take();
                let rec = recursive(ctor, k);
                let s = &s;
                let of = &of;
                let by_instance = &by_instance;
                proof = Some(Box::new(move |h1: Expr, h2: Expr| {
                    // `f [ord := %ok] %ak %bk %ck`, with the field's instance
                    // found once, by `with_instances`, before the hypotheses
                    // of the fields before it are in scope, where each search
                    // is dearer.
                    let by_instance = |f: &str| {
                        let args = [&ak, &bk, &ck].into_iter().map(|x| s.var(x)).collect();
                        s.app(by_instance(f, k), args)
                    };
                    let Some(next) = &next else {
                        let law = match rec {
                            Some(target) => call(&of(target, "trans"), &[&ak, &bk, &ck]),
                            None => by_instance("Std.Ord.trans"),
                        };
                        return s.app(law, vec![h1, h2]);
                    };
                    let rest = s.lam(&[&p, &q], next(s.var(&p), s.var(&q)));
                    if let Some(target) = rec {
                        let law = of(target, "trans");
                        let (compare, equal) = (of(target, "compare"), of(target, "equal"));
                        let (e, x, y) = (format!("%e{t}"), format!("%x{t}"), format!("%y{t}"));
                        s.app(
                            s.var("Std.Ordering.thenTransBy"),
                            vec![
                                s.var(&compare),
                                s.var(&ak),
                                s.var(&bk),
                                s.var(&ck),
                                h1,
                                h2,
                                s.lam(&[&x, &y], call(&law, &[&ak, &bk, &ck, &x, &y])),
                                s.lam(&[&e], call(&equal, &[&ak, &bk, &e])),
                                s.lam(&[&e], call(&equal, &[&bk, &ck, &e])),
                                rest,
                            ],
                        )
                    } else {
                        s.app(by_instance("Std.Ord.thenTrans"), vec![h1, h2, rest])
                    }
                }));
            }
            match &proof {
                Some(proof) => with_instances(ctor, proof(h1, h2)),
                None => s.app(
                    s.var("Std.Void.impossible"),
                    vec![s.app(s.var("Std.Ordering.equalNotLess"), vec![h1])],
                ),
            }
        };
        // `let %b0 := T.%C%0%at %s %e …` (or `%c`s) around `body`.
        let known = |ctor: usize, names: &dyn Fn(usize) -> String, x: &str, e: &str, body: Expr| {
            let ct = &ctor_list[ctor];
            (0..ct.fields.len()).rev().fold(body, |body, k| {
                let at = format!("{prefix}{}%{k}%at", ct.name);
                let_in(s.span, &names(k), None, call(&at, &[x, e]), body)
            })
        };
        let eta_at = |x: &str, ctor: usize, e: &str| {
            s.app(
                s.var(&of(m, "etaAt")),
                vec![s.var(x), number(ctor), s.var(e)],
            )
        };
        let sym = |x: Expr| s.app(s.var("Std.Eq.flipped"), vec![x]);
        let tag_is = |x: &str, ctor: usize| s.eq(tag(x), number(ctor));

        // T.%compare
        let ty = values(&["%r", "%s"], s.var("Std.Ordering"));
        if tagged {
            // T.%compare %r %s = if Nat.equal (T.%tag %r) (T.%tag %s) then T.%fields %r %s else Nat.compare (T.%tag %r) (T.%tag %s)
            // T.%fields (C %a0 …) %s = <the a's compared with T.%C%k %ak %s>
            let rhs = Expr::If {
                binder: None,
                cond: Box::new(tags("Std.Nat.equal", &["%r", "%s"])),
                then: Box::new(call(&fields_of, &["%r", "%s"])),
                otherwise: Box::new(tags("Std.Nat.compare", &["%r", "%s"])),
                span: s.span,
            };
            out.push((
                0,
                (
                    signature(&compare, ty.clone()),
                    vec![equation(&compare, vars(&["%r", "%s"]), rhs)],
                ),
            ));
            let equations = (0..ctors)
                .map(|ctor| {
                    let projected = |k: usize| {
                        let field = format!("{prefix}{}%{k}", ctor_list[ctor].name);
                        call(&field, &[&a(k), "%s"])
                    };
                    equation(
                        &fields_of,
                        vec![ctor_pattern(ctor, &a), Pattern::Var(s.n("%s"))],
                        chain(ctor, &va, &projected),
                    )
                })
                .collect();
            out.push((0, (signature(&fields_of, ty), equations)));
        } else if enumeration {
            let rhs = tags("Std.Nat.compare", &["%r", "%s"]);
            out.push((
                0,
                (
                    signature(&compare, ty),
                    vec![equation(&compare, vars(&["%r", "%s"]), rhs)],
                ),
            ));
        } else {
            let equations = vec![equation(
                &compare,
                vec![ctor_pattern(0, &a), ctor_pattern(0, &b)],
                chain(0, &va, &vb),
            )];
            out.push((0, (signature(&compare, ty), equations)));
        }

        // T.%equal
        let ty = values(
            &["%r", "%s"],
            s.arrow(
                s.eq(call(&compare, &["%r", "%s"]), ordering("Equal")),
                s.eq(s.var("%r"), s.var("%s")),
            ),
        );
        let mut equations = Vec::new();
        for ctor in 0..ctors {
            let second = Pattern::Var(s.n("%s"));
            let patterns = |second| vec![ctor_pattern(ctor, &a), second, Pattern::Var(s.n("%h"))];
            if enumeration {
                // T.%equal C %s %h = T.%etaAt %s c (Eq.sym (Nat.compareEqual c (T.%tag %s) %h))
                let tags_equal = s.app(
                    s.var("Std.Nat.compareEqual"),
                    vec![number(ctor), tag("%s"), s.var("%h")],
                );
                let proof = s.app(
                    s.var(&of(m, "etaAt")),
                    vec![s.var("%s"), number(ctor), sym(tags_equal)],
                );
                equations.push(equation(&equal, patterns(second), proof));
            } else if tagged {
                // T.%equal (C %a0 …) %s %h =
                //   let %t := Ordering.tagsEqual c (T.%tag %s) (T.%fields (C %a0 …) %s) %h
                //   let %e : T.%tag %s = c := Eq.sym (And.left %t)
                //   let %b0 := T.%C%0%at %s %e …
                //   let %f : <the a's compared with the b's> = Equal :=
                //     J (%y %q => T.%fields (C %a0 …) %y = Equal) (And.right %t) (Eq.sym (T.%etaAt %s c %e))
                //   Eq.trans <C %a0 … = C %b0 …, from %f> (T.%etaAt %s c %e)
                let split = s.app(
                    s.var("Std.Ordering.tagsEqual"),
                    vec![
                        number(ctor),
                        tag("%s"),
                        s.app(s.var(&fields_of), vec![first(ctor), s.var("%s")]),
                        s.var("%h"),
                    ],
                );
                let motive = s.lam(
                    &["%y", "%q"],
                    s.eq(
                        s.app(s.var(&fields_of), vec![first(ctor), s.var("%y")]),
                        ordering("Equal"),
                    ),
                );
                let viewed = s.app(
                    s.var("J"),
                    vec![
                        motive,
                        s.app(s.var("Std.And.right"), vec![s.var("%t")]),
                        sym(eta_at("%s", ctor, "%e")),
                    ],
                );
                let body = s.app(
                    s.var("Std.Eq.trans"),
                    vec![equal_fields(ctor, "%f"), eta_at("%s", ctor, "%e")],
                );
                let viewed_ty = s.eq(chain_by(ctor, &va, &vb, true), ordering("Equal"));
                let body = let_in(s.span, "%f", Some(viewed_ty), viewed, body);
                let body = known(ctor, &b, "%s", "%e", body);
                let body = let_in(
                    s.span,
                    "%e",
                    Some(tag_is("%s", ctor)),
                    sym(s.app(s.var("Std.And.left"), vec![s.var("%t")])),
                    body,
                );
                let body = let_in(s.span, "%t", None, split, body);
                let body = with_instances(ctor, body);
                equations.push(equation(&equal, patterns(second), body));
            } else {
                equations.push(equation(
                    &equal,
                    patterns(ctor_pattern(ctor, &b)),
                    equal_fields(ctor, "%h"),
                ));
            }
        }
        out.push((1, (signature(&equal, ty), equations)));

        // T.%flip
        let ty = values(
            &["%r", "%s"],
            s.eq(
                call(&compare, &["%s", "%r"]),
                s.app(
                    s.var("Std.Ordering.flip"),
                    vec![call(&compare, &["%r", "%s"])],
                ),
            ),
        );
        let mut equations = Vec::new();
        if enumeration {
            equations.push(equation(
                &flip,
                vars(&["%r", "%s"]),
                tags("Std.Nat.compareFlip", &["%r", "%s"]),
            ));
        } else if tagged {
            // T.%flip (C %a0 …) %s = Ordering.tagsFlip c (T.%tag %s) (T.%fields (C %a0 …) %s) (T.%fields %s (C %a0 …))
            //   (%t => let %e : T.%tag %s = c := Eq.sym %t
            //     let %b0 := T.%C%0%at %s %e …
            //     J (%y %q => T.%fields %y (C %a0 …) = Ordering.flip (T.%fields (C %a0 …) %y)) <flip of the fields> (T.%etaAt %s c %e))
            for ctor in 0..ctors {
                let fields = |x: Expr, y: Expr| s.app(s.var(&fields_of), vec![x, y]);
                let motive = s.lam(
                    &["%y", "%q"],
                    s.eq(
                        fields(s.var("%y"), first(ctor)),
                        s.app(
                            s.var("Std.Ordering.flip"),
                            vec![fields(first(ctor), s.var("%y"))],
                        ),
                    ),
                );
                let proof = s.app(
                    s.var("J"),
                    vec![motive, flip_fields(ctor), eta_at("%s", ctor, "%e")],
                );
                let proof = known(ctor, &b, "%s", "%e", proof);
                let proof = let_in(
                    s.span,
                    "%e",
                    Some(tag_is("%s", ctor)),
                    sym(s.var("%t")),
                    proof,
                );
                let rhs = s.app(
                    s.var("Std.Ordering.tagsFlip"),
                    vec![
                        number(ctor),
                        tag("%s"),
                        fields(first(ctor), s.var("%s")),
                        fields(s.var("%s"), first(ctor)),
                        s.lam(&["%t"], proof),
                    ],
                );
                equations.push(equation(
                    &flip,
                    vec![ctor_pattern(ctor, &a), Pattern::Var(s.n("%s"))],
                    rhs,
                ));
            }
        } else {
            equations.push(equation(
                &flip,
                vec![ctor_pattern(0, &a), ctor_pattern(0, &b)],
                flip_fields(0),
            ));
        }
        out.push((2, (signature(&flip, ty), equations)));

        // T.%trans
        let is_less = |x: &str, y: &str| s.eq(call(&compare, &[x, y]), less());
        let ty = values(
            &["%r", "%s", "%u"],
            s.arrow(
                is_less("%r", "%s"),
                s.arrow(is_less("%s", "%u"), is_less("%r", "%u")),
            ),
        );
        let mut equations = Vec::new();
        if enumeration {
            equations.push(equation(
                &trans,
                vars(&["%r", "%s", "%u", "%h1", "%h2"]),
                s.app(
                    tags("Std.Nat.compareTrans", &["%r", "%s", "%u"]),
                    vec![s.var("%h1"), s.var("%h2")],
                ),
            ));
        } else if tagged {
            // T.%trans (C %a0 …) %s %u %h1 %h2 = Ordering.tagsTrans c (T.%tag %s) (T.%tag %u)
            //     (T.%fields (C %a0 …) %s) (T.%fields %s %u) (T.%fields (C %a0 …) %u)
            //   (%t1 %t2 => let %e : T.%tag %s = c := Eq.sym %t1
            //     let %eu : T.%tag %u = c := Eq.sym (Eq.trans %t1 %t2)
            //     let %b0 := T.%C%0%at %s %e …; let %c0 := T.%C%0%at %u %eu …
            //     J (%x %q => M %x %u) (J (%y %q => M (T.%view %s c %e) %y) (%l1 %l2 => <trans of the fields>) (T.%etaAt %u c %eu)) (T.%etaAt %s c %e))
            //   %h1 %h2
            // where M x y = T.%fields (C %a0 …) x = Less -> T.%fields x y = Less -> T.%fields (C %a0 …) y = Less.
            for ctor in 0..ctors {
                let fields = |x: Expr, y: Expr| s.app(s.var(&fields_of), vec![x, y]);
                let is_less = |e: Expr| s.eq(e, less());
                let claim = |x: Expr, y: Expr| {
                    s.arrow(
                        is_less(fields(first(ctor), x.clone())),
                        s.arrow(
                            is_less(fields(x, y.clone())),
                            is_less(fields(first(ctor), y)),
                        ),
                    )
                };
                let viewed_s = s.app(
                    s.var(&of(m, "view")),
                    vec![s.var("%s"), number(ctor), s.var("%e")],
                );
                let inner = s.app(
                    s.var("J"),
                    vec![
                        s.lam(&["%y", "%q"], claim(viewed_s, s.var("%y"))),
                        s.lam(
                            &["%l1", "%l2"],
                            trans_fields(ctor, s.var("%l1"), s.var("%l2")),
                        ),
                        eta_at("%u", ctor, "%eu"),
                    ],
                );
                let proof = s.app(
                    s.var("J"),
                    vec![
                        s.lam(&["%x", "%q"], claim(s.var("%x"), s.var("%u"))),
                        inner,
                        eta_at("%s", ctor, "%e"),
                    ],
                );
                let proof = known(ctor, &c, "%u", "%eu", proof);
                let proof = known(ctor, &b, "%s", "%e", proof);
                let proof = let_in(
                    s.span,
                    "%eu",
                    Some(tag_is("%u", ctor)),
                    sym(s.app(s.var("Std.Eq.trans"), vec![s.var("%t1"), s.var("%t2")])),
                    proof,
                );
                let proof = let_in(
                    s.span,
                    "%e",
                    Some(tag_is("%s", ctor)),
                    sym(s.var("%t1")),
                    proof,
                );
                let rhs = s.app(
                    s.var("Std.Ordering.tagsTrans"),
                    vec![
                        number(ctor),
                        tag("%s"),
                        tag("%u"),
                        fields(first(ctor), s.var("%s")),
                        fields(s.var("%s"), s.var("%u")),
                        fields(first(ctor), s.var("%u")),
                        s.lam(&["%t1", "%t2"], proof),
                        s.var("%h1"),
                        s.var("%h2"),
                    ],
                );
                let mut patterns = vec![ctor_pattern(ctor, &a)];
                patterns.extend(vars(&["%s", "%u", "%h1", "%h2"]));
                equations.push(equation(&trans, patterns, rhs));
            }
        } else {
            let mut patterns = vec![
                ctor_pattern(0, &a),
                ctor_pattern(0, &b),
                ctor_pattern(0, &c),
            ];
            patterns.extend(vars(&["%h1", "%h2"]));
            equations.push(equation(
                &trans,
                patterns,
                trans_fields(0, s.var("%h1"), s.var("%h2")),
            ));
        }
        out.push((3, (signature(&trans, ty), equations)));
        out
    }
}

/// `[%p0 : _] -> … -> [auto ord : Std.Ord %p0] -> … -> rest`, for `T`
/// (`data`): an `ord` for each parameter the plan's fields need one for
/// (`ordA` for `a`, … when there are several).
fn ord_params<'a>(
    s: &'a Src,
    data: &'a stitchwort_core::globals::Data,
    plan: &'a Plan,
) -> impl Fn(Expr) -> Expr + 'a {
    let np = data.params().len();
    let dicts: Vec<usize> = (0..np).filter(|j| plan.deciders[*j]).collect();
    move |rest: Expr| {
        let dict = |j: usize| {
            if dicts.len() == 1 {
                "ord".to_string()
            } else {
                let p = data.params()[j].0.to_string();
                let mut chars = p.chars();
                match chars.next() {
                    Some(ch) => format!("ord{}{}", ch.to_uppercase(), chars.as_str()),
                    None => format!("ord{j}"),
                }
            }
        };
        let mut ty = rest;
        for &j in dicts.iter().rev() {
            let dom = s.app(s.var("Std.Ord"), vec![s.var(&format!("%p{j}"))]);
            ty = s.pi(&[&dict(j)], true, true, dom, ty);
        }
        for j in (0..np).rev() {
            ty = s.pi(&[&format!("%p{j}")], true, false, Expr::Hole(s.span), ty);
        }
        ty
    }
}

/// Builds source at one place.
pub(crate) struct Src {
    pub(crate) span: Span,
}

impl Src {
    /// `T %p0 …`, an `auto` parameter given by name: `T %p0 [ord := %p1]`.
    pub(crate) fn this(&self, ty_name: &str, data: &stitchwort_core::globals::Data) -> Expr {
        let np = data.params().len();
        self.app(
            self.var(ty_name),
            (0..np)
                .map(|j| {
                    let p = self.var(&format!("%p{j}"));
                    if data.auto_params().get(j) == Some(&true) {
                        Expr::NamedArg(
                            self.n(&data.params()[j].0),
                            Box::new(p),
                            self.span,
                            Bracket::Square,
                        )
                    } else {
                        p
                    }
                })
                .collect(),
        )
    }

    pub(crate) fn signature(&self, name: &str, ty: Expr, instance: bool) -> Decl {
        Decl::Signature {
            name: self.n(name),
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
            span: self.span,
        }
    }

    pub(crate) fn equation(&self, name: &str, patterns: Vec<Pattern>, rhs: Expr) -> Decl {
        Decl::Equation {
            guard: None,
            name: self.n(name),
            patterns,
            rhs: Some(rhs),
            arm: None,
            span: self.span,
        }
    }

    pub(crate) fn n(&self, text: &str) -> ast::Name {
        ast::Name {
            text: text.to_string(),
            span: self.span,
        }
    }

    pub(crate) fn var(&self, text: &str) -> Expr {
        Expr::Var(self.n(text))
    }

    pub(crate) fn app(&self, head: Expr, args: Vec<Expr>) -> Expr {
        args.into_iter()
            .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
    }

    pub(crate) fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::Binary(BinOp::Eq, Box::new(a), Box::new(b))
    }

    pub(crate) fn arrow(&self, a: Expr, b: Expr) -> Expr {
        Expr::Arrow(Box::new(a), Box::new(b))
    }

    pub(crate) fn lam(&self, names: &[&str], body: Expr) -> Expr {
        Expr::Lam(
            names.iter().map(|x| self.n(x)).collect(),
            Box::new(body),
            self.span,
        )
    }

    /// `(x: ty) => body`.
    pub(crate) fn typed_lam(&self, x: &str, ty: Expr, body: Expr) -> Expr {
        Expr::TypedLam(
            self.n(x),
            ast::Mode::Explicit,
            Box::new(ty),
            Box::new(body),
            self.span,
        )
    }

    pub(crate) fn pi(
        &self,
        names: &[&str],
        implicit: bool,
        auto: bool,
        dom: Expr,
        cod: Expr,
    ) -> Expr {
        names.iter().rev().fold(cod, |cod, x| Expr::Pi {
            name: self.n(x),
            implicit,
            auto,
            dom: Box::new(dom.clone()),
            cod: Box::new(cod),
            span: self.span,
        })
    }
}
