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
//! the fields use; `Ord`'s `eq` is `T`'s own `DecEq` instance, so a type
//! without a derived one gets no `Ord` either. Why not is kept for the note
//! when an `Ord` is needed for `T`.
//!
//! The laws are put together from lemmas in the core, proved once
//! (`Ordering.thenEqual`, `Ordering.thenFlip`, `Ord.thenTrans`, …): each
//! constructor's case follows its fields, one lemma per field. For
//! `type T a = | C1 … | C2 x y | …`, with `x: Nat` and `y: T a`:
//!
//! ```text
//! T.%compare : [a : _] -> [auto ord: Ord a] -> (%r %s : T a) -> Ordering
//! T.%compare (C2 a0 a1) (C2 b0 b1) = Ordering.andThen (Ord.compare a0 b0) (T.%compare a1 b1)
//! …   -- one equation for each constructor
//! T.%compare r s = Nat.compare (T.%tag r) (T.%tag s)
//!
//! T.%equal : … -> (%r %s : T a) -> T.%compare r s = Equal -> r = s
//! T.%flip : … -> (%r %s : T a) -> T.%compare s r = Ordering.flip (T.%compare r s)
//! T.%unfold : … -> (%r %s : T a) -> T.%compare r s = Ordering.andThen (Nat.compare (T.%tag r) (T.%tag s)) (T.%compare r s)
//! T.%trans : … -> (%r %s %u : T a) -> T.%compare r s = Less -> T.%compare s u = Less -> T.%compare r u = Less
//!
//! instance T.%instOrd : … -> Ord (T a) := Ord.fromCompare T.%compare T.%equal T.%flip T.%trans
//! ```
//!
//! For values of different constructors the last equation of each applies,
//! and the tags decide: `equal` refutes `Nat.compare i j = Equal` for two
//! different numbers, `flip` is `Nat.compare`'s, and `trans` is
//! `Ordering.byTagTrans` through `T.%unfold` (which is `rfl` in every case,
//! but the third value may not have been matched yet). An enumeration (no
//! fields at all) is just its tags: `T.%compare r s = Nat.compare (T.%tag r)
//! (T.%tag s)`, with `Nat`'s laws, and only `equal` looks at constructors.

use stitchwort_core::DataId;
use stitchwort_syntax::Span;
use stitchwort_syntax::ast::{self, BinOp, Bracket, Decl, Expr, Pattern};

use crate::derive::{Field, Plan, fields_equal};
use crate::{Elaborator, Result, interfaces};

type Definition = (Decl, Vec<Decl>);

impl Elaborator {
    /// After data type or record `d` is admitted, and its `DecEq` derived:
    /// its `Ord` instance, if one can be derived, or else why not.
    pub(crate) fn derive_data_ord(&mut self, d: DataId) -> Result<()> {
        let data = self.globals.data(d);
        let generated = !data.record && data.ctors.iter().any(|c| c.name.starts_with('%'));
        let (Some(ord), Some(dec_eq)) = (interfaces::ord(self), interfaces::dec_eq(self)) else {
            return Ok(());
        };
        if self.loading_prelude || generated || self.declares_instance_of(ord) {
            return Ok(());
        }
        // `Ord`'s `eq` is `T`'s `DecEq` instance, found when the instance is
        // built.
        if let Some(why) = self.no_eq.get(&d) {
            let why = format!("`Ord` needs `==`, which isn't derived for it: {why}");
            self.no_ord.insert(d, why);
            return Ok(());
        }
        if self.declares_instance_of(dec_eq) {
            self.no_ord.insert(
                d,
                "its module's own `DecEq` instance, which `Ord` needs, isn't known yet when it's \
                 declared; declare an `Ord` instance too"
                    .into(),
            );
            return Ok(());
        }
        let plan = match self.field_plan(d, ord, "`Ord`")? {
            Ok(plan) => plan,
            Err(why) => {
                self.no_ord.insert(d, why);
                return Ok(());
            }
        };
        // The helpers `DecEq` declares, in case it didn't.
        let ctors = self.globals.data(d).ctors.len();
        if ctors > 1 && !self.has_member(d, "%tag") {
            self.derive_tag(d)?;
        }
        for c in 0..ctors {
            for (k, field) in plan.fields[c].iter().enumerate() {
                let member = format!("%{}%P%{k}", self.globals.data(d).ctors[c].name);
                if *field == Field::Proof && !self.has_member(d, &member) {
                    self.derive_proof_type(d, c, k)?;
                }
            }
        }
        let mut result = Ok(());
        for (signature, equations) in self.ord_source(d, &plan) {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&signature, &equations));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if e.code == "E-RESOURCE" => return Err(e),
            Err(e) => {
                self.no_ord
                    .insert(d, format!("deriving it failed: {}", e.message));
            }
        }
        Ok(())
    }

    /// Whether `T.member` is declared.
    fn has_member(&self, d: DataId, member: &str) -> bool {
        let key = Self::member_key(&self.data_key(d), member);
        self.scope.get(&key).is_some()
    }

    /// The source of `T.%compare`, `T.%equal`, `T.%flip`, `T.%unfold` (with
    /// two constructors or more, not all without fields), `T.%trans` and
    /// `T.%instOrd`, in that order.
    fn ord_source(&self, d: DataId, plan: &Plan) -> Vec<Definition> {
        let data = self.globals.data(d);
        let ty_name = self.relative_to_root(&data.name);
        let s = Src { span: data.span };
        let np = data.params.len();
        let ctors = data.ctors.len();
        let enumeration = ctors > 1 && data.ctors.iter().all(|c| c.fields.is_empty());
        let tagged = ctors > 1 && !enumeration;
        let param = |j: usize| format!("%p{j}");
        let a = |k: usize| format!("%a{k}");
        let b = |k: usize| format!("%b{k}");
        let c = |k: usize| format!("%c{k}");
        let member = |m: &str| format!("{ty_name}.%{m}");
        let (compare, equal, flip, unfold, trans) = (
            member("compare"),
            member("equal"),
            member("flip"),
            member("unfold"),
            member("trans"),
        );
        let dicts: Vec<usize> = (0..np).filter(|j| plan.deciders[*j]).collect();
        // `ord`, or one per parameter after it (`ordA` for `a`) when there are
        // several.
        let dict = |j: usize| {
            if dicts.len() == 1 {
                "ord".to_string()
            } else {
                let p = data.params[j].0.to_string();
                let mut chars = p.chars();
                match chars.next() {
                    Some(ch) => format!("ord{}{}", ch.to_uppercase(), chars.as_str()),
                    None => format!("ord{j}"),
                }
            }
        };
        // [%p0 : _] -> … -> [auto ord : Std.Ord %p0] -> … -> rest
        let with_params = |rest: Expr| {
            let mut ty = rest;
            for &j in dicts.iter().rev() {
                let dom = s.app(s.var("Std.Ord"), vec![s.var(&param(j))]);
                ty = s.pi(&[&dict(j)], true, true, dom, ty);
            }
            for j in (0..np).rev() {
                ty = s.pi(&[&param(j)], true, false, Expr::Hole(s.span), ty);
            }
            ty
        };
        // An `auto` parameter is given by name: `T %p0 [ord := %p1]`.
        let this = s.app(
            s.var(&ty_name),
            (0..np)
                .map(|j| {
                    if data.auto_params.get(j) == Some(&true) {
                        Expr::NamedArg(
                            s.n(&data.params[j].0),
                            Box::new(s.var(&param(j))),
                            s.span,
                            Bracket::Square,
                        )
                    } else {
                        s.var(&param(j))
                    }
                })
                .collect(),
        );
        let values =
            |names: &[&str], cod: Expr| with_params(s.pi(names, false, false, this.clone(), cod));
        let call =
            |f: &str, args: &[&str]| s.app(s.var(f), args.iter().map(|x| s.var(x)).collect());
        let tag = |x: &str| call(&format!("{ty_name}.%tag"), &[x]);
        let tags = |f: &str, xs: &[&str]| s.app(s.var(f), xs.iter().map(|x| tag(x)).collect());
        let ordering = |c: &str| s.var(&format!("Std.Ordering.{c}"));
        let less = || ordering("Less");
        let equation = |name: &str, patterns: Vec<Pattern>, rhs: Expr| Decl::Equation {
            name: s.n(name),
            patterns,
            rhs: Some(rhs),
            arm: None,
            span: s.span,
        };
        let vars = |xs: &[&str]| xs.iter().map(|x| Pattern::Var(s.n(x))).collect::<Vec<_>>();
        let ctor_pattern = |ctor: usize, f: &dyn Fn(usize) -> String| {
            let ct = &data.ctors[ctor];
            Pattern::Ctor(
                s.n(&format!("{ty_name}.{}", ct.name)),
                (0..ct.fields.len())
                    .map(|k| Pattern::Var(s.n(&f(k))))
                    .collect(),
                s.span,
            )
        };
        // The data fields of each constructor, in order.
        let data_fields: Vec<Vec<usize>> = plan
            .fields
            .iter()
            .map(|kinds| {
                (0..kinds.len())
                    .filter(|k| kinds[*k] != Field::Proof)
                    .collect()
            })
            .collect();
        let recursive = |ctor: usize, k: usize| plan.fields[ctor][k] == Field::Recursive;
        // Field `k`'s comparison of `x` and `y`.
        let cmp = |ctor: usize, k: usize, x: &str, y: &str| {
            if recursive(ctor, k) {
                call(&compare, &[x, y])
            } else {
                call("Std.Ord.compare", &[x, y])
            }
        };
        // The comparison of the data fields from position `t` on.
        let chain =
            |ctor: usize, t: usize, x: &dyn Fn(usize) -> String, y: &dyn Fn(usize) -> String| {
                let fields = &data_fields[ctor];
                let mut result: Option<Expr> = None;
                for &k in fields[t..].iter().rev() {
                    let here = cmp(ctor, k, &x(k), &y(k));
                    result = Some(match result {
                        None => here,
                        Some(rest) => s.app(s.var("Std.Ordering.andThen"), vec![here, rest]),
                    });
                }
                result.unwrap_or_else(|| ordering("Equal"))
            };
        let signature = |name: &str, ty: Expr, instance: bool| Decl::Signature {
            name: s.n(name),
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
            span: s.span,
        };
        let mut out: Vec<Definition> = Vec::new();

        // T.%compare
        let ty = values(&["%r", "%s"], s.var("Std.Ordering"));
        let mut equations = Vec::new();
        if enumeration {
            equations.push(equation(
                &compare,
                vars(&["%r", "%s"]),
                tags("Std.Nat.compare", &["%r", "%s"]),
            ));
        } else {
            for ctor in 0..ctors {
                equations.push(equation(
                    &compare,
                    vec![ctor_pattern(ctor, &a), ctor_pattern(ctor, &b)],
                    chain(ctor, 0, &a, &b),
                ));
            }
            if tagged {
                equations.push(equation(
                    &compare,
                    vars(&["%r", "%s"]),
                    tags("Std.Nat.compare", &["%r", "%s"]),
                ));
            }
        }
        out.push((signature(&compare, ty, false), equations));

        // Values of different constructors don't compare `Equal`.
        let differ = || {
            let equal_tags = s.app(
                tags("Std.Nat.compareEqual", &["%r", "%s"]),
                vec![s.var("%h")],
            );
            let refuted = s.app(
                tags("Std.Nat.equalFalse", &["%r", "%s"]),
                vec![s.var("rfl"), equal_tags],
            );
            s.app(s.var("Std.Void.exfalso"), vec![refuted])
        };

        // T.%equal
        let ty = values(
            &["%r", "%s"],
            s.arrow(
                s.eq(call(&compare, &["%r", "%s"]), ordering("Equal")),
                s.eq(s.var("%r"), s.var("%s")),
            ),
        );
        let mut equations = Vec::new();
        for (ctor, fields) in data_fields.iter().enumerate() {
            let m = fields.len();
            // The proof that field `fields[t]`'s comparison is `Equal`, from
            // `%h`, the whole comparison's, by `Ordering.thenEqual`.
            let mut rest = s.var("%h");
            let mut equals: Vec<Expr> = Vec::new();
            for t in 0..m {
                if t + 1 == m {
                    equals.push(rest.clone());
                } else {
                    let split = s.app(s.var("Std.Ordering.thenEqual"), vec![rest.clone()]);
                    equals.push(s.app(s.var("Std.And.left"), vec![split.clone()]));
                    rest = s.app(s.var("Std.And.right"), vec![split]);
                }
            }
            let is_proof: Vec<bool> = plan.fields[ctor]
                .iter()
                .map(|f| *f == Field::Proof)
                .collect();
            let field_equal = |k: usize| {
                let t = fields.iter().position(|q| *q == k).expect("a data field");
                let law = if recursive(ctor, k) {
                    equal.as_str()
                } else {
                    "Std.Ord.equal"
                };
                s.app(call(law, &[&a(k), &b(k)]), vec![equals[t].clone()])
            };
            let proof = fields_equal(
                s.span,
                &ty_name,
                &data.ctors[ctor].name,
                &is_proof,
                np,
                &this,
                &a,
                &b,
                &field_equal,
                &|j| format!("%p{j}"),
            );
            equations.push(equation(
                &equal,
                vec![
                    ctor_pattern(ctor, &a),
                    ctor_pattern(ctor, &b),
                    Pattern::Var(s.n("%h")),
                ],
                proof,
            ));
        }
        if ctors > 1 {
            equations.push(equation(&equal, vars(&["%r", "%s", "%h"]), differ()));
        }
        out.push((signature(&equal, ty, false), equations));

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
        let by_tags = || tags("Std.Nat.compareFlip", &["%r", "%s"]);
        let mut equations = Vec::new();
        if enumeration {
            equations.push(equation(&flip, vars(&["%r", "%s"]), by_tags()));
        } else {
            for (ctor, fields) in data_fields.iter().enumerate() {
                let mut proof: Option<Expr> = None;
                for &k in fields.iter().rev() {
                    let law = if recursive(ctor, k) {
                        flip.as_str()
                    } else {
                        "Std.Ord.flip"
                    };
                    let here = call(law, &[&a(k), &b(k)]);
                    proof = Some(match proof {
                        None => here,
                        Some(rest) => s.app(s.var("Std.Ordering.thenFlip"), vec![here, rest]),
                    });
                }
                equations.push(equation(
                    &flip,
                    vec![ctor_pattern(ctor, &a), ctor_pattern(ctor, &b)],
                    proof.unwrap_or_else(|| s.var("rfl")),
                ));
            }
            if tagged {
                equations.push(equation(&flip, vars(&["%r", "%s"]), by_tags()));
            }
        }
        out.push((signature(&flip, ty, false), equations));

        // T.%unfold: a comparison is its tags' then itself.
        if tagged {
            let ty = values(
                &["%r", "%s"],
                s.eq(
                    call(&compare, &["%r", "%s"]),
                    s.app(
                        s.var("Std.Ordering.andThen"),
                        vec![
                            tags("Std.Nat.compare", &["%r", "%s"]),
                            call(&compare, &["%r", "%s"]),
                        ],
                    ),
                ),
            );
            let mut equations: Vec<Decl> = (0..ctors)
                .map(|ctor| {
                    equation(
                        &unfold,
                        vec![ctor_pattern(ctor, &a), ctor_pattern(ctor, &b)],
                        s.var("rfl"),
                    )
                })
                .collect();
            equations.push(equation(&unfold, vars(&["%r", "%s"]), s.var("rfl")));
            out.push((signature(&unfold, ty, false), equations));
        }

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
        } else {
            for (ctor, fields) in data_fields.iter().enumerate() {
                let m = fields.len();
                // From position `t` on, given `h1` and `h2` for the rest.
                let mut proof: Option<Box<dyn Fn(Expr, Expr) -> Expr + '_>> = None;
                for t in (0..m).rev() {
                    let k = fields[t];
                    let (ak, bk, ck) = (a(k), b(k), c(k));
                    let (p, q) = (format!("%p{t}"), format!("%q{t}"));
                    let next = proof.take();
                    let rec = recursive(ctor, k);
                    let s = &s;
                    let compare = &compare;
                    let equal = &equal;
                    let trans = &trans;
                    proof = Some(Box::new(move |h1: Expr, h2: Expr| {
                        let law = if rec { trans.as_str() } else { "Std.Ord.trans" };
                        let Some(next) = &next else {
                            return s.app(call(law, &[&ak, &bk, &ck]), vec![h1, h2]);
                        };
                        let rest = s.lam(&[&p, &q], next(s.var(&p), s.var(&q)));
                        if rec {
                            let (e, x, y) = (format!("%e{t}"), format!("%x{t}"), format!("%y{t}"));
                            s.app(
                                s.var("Std.Ordering.thenTransBy"),
                                vec![
                                    s.var(compare),
                                    s.var(&ak),
                                    s.var(&bk),
                                    s.var(&ck),
                                    h1,
                                    h2,
                                    s.lam(&[&x, &y], call(trans, &[&ak, &bk, &ck, &x, &y])),
                                    s.lam(&[&e], call(equal, &[&ak, &bk, &e])),
                                    s.lam(&[&e], call(equal, &[&bk, &ck, &e])),
                                    rest,
                                ],
                            )
                        } else {
                            s.app(
                                call("Std.Ord.thenTrans", &[&ak, &bk, &ck]),
                                vec![h1, h2, rest],
                            )
                        }
                    }));
                }
                let body = match &proof {
                    Some(proof) => proof(s.var("%h1"), s.var("%h2")),
                    None => s.app(
                        s.var("Std.Void.exfalso"),
                        vec![s.app(s.var("Std.Ordering.equalNotLess"), vec![s.var("%h1")])],
                    ),
                };
                let mut patterns = vec![
                    ctor_pattern(ctor, &a),
                    ctor_pattern(ctor, &b),
                    ctor_pattern(ctor, &c),
                ];
                patterns.extend(vars(&["%h1", "%h2"]));
                equations.push(equation(&trans, patterns, body));
            }
            if tagged {
                // Not all of one constructor: the tags decide.
                let through = |x: &str, y: &str, h: &str| {
                    s.app(
                        s.var("Std.Eq.trans"),
                        vec![
                            s.app(s.var("Std.Eq.sym"), vec![call(&unfold, &[x, y])]),
                            s.var(h),
                        ],
                    )
                };
                let never = s.lam(
                    &["%e1", "%e2", "%p", "%q"],
                    s.app(
                        s.var("Std.Void.exfalso"),
                        vec![s.app(
                            s.var("Std.Ordering.notBothEqual"),
                            vec![
                                tags("Std.Nat.compare", &["%r", "%s"]),
                                tags("Std.Nat.compare", &["%s", "%u"]),
                                s.var("rfl"),
                                s.var("%e1"),
                                s.var("%e2"),
                            ],
                        )],
                    ),
                );
                let mut args: Vec<Expr> = ["%r", "%s", "%u"].iter().map(|x| tag(x)).collect();
                args.extend([
                    call(&compare, &["%r", "%s"]),
                    call(&compare, &["%s", "%u"]),
                    call(&compare, &["%r", "%u"]),
                    through("%r", "%s", "%h1"),
                    through("%s", "%u", "%h2"),
                    never,
                ]);
                let by_tags = s.app(s.var("Std.Ordering.byTagTrans"), args);
                let body = s.app(
                    s.var("Std.Eq.trans"),
                    vec![call(&unfold, &["%r", "%u"]), by_tags],
                );
                equations.push(equation(
                    &trans,
                    vars(&["%r", "%s", "%u", "%h1", "%h2"]),
                    body,
                ));
            }
        }
        out.push((signature(&trans, ty, false), equations));

        // instance T.%instOrd : … -> Std.Ord (T %p0 …) :=
        //   Std.Ord.fromCompare T.%compare T.%equal T.%flip T.%trans
        let instance = format!("{ty_name}.%instOrd");
        let ty = with_params(s.app(s.var("Std.Ord"), vec![this.clone()]));
        let body = call("Std.Ord.fromCompare", &[&compare, &equal, &flip, &trans]);
        out.push((
            signature(&instance, ty, true),
            vec![equation(&instance, Vec::new(), body)],
        ));
        out
    }
}

/// Builds source at one place.
struct Src {
    span: Span,
}

impl Src {
    fn n(&self, text: &str) -> ast::Name {
        ast::Name {
            text: text.to_string(),
            span: self.span,
        }
    }

    fn var(&self, text: &str) -> Expr {
        Expr::Var(self.n(text))
    }

    fn app(&self, head: Expr, args: Vec<Expr>) -> Expr {
        args.into_iter()
            .fold(head, |f, a| Expr::App(Box::new(f), Box::new(a)))
    }

    fn eq(&self, a: Expr, b: Expr) -> Expr {
        Expr::Binary(BinOp::Eq, Box::new(a), Box::new(b))
    }

    fn arrow(&self, a: Expr, b: Expr) -> Expr {
        Expr::Arrow(Box::new(a), Box::new(b))
    }

    fn lam(&self, names: &[&str], body: Expr) -> Expr {
        Expr::Lam(
            names.iter().map(|x| self.n(x)).collect(),
            Box::new(body),
            self.span,
        )
    }

    fn pi(&self, names: &[&str], implicit: bool, auto: bool, dom: Expr, cod: Expr) -> Expr {
        Expr::Pi {
            names: names.iter().map(|x| self.n(x)).collect(),
            implicit,
            auto,
            dom: Box::new(dom),
            cod: Box::new(cod),
            span: self.span,
        }
    }
}
