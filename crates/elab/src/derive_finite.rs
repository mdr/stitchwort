//! A derived `Finite` instance for data types and records declared in a
//! program (docs/proposals/decide.md §6.2, SW-807): `T.%instFinite`, made of
//! `T.%all`, a list of every value, and `T.%complete`, the proof that every
//! value is on it. Generated as source, like the derived `DecEq`
//! (`derive.rs`), and elaborated like any definition, so the kernel checks
//! the proof.
//!
//! It's derived when `T` is declared, for a type with constructors (not a
//! proposition, not defined together with other types, without indices) that
//! isn't recursive and whose fields are all data with a `Finite` instance,
//! given one for each parameter that's a type the fields use (`[auto fin:
//! Finite a]`), none depending on an earlier field. A proof field, a
//! function, a type, `Nat` or `T` itself stops it, and why not is kept for
//! the note when an instance is wanted (`E-INSTANCE-NONE`). The library's
//! types are skipped (`Bool`, `Ordering`, `Option` and pairs have instances
//! written by hand in core/Finite.sw), as is a type whose module declares its
//! own instance.
//!
//! `all` lists the constructors in the order they're declared, each with
//! every value of its fields, the first field varying slowest: the order the
//! derived `<` puts them in when the fields' lists are in theirs. An
//! enumeration's is the list of its constructors. Otherwise a constructor
//! without fields is a `Cons` cell, and one with fields is its *part*, a
//! `concatMap` over each field's `Finite.all`, appended to what follows. For
//! `type K = | A | B (x: X) (y: Y) | C`:
//!
//! ```text
//! K.%B%F%0 : Type := X                      -- each field's type, so source can name it
//! K.%B%F%1 : X -> Type := Y
//! K.%part%1%1 : (%a0 : K.%B%F%0) -> List K := List.concatMap Finite.all ((%a1 : K.%B%F%1 %a0) => ([K.B %a0 %a1] : List K))
//! K.%part%1   : List K := List.concatMap Finite.all ((%a0 : K.%B%F%0) => K.%part%1%1 %a0)
//! K.%all%2    : List K := Cons K.C Nil      -- what follows a constructor with fields
//! K.%all      : List K := Cons K.A (List.append K.%part%1 K.%all%2)
//!
//! K.%complete : (%x : K) -> List.Mem %x K.%all
//! K.%complete K.A = Inl rfl
//! K.%complete (K.B %a0 %a1) =
//!   Inr (List.memAppendLeft (K.B %a0 %a1) K.%part%1 K.%all%2
//!     (List.memConcatMap ((%a0 : …) => K.%part%1%1 %a0) %a0 (K.B %a0 %a1) Finite.all (Finite.complete %a0)
//!       (List.memConcatMap ((%a1 : …) => ([K.B %a0 %a1] : List K)) %a1 (K.B %a0 %a1) Finite.all (Finite.complete %a1) (Inl rfl))))
//! K.%complete K.C = Inr (List.memAppendRight K.C K.%part%1 K.%all%2 (Inl rfl))
//!
//! instance K.%instFinite : Finite K := { all = K.%all, complete = K.%complete }
//! ```
//!
//! The proof of each value's membership walks the list to its constructor
//! (an `Inr` past each constructor without fields, `memAppendRight` past each
//! with), then down its fields, one `memConcatMap` and the field's own
//! `Finite.complete` per field: nothing is computed and nothing is searched
//! but the fields' instances. Its size is linear in the fields, and in the
//! constructors but for a run of constructors without fields, which is a
//! chain of `Inr`s, as a hand-written proof is.
//!
//! Everything a proof's arguments mention is named, and every generated name
//! gets `T`'s parameters and dictionaries by name: the elaborator checks an
//! application's arguments before its result type meets the expected one, so
//! `_` there would be unsolved, and an instance still to be found inside a
//! lambda can't be matched with another (each part's level is its own
//! definition so that its `Finite.all` is found there).
//!
//! Names generated here contain `%`, which source can't write, so they never
//! clash with the user's.

use std::rc::Rc;

use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{Bracket, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::derive_ord::Src;
use crate::{Elaborator, Global, Result, interfaces, kernel};

type Definition = (Decl, Vec<Decl>);

/// What a derived `Finite` for a data type is made from.
struct Plan {
    /// Which parameters (types) take a `Finite` dictionary: those fields use.
    dicts: Vec<bool>,
}

impl Elaborator {
    /// After data type or record `d` is admitted: its `Finite` instance, if
    /// one can be derived, or else why not.
    pub(crate) fn derive_data_finite(&mut self, d: DataId) -> Result<()> {
        let data = self.globals.data(d);
        let generated = !data.record && data.ctors.iter().any(|c| c.name.starts_with('%'));
        let Some(finite) = interfaces::finite(self) else {
            return Ok(());
        };
        if self.loading_prelude || generated || self.declares_instance_of(finite) {
            return Ok(());
        }
        let plan = match self.finite_plan(d, finite)? {
            Ok(plan) => plan,
            Err(why) => {
                self.no_finite.insert(d, why);
                return Ok(());
            }
        };
        let ctors: Vec<usize> = self
            .globals
            .data(d)
            .ctors
            .iter()
            .map(|c| c.fields.len())
            .collect();
        for (c, count) in ctors.into_iter().enumerate() {
            for k in 0..count {
                self.derive_field_type(d, c, k)?;
            }
        }
        let mut result = Ok(());
        for definition in self.finite_source(d, &plan) {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&definition.0, &definition.1));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if e.code == "E-RESOURCE" => return Err(e),
            Err(e) => {
                self.no_finite
                    .insert(d, format!("deriving it failed: {}", e.message));
            }
        }
        Ok(())
    }

    /// Why `Finite` can't be derived for `d`, or which parameters take a
    /// dictionary.
    fn finite_plan(
        &mut self,
        d: DataId,
        finite: DataId,
    ) -> Result<std::result::Result<Plan, String>> {
        let g = &self.globals;
        let data = g.data(d);
        let name = data.name.to_string();
        let np = data.params.len();
        if data.group.len() > 1 {
            return Ok(Err(format!(
                "`{name}` is defined together with other types, which `Finite` isn't derived \
                 for yet"
            )));
        }
        if data.sort == Sort::Prop {
            return Ok(Err(format!("`{name}` is a proposition")));
        }
        if !data.indices.is_empty() {
            return Ok(Err(format!(
                "`{name}` has indices, which `Finite` isn't derived for yet; declare an instance"
            )));
        }
        if data.ctors.is_empty() {
            return Ok(Err(format!(
                "`{name}` has no constructors, which `Finite` isn't derived for yet"
            )));
        }
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = data.params.iter().map(|(_, t)| is_type(t)).collect();
        let mut dicts = vec![false; np];
        let mut to_find: Vec<(Value, String)> = Vec::new();
        for ctor in &data.ctors {
            for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                let what = if data.record {
                    format!("its field `{field}`")
                } else {
                    format!("the field `{field}` of `{}`", ctor.name)
                };
                if ty
                    .subterms()
                    .any(|(t, _)| matches!(t, Term::Data(e, _) if *e == d))
                {
                    return Ok(Err(format!(
                        "it's recursive ({what} holds a `{name}`), so there's no list of every \
                         value"
                    )));
                }
                if ctor.field_erased[i] {
                    if ctor.field_sorts[i] == Sort::Prop {
                        return Ok(Err(format!(
                            "{what} is a proof, which `Finite` isn't derived for yet"
                        )));
                    }
                    return Ok(Err(format!(
                        "{what} is a type, and there's no list of every type"
                    )));
                }
                if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                    return Ok(Err(format!(
                        "the type of {what} depends on an earlier field, which `Finite` isn't \
                         derived for yet"
                    )));
                }
                let env: Vec<Value> = (0..np)
                    .map(Value::var)
                    .chain((0..i).map(|_| unused()))
                    .collect();
                let value = force(g, eval(g, &env, ty)?)?;
                if matches!(value, Value::Pi(..)) {
                    return Ok(Err(format!(
                        "{what} is a function, and there's no list of every function"
                    )));
                }
                for j in 0..np {
                    if ty.mentions(i + np - 1 - j) {
                        dicts[j] |= param_is_type[j];
                    }
                }
                to_find.push((value, what));
            }
        }
        self.clear_metas();
        let span = self.globals.data(d).span;
        let params = self.globals.data(d).params.clone();
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
                        format!("%finite{j}").as_str().into(),
                        Value::Data(finite, vec![Value::var(j)]),
                    );
                }
            }
            for (ty, what) in to_find {
                let goal = Value::Data(finite, vec![ty.clone()]);
                if let Some(e) = interfaces::findable(&mut cx, &goal)? {
                    let mut reason = format!(
                        "{what} has type `{}`, which has no `Finite` instance (when `{name}` was \
                         declared)",
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
            None => Ok(Plan { dicts }),
        })
    }

    /// Declares `T.%C%F%k : (params) -> (fields before k) -> Sort`, the
    /// type of field `k` of `C`, all its arguments explicit, so source can
    /// name it (as `T.%C%P%k` does for a proof field, `derive.rs`).
    fn derive_field_type(&mut self, d: DataId, c: usize, k: usize) -> Result<()> {
        let data = self.globals.data(d);
        let ctor = &data.ctors[c];
        let member = format!("%{}%F%{k}", ctor.name);
        if self.has_member(d, &member) {
            return Ok(());
        }
        let binders: Vec<(Name, Term)> = data
            .params
            .iter()
            .chain(&ctor.fields[..k])
            .cloned()
            .collect();
        let mut ty = Term::Sort(ctor.field_sorts[k]);
        let mut body = ctor.fields[k].1.clone();
        for (x, t) in binders.iter().rev() {
            ty = Term::Pi(x.clone(), Icit::Explicit, Rc::new(t.clone()), Rc::new(ty));
            body = Term::Lam(x.clone(), Icit::Explicit, Rc::new(body));
        }
        let name: Name = format!("{}.{member}", data.name).into();
        let span = data.span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
        kernel::define_def(&mut self.globals, id, &body)?;
        let key = Self::member_key(&self.data_key(d), &member);
        self.scope.insert(&key, Global::Def(id), span, false);
        Ok(())
    }

    /// The source of each constructor's part and its levels (`T.%part%c`,
    /// `T.%part%c%j`), the lists after constructors with fields
    /// (`T.%all%c`), `T.%all`, `T.%complete` and `T.%instFinite`, in an order
    /// where each uses only those before it.
    fn finite_source(&self, d: DataId, plan: &Plan) -> Vec<Definition> {
        let data = self.globals.data(d);
        let ty_name = self.relative_to_root(&data.name);
        let s = Src { span: data.span };
        let np = data.params.len();
        let ctors = &data.ctors;
        let n = ctors.len();
        let dicts: Vec<usize> = (0..np).filter(|j| plan.dicts[*j]).collect();
        let param = |j: usize| format!("%p{j}");
        let dict = |j: usize| {
            if dicts.len() == 1 {
                "fin".to_string()
            } else {
                let p = data.params[j].0.to_string();
                let mut chars = p.chars();
                match chars.next() {
                    Some(ch) => format!("fin{}{}", ch.to_uppercase(), chars.as_str()),
                    None => format!("fin{j}"),
                }
            }
        };
        let with_params = |rest: Expr| {
            let mut ty = rest;
            for &j in dicts.iter().rev() {
                let dom = s.app(s.var("Std.Finite"), vec![s.var(&param(j))]);
                ty = s.pi(&[&dict(j)], true, true, dom, ty);
            }
            for j in (0..np).rev() {
                ty = s.pi(&[&param(j)], true, false, Expr::Hole(s.span), ty);
            }
            ty
        };
        // A generated name, with `T`'s parameters and dictionaries given by
        // name, so nothing is left to find.
        let by_name = |x: &str| Expr::NamedArg(s.n(x), Box::new(s.var(x)), s.span, Bracket::Square);
        let generated = |name: &str| {
            let mut args: Vec<Expr> = (0..np).map(|j| by_name(&param(j))).collect();
            args.extend(dicts.iter().map(|&j| by_name(&dict(j))));
            s.app(s.var(name), args)
        };
        let this = s.this(&ty_name, data);
        let list_of_this = || s.app(s.var("Std.List"), vec![this.clone()]);
        let member = |m: &str| format!("{ty_name}.%{m}");
        let part = |c: usize, j: usize| {
            if j == 0 {
                member(&format!("part%{c}"))
            } else {
                member(&format!("part%{c}%{j}"))
            }
        };
        let tail = |c: usize| member(&format!("all%{c}"));
        let a = |k: usize| format!("%a{k}");
        let ctor = |c: usize| s.var(&format!("{ty_name}.{}", ctors[c].name));
        let has_fields = |c: usize| !ctors[c].fields.is_empty();
        // `C %a0 …`, a value of constructor `c`.
        let value = |c: usize| {
            s.app(
                ctor(c),
                (0..ctors[c].fields.len()).map(|k| s.var(&a(k))).collect(),
            )
        };
        // The type of field `k` of `c`: `T.%C%F%k %p0 … %a0 …`.
        let field_ty = |c: usize, k: usize| {
            s.app(
                s.var(&member(&format!("{}%F%{k}", ctors[c].name))),
                (0..np)
                    .map(|j| s.var(&param(j)))
                    .chain((0..k).map(|i| s.var(&a(i))))
                    .collect(),
            )
        };
        // Level `j` of `c`'s part takes field `j`: `(%aj : …) => …`, the
        // next level applied to the fields so far, or at the last, the value.
        let level = |c: usize, j: usize| {
            let count = ctors[c].fields.len();
            let next = if j + 1 < count {
                s.app(
                    generated(&part(c, j + 1)),
                    (0..=j).map(|i| s.var(&a(i))).collect(),
                )
            } else {
                Expr::Ann(
                    Box::new(s.app(
                        s.var("Std.List.Cons"),
                        vec![value(c), s.var("Std.List.Nil")],
                    )),
                    Box::new(list_of_this()),
                    s.span,
                )
            };
            s.typed_lam(&a(j), field_ty(c, j), next)
        };
        // The list from constructor `c` on: a `Cons` for each constructor
        // without fields, then the end, or a constructor with fields, whose
        // part is appended to the (named) list after it.
        let from = |c: usize| -> Expr {
            let mut k = c;
            let mut cells = Vec::new();
            let mut list = s.var("Std.List.Nil");
            while k < n {
                if has_fields(k) {
                    list = if k + 1 == n {
                        generated(&part(k, 0))
                    } else {
                        s.app(
                            s.var("Std.List.append"),
                            vec![generated(&part(k, 0)), generated(&tail(k + 1))],
                        )
                    };
                    break;
                }
                cells.push(k);
                k += 1;
            }
            for k in cells.into_iter().rev() {
                list = s.app(s.var("Std.List.Cons"), vec![ctor(k), list]);
            }
            list
        };
        let list_def = |name: &str, body: Expr| -> Definition {
            (
                s.signature(name, with_params(list_of_this()), false),
                vec![s.equation(name, Vec::new(), body)],
            )
        };
        let mut out: Vec<Definition> = Vec::new();
        // Each part, its last level first: `T.%part%c%j %a0 … = List.concatMap
        // Finite.all (level j)`.
        for (c, ctor_c) in ctors.iter().enumerate() {
            let count = ctor_c.fields.len();
            for j in (0..count).rev() {
                let name = part(c, j);
                let mut ty = list_of_this();
                for k in (0..j).rev() {
                    ty = s.pi(&[&a(k)], false, false, field_ty(c, k), ty);
                }
                let body = s.app(
                    s.var("Std.List.concatMap"),
                    vec![s.var("Std.Finite.all"), level(c, j)],
                );
                out.push((
                    s.signature(&name, with_params(ty), false),
                    vec![s.equation(
                        &name,
                        (0..j).map(|k| Pattern::Var(s.n(&a(k)))).collect(),
                        body,
                    )],
                ));
            }
        }
        // A list after a constructor with fields is named (unless it's the
        // end); last first, as each uses the ones after it.
        for c in (1..n).rev() {
            if has_fields(c - 1) {
                out.push(list_def(&tail(c), from(c)));
            }
        }
        out.push(list_def(&member("all"), from(0)));
        // `C %a0 … ∈ T.%all`, for the fields as variables.
        let in_all = |x: Expr| s.app(s.var("Std.List.Mem"), vec![x, generated(&member("all"))]);
        // `(%a0 : …) -> … -> rest`, over `c`'s fields.
        let over_fields = |c: usize, rest: Expr| {
            let mut ty = rest;
            for k in (0..ctors[c].fields.len()).rev() {
                ty = s.pi(&[&a(k)], false, false, field_ty(c, k), ty);
            }
            ty
        };
        let mem = |c: usize| member(&format!("mem%{c}"));
        // `T.%mem%c`: each constructor's values are on the list, walked to
        // the constructor, then down its fields.
        for (c, ctor_c) in ctors.iter().enumerate() {
            // Down the fields: `C %a0 …` is in its part.
            let count = ctor_c.fields.len();
            let mut proof = s.app(s.var("Std.Or.Inl"), vec![s.var("rfl")]);
            for j in (0..count).rev() {
                proof = s.app(
                    s.var("Std.List.memConcatMap"),
                    vec![
                        level(c, j),
                        s.var(&a(j)),
                        value(c),
                        s.var("Std.Finite.all"),
                        s.app(s.var("Std.Finite.complete"), vec![s.var(&a(j))]),
                        proof,
                    ],
                );
            }
            if has_fields(c) && c + 1 < n {
                proof = s.app(
                    s.var("Std.List.memAppendLeft"),
                    vec![
                        value(c),
                        generated(&part(c, 0)),
                        generated(&tail(c + 1)),
                        proof,
                    ],
                );
            }
            // Back up the list, past each constructor before `c`.
            for k in (0..c).rev() {
                proof = if has_fields(k) {
                    s.app(
                        s.var("Std.List.memAppendRight"),
                        vec![
                            value(c),
                            generated(&part(k, 0)),
                            generated(&tail(k + 1)),
                            proof,
                        ],
                    )
                } else {
                    s.app(s.var("Std.Or.Inr"), vec![proof])
                };
            }
            let name = mem(c);
            out.push((
                s.signature(&name, with_params(over_fields(c, in_all(value(c)))), false),
                vec![s.equation(
                    &name,
                    (0..count).map(|k| Pattern::Var(s.n(&a(k)))).collect(),
                    proof,
                )],
            ));
        }
        // `T.%cover`: what holds of each constructor's values holds of every
        // value. The match is here, on a statement `%P` that is a variable:
        // matching in `T.%complete` itself would have the kernel refine the
        // list in its statement in every branch, which costs as much as the
        // list is long.
        let cover = member("cover");
        let motive = "%P";
        let case = |c: usize| format!("%c{c}");
        let mut cover_ty = s.pi(
            &["%x"],
            false,
            false,
            this.clone(),
            s.app(s.var(motive), vec![s.var("%x")]),
        );
        for c in (0..n).rev() {
            let dom = over_fields(c, s.app(s.var(motive), vec![value(c)]));
            cover_ty = s.pi(&[&case(c)], false, false, dom, cover_ty);
        }
        let motive_ty = s.arrow(this.clone(), Expr::Prop(s.span));
        cover_ty = s.pi(&[motive], false, false, motive_ty, cover_ty);
        for j in (0..np).rev() {
            cover_ty = s.pi(&[&param(j)], true, false, Expr::Hole(s.span), cover_ty);
        }
        let cover_equations = (0..n)
            .map(|c| {
                let count = ctors[c].fields.len();
                let mut patterns = vec![Pattern::Var(s.n(motive))];
                patterns.extend((0..n).map(|k| Pattern::Var(s.n(&case(k)))));
                patterns.push(Pattern::Ctor(
                    s.n(&format!("{ty_name}.{}", ctors[c].name)),
                    (0..count).map(|k| Pattern::Var(s.n(&a(k)))).collect(),
                    s.span,
                ));
                s.equation(
                    &cover,
                    patterns,
                    s.app(s.var(&case(c)), (0..count).map(|k| s.var(&a(k))).collect()),
                )
            })
            .collect();
        out.push((s.signature(&cover, cover_ty, false), cover_equations));
        // `T.%complete`: `T.%cover` of the constructors' `T.%mem%c`.
        let complete = member("complete");
        let complete_ty =
            with_params(s.pi(&["%x"], false, false, this.clone(), in_all(s.var("%x"))));
        let mut args = vec![s.lam(&["%x"], in_all(s.var("%x")))];
        args.extend((0..n).map(|c| generated(&mem(c))));
        let params_by_name: Vec<Expr> = (0..np).map(|j| by_name(&param(j))).collect();
        let body = s.app(s.app(s.var(&cover), params_by_name), args);
        out.push((
            s.signature(&complete, complete_ty, false),
            vec![s.equation(&complete, Vec::new(), body)],
        ));
        let instance = member("instFinite");
        let instance_ty = with_params(s.app(s.var("Std.Finite"), vec![this]));
        let body = Expr::Record {
            base: None,
            fields: vec![
                (s.n("all"), generated(&member("all"))),
                (s.n("complete"), generated(&complete)),
            ],
            span: s.span,
        };
        out.push((
            s.signature(&instance, instance_ty, true),
            vec![s.equation(&instance, Vec::new(), body)],
        ));
        out
    }
}
