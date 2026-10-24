//! A derived `Show` instance for data types and records declared in a
//! program: `T.%instShow`, made from `T.%show`, which gives both `toText`
//! and `toSource` (docs/proposals/interfaces.md §5.14: for everything but
//! `Text` and `Char` the two agree). Generated as source, like the derived
//! `DecEq` (`derive.rs`), and elaborated like any definition.
//!
//! It's derived when `T` is declared, for a type with constructors (not a
//! proposition, not defined together with other types, without indices)
//! whose data fields are `T` itself, with the same parameters, or have a
//! `Show` instance, given one for each parameter that's a type. Proof fields
//! are left out. Anything else (a function, a type, a field whose type
//! depends on an earlier one, `T` inside another type) stops derivation,
//! and why not is kept for the note when `${…}` is used on `T`.
//!
//! Elements are shown with `toSource`. A constructor is its name, then its
//! fields, each in brackets when it has spaces and isn't already one piece
//! (`Node (Leaf 1) (Leaf 2)`, `Some (-5)`); a record is `{ name = "tea",
//! price = 3 }`, and `{}` with nothing to show.
//!
//! ```text
//! T.%show : [%p0 : _] -> [auto show: Std.Show %p0] -> (%r : T %p0) -> Std.Text
//! T.%show (C a0 a1) = "C " ++ Show.arg (Show.toSource a0) ++ " " ++ …
//! instance T.%instShow : … -> Std.Show (T %p0) := { toText = T.%show, toSource = T.%show }
//! ```

use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Bracket, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::{Elaborator, Global, Result, interfaces};

/// How the derived `Show` treats one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
enum Field {
    /// It's `T` again: a recursive call.
    Recursive,
    /// Its type has a `Show` instance, which `Show.toSource` finds.
    Shown,
    /// A proof: left out.
    Proof,
}

struct Plan {
    /// Which parameters (types) take a `Show` dictionary: those fields use.
    dicts: Vec<bool>,
    fields: Vec<Vec<Field>>,
}

type Equations = (Decl, Vec<Decl>);

impl Elaborator {
    /// After data type or record `d` is admitted: its `Show` instance, if
    /// one can be derived, or else why not.
    pub(crate) fn derive_data_show(&mut self, d: DataId) -> Result<()> {
        let data = self.globals.data(d);
        let generated = !data.record && data.ctors.iter().any(|c| c.name.starts_with('%'));
        let Some(show) = interfaces::show(self) else {
            return Ok(());
        };
        if self.loading_prelude || generated || self.declares_instance_of(show) {
            return Ok(());
        }
        let plan = match self.show_plan(d, show)? {
            Ok(plan) => plan,
            Err(why) => {
                self.no_show.insert(d, why);
                return Ok(());
            }
        };
        self.clear_metas();
        let (function, instance) = self.show_source(d, &plan);
        let mut result = self.definition(&function.0, &function.1);
        self.clear_metas();
        result = result.and_then(|()| self.definition(&instance.0, &instance.1));
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if e.code == "E-RESOURCE" => return Err(e),
            Err(e) => {
                self.no_show
                    .insert(d, format!("deriving it failed: {}", e.message));
            }
        }
        Ok(())
    }

    fn show_plan(&mut self, d: DataId, show: DataId) -> Result<std::result::Result<Plan, String>> {
        let g = &self.globals;
        let data = g.data(d);
        let name = data.name.to_string();
        let np = data.params.len();
        if data.group.len() > 1 {
            return Ok(Err(format!(
                "`{name}` is defined together with other types, which `Show` isn't derived for yet"
            )));
        }
        if data.sort == Sort::Prop {
            return Ok(Err(format!("`{name}` is a proposition")));
        }
        if !data.indices.is_empty() {
            return Ok(Err(format!(
                "`{name}` has indices, which `Show` isn't derived for yet"
            )));
        }
        if data.ctors.is_empty() {
            return Ok(Err(format!("`{name}` has no constructors")));
        }
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = data.params.iter().map(|(_, t)| is_type(t)).collect();
        let mut dicts = vec![false; np];
        let mut fields = Vec::new();
        let mut to_show: Vec<(Value, String)> = Vec::new();
        for ctor in &data.ctors {
            let mut kinds = Vec::new();
            for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                let what = if data.record {
                    format!("its field `{field}`")
                } else {
                    format!("the field `{field}` of `{}`", ctor.name)
                };
                if ctor.field_erased[i] {
                    if ctor.field_sorts[i] != Sort::Prop {
                        return Ok(Err(format!("{what} is a type, which `Show` can't show")));
                    }
                    kinds.push(Field::Proof);
                    continue;
                }
                if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                    return Ok(Err(format!(
                        "the type of {what} depends on an earlier field, which `Show` isn't \
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
                        "{what} is a function, and functions can't be shown"
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
                        "{what} contains `{name}` inside another type, which `Show` isn't \
                         derived for yet"
                    )));
                }
                for j in 0..np {
                    if ty.mentions(i + np - 1 - j) {
                        dicts[j] |= param_is_type[j];
                    }
                }
                kinds.push(Field::Shown);
                to_show.push((value, what));
            }
            fields.push(kinds);
        }
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
                        format!("%show{j}").as_str().into(),
                        Value::Data(show, vec![Value::var(j)]),
                    );
                }
            }
            for (ty, what) in to_show {
                let goal = Value::Data(show, vec![ty.clone()]);
                if let Some(e) = interfaces::findable(&mut cx, &goal)? {
                    let mut reason = format!(
                        "{what} has type `{}`, which has no `Show` instance (when `{name}` was \
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
            None => Ok(Plan { dicts, fields }),
        })
    }

    /// The source of `T.%show` and of `T.%instShow`, each a signature and
    /// its equations.
    fn show_source(&self, d: DataId, plan: &Plan) -> (Equations, Equations) {
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
            attrs: Vec::new(),
            span,
        };
        let text = |s: &str| Expr::Str(s.to_string(), span);
        let np = data.params.len();
        let param = |j: usize| format!("%p{j}");
        let a = |k: usize| format!("%a{k}");
        let show_name = format!("{ty_name}.%show");
        let dicts: Vec<usize> = (0..np).filter(|j| plan.dicts[*j]).collect();
        let dict = |j: usize| {
            if dicts.len() == 1 {
                "show".to_string()
            } else {
                let p = data.params[j].0.to_string();
                let mut chars = p.chars();
                match chars.next() {
                    Some(c) => format!("show{}{}", c.to_uppercase(), chars.as_str()),
                    None => format!("show{j}"),
                }
            }
        };
        let with_params = |rest: Expr| {
            let mut ty = rest;
            for &j in dicts.iter().rev() {
                let dom = apps(var("Std.Show"), vec![var(&param(j))]);
                ty = pi(&dict(j), true, true, dom, ty);
            }
            for j in (0..np).rev() {
                ty = pi(&param(j), true, false, Expr::Hole(span), ty);
            }
            ty
        };
        let this = apps(
            var(&ty_name),
            (0..np)
                .map(|j| {
                    if data.auto_params.get(j) == Some(&true) {
                        Expr::NamedArg(
                            n(&data.params[j].0),
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
        let ty = with_params(Expr::Pi {
            names: vec![n("%r")],
            implicit: false,
            auto: false,
            dom: Box::new(this.clone()),
            cod: Box::new(var("Std.Text")),
            span,
        });
        let name = n(&show_name);
        let sig = signature(&name, ty, false);

        let mut equations = Vec::new();
        for (c, ctor) in data.ctors.iter().enumerate() {
            let kinds = &plan.fields[c];
            let count = ctor.fields.len();
            let ctor_name = format!("{ty_name}.{}", ctor.name);
            let pattern = Pattern::Ctor(
                n(&ctor_name),
                (0..count).map(|k| Pattern::Var(n(&a(k)))).collect(),
                span,
            );
            let shown: Vec<usize> = (0..count).filter(|k| kinds[*k] != Field::Proof).collect();
            let element = |k: usize| {
                if kinds[k] == Field::Recursive {
                    apps(var(&show_name), vec![var(&a(k))])
                } else {
                    apps(var("Std.Show.toSource"), vec![var(&a(k))])
                }
            };
            let mut pieces: Vec<Expr> = Vec::new();
            if data.record {
                if shown.is_empty() {
                    pieces.push(text("{}"));
                } else {
                    for (i, &k) in shown.iter().enumerate() {
                        let open = if i == 0 { "{ " } else { ", " };
                        pieces.push(text(&format!("{open}{} = ", ctor.fields[k].0)));
                        pieces.push(element(k));
                    }
                    pieces.push(text(" }"));
                }
            } else {
                pieces.push(text(&ctor.name));
                for &k in &shown {
                    pieces.push(text(" "));
                    pieces.push(apps(var("Std.Show.arg"), vec![element(k)]));
                }
            }
            let mut pieces = pieces.into_iter().rev();
            let mut body = pieces.next().expect("at least one piece");
            for lhs in pieces {
                body = apps(var("Std.Text.append"), vec![lhs, body]);
            }
            equations.push(Decl::Equation {
                name: name.clone(),
                patterns: vec![pattern],
                rhs: Some(body),
                arm: None,
                span,
            });
        }
        let instance_name = n(&format!("{ty_name}.%instShow"));
        let instance_ty = with_params(apps(var("Std.Show"), vec![this]));
        let instance = (
            signature(&instance_name, instance_ty, true),
            vec![Decl::Equation {
                name: instance_name,
                patterns: Vec::new(),
                rhs: Some(Expr::Record {
                    base: None,
                    fields: vec![
                        (n("toText"), var(&show_name)),
                        (n("toSource"), var(&show_name)),
                    ],
                    span,
                }),
                arm: None,
                span,
            }],
        );
        ((sig, equations), instance)
    }

    /// Whether the module item being checked (a data type) has an instance
    /// of `interface` declared by its module, by the names in the module's
    /// instance declarations (§5.11).
    pub(crate) fn declares_instance_of(&self, interface: DataId) -> bool {
        let Some(item) = self.module.item else {
            return false;
        };
        self.module.items.iter().any(|i| {
            i.instance
                && i.interface == Some(Global::Data(interface))
                && i.head == Some(Global::Unchecked(item))
        })
    }
}
