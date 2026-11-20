//! A derived `Show` instance for data types and records declared in a
//! program: `T.%instShow`, made from `T.%show`, which gives both `toText`
//! and `toSource` (docs/proposals/interfaces.md §5.14: for everything but
//! `Text` and `Char` the two agree). Generated as source, like the derived
//! `DecEq` (`derive.rs`), and elaborated like any definition.
//!
//! It's derived when `T` is declared, for a type with constructors (not a
//! proposition, without indices) whose data fields are `T` itself or a type
//! defined together with it, with the same parameters, one of those inside
//! another data type (as for `DecEq`, `derive.rs`), or have a `Show`
//! instance, given one for each parameter that's a type. Proof fields are
//! left out. Anything else (a function, a type, a field whose type depends
//! on an earlier one, `T` inside a container whose `Show` its module wrote)
//! stops derivation, and why not is kept for the note when `${…}` is used
//! on `T`. Types defined together are derived together, unless one of them
//! has its own `Show`.
//!
//! A nested type gets a function for each container it's in, defined
//! together with `T.%show`, as for `DecEq` (`derive.rs`): `T.%m1%show`,
//! which prints the container as its own instance does: a list `[x, y]`
//! (with `T.%m1%items` for the elements after the first, as `Show.items`),
//! a pair `(x, y)`, an option `None` or `Some x` (bracketed by `Show.arg`),
//! and another type as its derived `Show` prints it.
//!
//! Elements are shown with `toSource`. A constructor is its name, then its
//! fields, each in brackets when it has spaces and isn't already one piece
//! (`Node (Leaf 1) (Leaf 2)`, `Some (-5)`, `Some { price = 3 }`); a
//! constructor declared with its fields in braces is shown by field name,
//! `Meeting { title = "a" }`; a record is `{ name = "tea", price = 3 }`, and
//! `{}` with nothing to show.
//!
//! ```text
//! T.%show : [%p0 : _] -> [auto show: Std.Show %p0] -> (%r : T %p0) -> Std.Text
//! T.%show (C a0 a1) = "C " ++ Show.arg (Show.toSource a0) ++ " " ++ …
//! instance T.%instShow : … -> Std.Show (T %p0) := { toText = T.%show, toSource = T.%show }
//! ```

use crate::check::quote_internal;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{eval, force, unused};
use stitchwort_core::{DataId, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Decl, Expr, Pattern};

use crate::check::Ctx;
use crate::derive::{Member, member_of};
use crate::{Elaborator, Global, Result, interfaces};

/// How the derived `Show` treats one field of a constructor.
#[derive(Clone, Copy, PartialEq)]
enum Field {
    /// It's a type of the group again, or a container of one: member `m`
    /// of [`Plan::members`], a call to that member's function.
    Recursive(usize),
    /// Its type has a `Show` instance, which `Show.toSource` finds.
    Shown,
    /// A proof: left out.
    Proof,
}

struct Plan {
    /// Which parameters (types) take a `Show` dictionary: those fields use.
    dicts: Vec<bool>,
    /// The group's types (the first `roots`), then the containers they're
    /// nested in, as for `DecEq` (`derive.rs`).
    members: Vec<Member>,
    /// For each member, for each of its constructors, each field's.
    fields: Vec<Vec<Vec<Field>>>,
    roots: usize,
}

type Equations = (Decl, Vec<Decl>);

impl Elaborator {
    /// After data type or record `d` is admitted: its `Show` instance, if
    /// one can be derived, or else why not. The types of a group are
    /// derived together, once the last of them is admitted.
    pub(crate) fn derive_data_show(&mut self, d: DataId) -> Result<()> {
        let data = self.kernel.data(d);
        let generated = !data.record() && data.ctors().iter().any(|c| c.name.starts_with('%'));
        let Some(show) = interfaces::show(self) else {
            return Ok(());
        };
        if generated || data.group().last() != Some(&d) {
            return Ok(());
        }
        let (group, own) = self.group_and_own(d, show);
        if own.iter().all(|x| *x) {
            return Ok(());
        }
        let refuse = |e: &mut Self, why: String| {
            e.refuse_group(crate::derive::Derivation::Show, &group, &own, &why)
        };
        if let Some(r) = group
            .iter()
            .zip(&own)
            .find_map(|(r, own)| own.then_some(*r))
        {
            let why = format!(
                "`{}`, defined together with it, has its module's own `Show` instance, which \
                 the derived ones of the group can't use; declare `Show` for the others too",
                self.kernel.data(r).name()
            );
            refuse(self, why);
            return Ok(());
        }
        let plan = match self.show_plan(d, show)? {
            Ok(plan) => plan,
            Err(why) => {
                refuse(self, why);
                return Ok(());
            }
        };
        self.clear_metas();
        for member in &plan.members[plan.roots..] {
            self.derive_member_helpers(member, false)?;
        }
        self.clear_metas();
        let (functions, instances) = self.show_source(&plan);
        let mut result = self.definitions(&functions);
        for instance in instances {
            self.clear_metas();
            result = result.and_then(|()| self.definition(&instance.0, &instance.1));
        }
        self.clear_metas();
        match result {
            Ok(()) => {}
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => refuse(self, format!("deriving it failed: {}", e.message)),
        }
        Ok(())
    }

    fn show_plan(&mut self, d: DataId, show: DataId) -> Result<std::result::Result<Plan, String>> {
        let g = &self.ev();
        let group: Vec<DataId> = g.data(d).group().to_vec();
        let np = g.data(d).params().len();
        for &r in &group {
            let data = g.data(r);
            let name = data.name().to_string();
            if data.sort() == Sort::Prop {
                return Ok(Err(format!("`{name}` is a proposition")));
            }
            if !data.indices().is_empty() {
                return Ok(Err(format!(
                    "`{name}` has indices, which `Show` isn't derived for yet"
                )));
            }
            if data.ctors().is_empty() {
                return Ok(Err(format!("`{name}` has no constructors")));
            }
        }
        // The group's types and the containers they're nested in.
        let members = match self.members(d, "`Show`", Some("%instShow"))? {
            Ok(members) => members,
            Err(why) => return Ok(Err(why)),
        };
        let g = &self.ev();
        let first = g.data(d);
        let name = first.name().to_string();
        let is_type = |ty: &Term| matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)));
        let param_is_type: Vec<bool> = first.params().iter().map(|(_, t)| is_type(t)).collect();
        let mut dicts = vec![false; np];
        let mut fields: Vec<Vec<Vec<Field>>> = Vec::new();
        let mut to_show: Vec<(Value, String)> = Vec::new();
        for &r in &group {
            let data = g.data(r);
            let mut root_fields = Vec::new();
            for ctor in data.ctors() {
                let mut kinds = Vec::new();
                for (i, (field, ty)) in ctor.fields.iter().enumerate() {
                    let what = crate::derive::field_origin(data, ctor, field, group.len());
                    if ctor.field_erased[i] {
                        if ctor.field_sorts[i] != Sort::Prop {
                            return Ok(Err(format!("{what} is a type, which `Show` can't show")));
                        }
                        kinds.push(Field::Proof);
                        continue;
                    }
                    if (0..i).any(|j| ty.mentions(i - 1 - j)) {
                        return Ok(Err(format!(
                            "the type of {what} depends on an earlier field, which `Show` \
                             isn't derived for yet"
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
                    if crate::derive::mentions_group(ty, &group) {
                        match member_of(g, np, &members, &value)? {
                            Some(m) => kinds.push(Field::Recursive(m)),
                            None => {
                                return Ok(Err(format!(
                                    "{what} contains a type of the group inside another type, \
                                     which `Show` isn't derived for yet"
                                )));
                            }
                        }
                        continue;
                    }
                    for j in 0..np {
                        if ty.mentions(i + np - 1 - j) {
                            dicts[j] |= param_is_type[j];
                        }
                    }
                    kinds.push(Field::Shown);
                    to_show.push((value, what));
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
                    if ctor.field_erased[i] {
                        // A container's proof field is left out, as a
                        // type's own derived `Show` leaves it out.
                        if ctor.field_sorts[i] == Sort::Prop {
                            kinds.push(Field::Proof);
                            continue;
                        }
                    }
                    if ctor.field_erased[i] || (0..i).any(|j| ty.mentions(i - 1 - j)) {
                        return Ok(Err(format!(
                            "{what} is inside `{}`, whose fields `Show` can't show",
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
                            "{what} has a function inside `{}`, and functions can't be shown",
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
                            dicts[j] |= param_is_type[j];
                        }
                    }
                    kinds.push(Field::Shown);
                    to_show.push((value, what.clone()));
                }
                member_fields.push(kinds);
            }
            fields.push(member_fields);
        }
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
                        format!("%show{j}").as_str().into(),
                        Value::Data(show, vec![Value::var(j)].into()),
                    );
                }
            }
            for (ty, what) in to_show {
                let goal = Value::Data(show, vec![ty.clone()].into());
                if let Some(e) = interfaces::findable(&mut cx, &goal)? {
                    // The field's instance has an error: note it so a use
                    // waits for it (SW-3078).
                    if e.code == "E-FAILED-DEPENDENCY" {
                        cx.e.note_derive_waiting(&group, show);
                    }
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
            None => Ok(Plan {
                dicts,
                members,
                fields,
                roots: group.len(),
            }),
        })
    }

    /// The source of `T.%show` and of `T.%instShow`, each a signature and
    /// its equations; for a nested type, `T.%show` is with a function for
    /// each container it's in (`T.%m1%show`, and `T.%m1%items` for a
    /// list), to be defined together.
    fn show_source(&self, plan: &Plan) -> (Vec<Equations>, Vec<Equations>) {
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
        let text = |s: &str| Expr::Str(s.to_string(), span);
        let np = data.params().len();
        let param = |j: usize| format!("%p{j}");
        let a = |k: usize| format!("%a{k}");
        let dicts: Vec<usize> = (0..np).filter(|j| plan.dicts[*j]).collect();
        let dict = |j: usize| {
            if dicts.len() == 1 {
                "show".to_string()
            } else {
                let p = data.params()[j].0.to_string();
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
        let names: Vec<String> = plan.members.iter().map(|m| self.member_names(m)).collect();
        let show_of = |m: usize| format!("{}show", names[m]);
        // `%r : this` to `Std.Text`.
        let function_ty = |this: Expr| {
            with_params(Expr::Pi {
                name: n("%r"),
                implicit: false,
                auto: false,
                dom: Box::new(this),
                cod: Box::new(var("Std.Text")),
                span,
            })
        };
        // The text of the pieces, appended.
        let appended = |pieces: Vec<Expr>| {
            let mut pieces = pieces.into_iter().rev();
            let mut body = pieces.next().expect("at least one piece");
            for lhs in pieces {
                body = apps(var("Std.Text.append"), vec![lhs, body]);
            }
            body
        };
        let equation = |name: &ast::Name, pattern: Pattern, body: Expr| Decl::Equation {
            guard: None,
            name: name.clone(),
            patterns: vec![pattern],
            rhs: Some(body),
            arm: None,
            span,
        };
        let list = self.kernel.env.registry().data(Builtin::List);
        let pair = self.kernel.env.registry().data(Builtin::Pair);

        let mut functions = Vec::new();
        for (m, prefix) in names.iter().enumerate() {
            let prefix = prefix.clone();
            // The type matched on, how source names its constructors, and
            // the member's type: `T %p0 …`, or `T.%m1%type %p0 …`.
            let (matched, ctor_prefix, this) = self.member_shape(&src, &plan.members[m]);
            let member_fields = &plan.fields[m];
            let root = m < plan.roots;
            let ctors = self.kernel.data(matched).ctors();
            let name = n(&show_of(m));
            let pattern = |c: usize| {
                let ctor = &ctors[c];
                Pattern::Ctor(
                    n(&format!("{ctor_prefix}.{}", ctor.name)),
                    (0..ctor.fields.len())
                        .map(|k| Pattern::Var(n(&a(k))))
                        .collect(),
                    span,
                )
            };
            // An element, as source shows it: a member's own function, or
            // its type's `toSource`.
            let element = |c: usize, k: usize| match member_fields[c][k] {
                Field::Recursive(t) => apps(var(&show_of(t)), vec![var(&a(k))]),
                _ => apps(var("Std.Show.toSource"), vec![var(&a(k))]),
            };
            let mut equations = Vec::new();
            if !root && Some(matched) == list {
                // As `List`'s own: `[x, y]`, the elements after the first
                // by `T.%m1%items` (`Show.items`).
                let items = n(&format!("{prefix}items"));
                let (nil, cons) = (pattern(0), pattern(1));
                equations.push(equation(&name, nil.clone(), text("[]")));
                equations.push(equation(
                    &name,
                    cons.clone(),
                    appended(vec![
                        text("["),
                        element(1, 0),
                        apps(var(&items.text), vec![var(&a(1))]),
                        text("]"),
                    ]),
                ));
                functions.push((
                    signature(&name, function_ty(this.clone()), false),
                    equations,
                ));
                let rest = vec![
                    equation(&items, nil, text("")),
                    equation(
                        &items,
                        cons,
                        appended(vec![
                            text(", "),
                            element(1, 0),
                            apps(var(&items.text), vec![var(&a(1))]),
                        ]),
                    ),
                ];
                functions.push((signature(&items, function_ty(this), false), rest));
                continue;
            }
            if !root && Some(matched) == pair {
                // As a pair's own: `(x, y)`.
                equations.push(equation(
                    &name,
                    pattern(0),
                    appended(vec![
                        text("("),
                        element(0, 0),
                        text(", "),
                        element(0, 1),
                        text(")"),
                    ]),
                ));
                functions.push((signature(&name, function_ty(this), false), equations));
                continue;
            }
            // A constructor and its fields (`Option`'s as its own instance
            // shows them: `None`, `Some (Number 1)`), or a record.
            let record = self.kernel.data(matched).record();
            for (c, ctor) in ctors.iter().enumerate() {
                let kinds = &member_fields[c];
                let count = ctor.fields.len();
                let braced = ctor.braced && !ctor.implicit.contains(&true);
                let shown: Vec<usize> = (0..count).filter(|k| kinds[*k] != Field::Proof).collect();
                let mut pieces: Vec<Expr> = Vec::new();
                if record {
                    if shown.is_empty() {
                        pieces.push(text("{}"));
                    } else {
                        for (i, &k) in shown.iter().enumerate() {
                            let open = if i == 0 { "{ " } else { ", " };
                            pieces.push(text(&format!("{open}{} = ", ctor.fields[k].0)));
                            pieces.push(element(c, k));
                        }
                        pieces.push(text(" }"));
                    }
                } else if braced && !shown.is_empty() {
                    // By field name, as it is written: `Meeting { title = "a" }`.
                    pieces.push(text(&ctor.name));
                    for (i, &k) in shown.iter().enumerate() {
                        let open = if i == 0 { " { " } else { ", " };
                        pieces.push(text(&format!("{open}{} = ", ctor.fields[k].0)));
                        pieces.push(element(c, k));
                    }
                    pieces.push(text(" }"));
                } else {
                    pieces.push(text(&ctor.name));
                    for &k in &shown {
                        pieces.push(text(" "));
                        pieces.push(apps(var("Std.Show.arg"), vec![element(c, k)]));
                    }
                }
                equations.push(equation(&name, pattern(c), appended(pieces)));
            }
            functions.push((signature(&name, function_ty(this), false), equations));
        }
        let mut instances = Vec::new();
        for m in 0..plan.roots {
            let (_, ty_name, this) = self.member_shape(&src, &plan.members[m]);
            let show_name = show_of(m);
            let instance_name = n(&format!("{ty_name}.%instShow"));
            let instance_ty = with_params(apps(var("Std.Show"), vec![this]));
            instances.push((
                signature(&instance_name, instance_ty, true),
                vec![Decl::Equation {
                    guard: None,
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
            ));
        }
        (functions, instances)
    }

    /// Whether the module item being checked (a data type) has an instance
    /// of `interface` declared by its module, by the names in the module's
    /// instance declarations (§5.11).
    pub(crate) fn declares_instance_of(&self, interface: DataId) -> bool {
        let Some(item) = self.unit.module.item else {
            return false;
        };
        self.item_declares_instance(item, interface)
    }

    /// [`Self::declares_instance_of`] for data type `d`: for a type of a
    /// group, the module item that declared it, found by its key.
    pub(crate) fn declares_instance_for(&self, d: DataId, interface: DataId) -> bool {
        if self.kernel.data(d).group().len() == 1 {
            return self.declares_instance_of(interface);
        }
        let key = self.data_key(d);
        let item = self
            .unit
            .module
            .item_keys
            .iter()
            .find(|(_, k)| **k == key)
            .map(|(i, _)| *i);
        item.is_some_and(|item| self.item_declares_instance(item, interface))
    }

    /// Whether the module, or an earlier one, declares an instance of
    /// `interface` for data type `d`, whichever type is being derived now.
    pub(crate) fn has_written_instance(&self, d: DataId, interface: DataId) -> bool {
        if self.tables.instances.get(&(interface, d)).is_some() {
            return true;
        }
        let key = self.data_key(d);
        self.unit
            .module
            .item_keys
            .iter()
            .find(|(_, k)| **k == key)
            .is_some_and(|(i, _)| self.item_declares_instance(*i, interface))
    }

    /// Whether the module declares an instance of `interface` for the data
    /// type that `item` declares.
    fn item_declares_instance(&self, item: usize, interface: DataId) -> bool {
        self.unit.module.items.iter().any(|i| {
            i.instance
                && i.interface == Some(Global::Data(interface))
                && i.head == Some(Global::Unchecked(item))
        })
    }
}
