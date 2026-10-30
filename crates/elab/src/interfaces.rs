//! Interfaces and instances (docs/proposals/interfaces.md, stage 1).
//!
//! An interface `interface Pretty (a: Type) = { pretty: a -> Text }` is a
//! record (`records.rs`) the elaborator also remembers as an interface:
//!
//! - each field `f` gets a **method** `Pretty.f: [a: Type] -> [auto pretty:
//!   Pretty a] -> …`, which projects the field from the dictionary it's given
//!   (§5.1). The record's own projections are kept under hidden names
//!   (`Pretty.%f`), for dot notation on a dictionary (`d.pretty`), updates
//!   and patterns;
//! - a field whose type is another interface applied to the parameter is a
//!   **superclass** (§5.8). The superclass graph is acyclic
//!   (`E-INTERFACE-CYCLE`).
//!
//! An `instance` is a definition with a marker. Its signature may only have
//! head variables and prerequisites, and its head must be a nominal type
//! applied to distinct variables (§5.2); it must be declared in the module
//! that owns the interface or the head (§5.6), and there's at most one per
//! interface and head. So finding one is a lookup ([`attempt`], §5.5): the
//! dictionaries in scope first (and their superclass paths), then the one
//! global instance for the head. Every test has three results: a match, a
//! rigid mismatch, or *blocked* on an unknown the test didn't make itself,
//! and a blocked test makes the obligation wait (`auto.rs` retries it in
//! rounds) rather than guess.
//!
//! Nothing here is trusted: the kernel sees records, definitions and their
//! applications, and checks them as usual.

use std::rc::Rc;

use crate::kernel;
use stitchwort_core::value::{Head, conv, force, quote_at_most, unfold_folded};
use stitchwort_core::{DataId, DefId, Icit, Name, Term, Value, pretty};
use stitchwort_syntax::ast::{self, Decl};
use stitchwort_syntax::{Diagnostic, Span};

use crate::auto::Obligation;
use crate::check::{Ctx, Result, implicit_arg};
use crate::unify::rigid_head;
use crate::{Elaborator, Global, error};

/// How many instance steps one obligation, with the prerequisites it
/// creates, may take in all, across every round (§5.5 step 7, D182).
const BUDGET: usize = 10_000;

/// The most nodes [`scanned`] reads back of a normal form.
const SCAN_LIMIT: u64 = 100_000;

/// What the elaborator knows about an interface, beyond its record.
pub(crate) struct InterfaceInfo {
    /// The name of its methods' dictionary parameter: the interface's name
    /// with a lower-case first letter (`pretty` for `Pretty`, D181).
    pub dict: String,
    /// Its superclass fields: each field's index and the parent interface.
    pub supers: Vec<(usize, DataId)>,
    /// Its record's own projections, by field (`Pretty.%pretty`).
    pub projections: Vec<DefId>,
    /// Its methods, by field (`Pretty.pretty`).
    pub methods: Vec<DefId>,
    /// Its relation fields and their deciders (§5.16): `(r, d)` for a field
    /// `r` whose type ends in `Prop` and a field `decR` whose type ends in
    /// `Decidable`, as `lessThan` and `decLessThan` in `Ord`.
    pub relations: Vec<(usize, usize)>,
}

/// What an instance's parameter is.
#[derive(Clone, Copy, Debug)]
pub(crate) enum InstanceParam {
    /// A head variable: argument `k` of the head's type.
    Head(usize),
    /// A prerequisite: an `auto` parameter of an interface applied to a head
    /// variable.
    Prerequisite,
}

/// A global instance (§5.6).
#[derive(Clone)]
pub(crate) struct InstanceInfo {
    pub def: DefId,
    /// Its name, for messages.
    pub name: String,
    pub span: Span,
    pub params: Vec<InstanceParam>,
    /// Checked completely: its body, and its superclasses against the
    /// canonical ones (§5.8 (b)). Only a valid instance is used.
    pub valid: bool,
}

/// The result of one try at an interface obligation.
pub(crate) enum Attempt {
    /// Its metavariable is solved (any prerequisites are new obligations).
    Solved,
    /// It can't be settled yet: the error to report if nothing changes.
    Wait(Diagnostic),
}

/// The three results of matching a candidate's type with a goal, or of
/// comparing two candidates (§5.5).
enum Tri {
    Equal,
    Distinct,
    /// Depends on the unknown with this number.
    Blocked(usize),
}

/// A dictionary in scope: a variable, or a superclass path from one.
struct Candidate {
    term: Term,
    /// `d`, `d.eq`, `d.b.a`: for messages.
    path: String,
    interface: DataId,
    arg: Value,
}

/// An interface's relation fields and their deciders (§5.16): each field
/// `r` whose type, after its parameters, is `Prop`, with the field `decR`
/// (`r` with a capital first letter) whose type ends in `Decidable …`.
fn relation_pairs(fields: &[(Name, Term)], decidable: Option<DataId>) -> Vec<(usize, usize)> {
    fn result(mut t: &Term) -> &Term {
        loop {
            match t.strip_loc() {
                Term::Pi(_, _, _, cod) => t = cod,
                other => return other,
            }
        }
    }
    let mut out = Vec::new();
    for (r, (name, ty)) in fields.iter().enumerate() {
        if !matches!(result(ty), Term::Sort(stitchwort_core::Sort::Prop)) {
            continue;
        }
        let mut chars = name.chars();
        let Some(first) = chars.next() else { continue };
        let wanted: String = format!("dec{}{}", first.to_uppercase(), chars.as_str());
        let found = fields.iter().position(|(n, t)| {
            **n == *wanted && matches!(result(t), Term::Data(d, _) if Some(*d) == decidable)
        });
        if let Some(d) = found {
            out.push((r, d));
        }
    }
    out
}

/// `Pretty` → `pretty`, `DecEq` → `decEq`, `Shapes.Area` → `area`.
pub(crate) fn dictionary_name(interface: &str) -> String {
    let last = interface.rsplit('.').next().unwrap_or(interface);
    let mut chars = last.chars();
    match chars.next() {
        Some(c) => c.to_lowercase().chain(chars).collect(),
        None => String::new(),
    }
}

impl Elaborator {
    /// The module a declaration made now belongs to (§5.6 rule 1): `Std`
    /// for the core and the library, the namespace in a project or a file
    /// with a namespace line, and `Main` for a file without one.
    pub(crate) fn module_owner(&self) -> String {
        if self.loading_prelude {
            "Std".to_string()
        } else {
            self.module
                .namespace
                .clone()
                .unwrap_or_else(|| "Main".to_string())
        }
    }

    /// Whether `d` is an interface.
    pub(crate) fn is_interface(&self, d: DataId) -> bool {
        self.interfaces.contains_key(&d)
    }

    /// An interface's header: one parameter, a type, in `Type` (D174).
    pub(crate) fn check_interface_header(
        &self,
        decl: &Decl,
        params: &[(Name, Term)],
        sort: stitchwort_core::Sort,
    ) -> Result<()> {
        let Decl::Data { name, span, .. } = decl else {
            unreachable!()
        };
        let one_type = matches!(params, [(_, ty)] if matches!(ty.strip_loc(), Term::Sort(stitchwort_core::Sort::Type(0))));
        if !one_type || sort != stitchwort_core::Sort::Type(0) {
            return Err(error(
                "E-INTERFACE-SHAPE",
                *span,
                format!(
                    "an interface has one parameter, a type: `interface {} (a: Type) = {{ … }}`",
                    name.text
                ),
            )
            .with_note(
                "interfaces with several parameters, or over type constructors, aren't supported",
            ));
        }
        Ok(())
    }

    /// Checks field `field` of interface `d` (declared with the interfaces
    /// `group`), whose type is `ty` in the context of the parameter (level
    /// 0) and the earlier fields: a field whose type is an interface is a
    /// superclass, which must be that interface applied to the parameter,
    /// and must not be one being declared with `d` (`E-INTERFACE-CYCLE`).
    pub(crate) fn check_interface_field(
        &self,
        d: DataId,
        group: &[DataId],
        field: &ast::Name,
        ty: &Value,
    ) -> Result<()> {
        let g = &self.globals;
        let Value::Data(j, args) = force(g, ty.clone())? else {
            return Ok(());
        };
        if group.contains(&j) {
            let cycle = if j == d {
                format!("`{}` contains itself", g.data(d).name)
            } else {
                format!(
                    "`{}` contains `{}`, which contains `{}`",
                    g.data(d).name,
                    g.data(j).name,
                    g.data(d).name
                )
            };
            return Err(error(
                "E-INTERFACE-CYCLE",
                field.span,
                format!("an interface can't be its own superclass: {cycle}"),
            )
            .with_note("a field whose type is an interface is a superclass, and the superclasses can't form a cycle"));
        }
        if !self.is_interface(j) {
            return Ok(());
        }
        let on_param = matches!(args.as_slice(), [a] if matches!(force(g, a.clone())?, Value::Neutral(Head::Var(0, _), s) if s.is_empty()));
        if !on_param {
            return Err(error(
                "E-INTERFACE-SHAPE",
                field.span,
                format!(
                    "the superclass field `{}` must be `{}` applied to the interface's parameter",
                    field.text,
                    g.data(j).name
                ),
            ));
        }
        Ok(())
    }

    /// After interface `d`'s record is admitted, with its projections
    /// `projections` (registered under hidden names): its methods, and what
    /// resolution needs to know.
    pub(crate) fn after_interface(&mut self, d: DataId, projections: Vec<DefId>) -> Result<()> {
        let g = &self.globals;
        let data = g.data(d);
        let dict = dictionary_name(&data.name);
        let fields: Vec<(Name, Term)> = data.ctors[0].fields.clone();
        // Superclasses: fields whose type is an interface (on the parameter,
        // as `check_interface_field` made sure).
        let mut supers = Vec::new();
        let mut env = vec![Value::var(0)];
        for (i, (_, ty)) in fields.iter().enumerate() {
            // Earlier fields aren't needed: a superclass's type doesn't
            // mention them.
            if !(0..i).any(|j| ty.mentions(i - 1 - j))
                && let Value::Data(j, _) = force(g, stitchwort_core::value::eval(g, &env, ty)?)?
                && self.is_interface(j)
            {
                supers.push((i, j));
            }
            env.push(stitchwort_core::value::unused());
        }
        let data_key = self.data_key(d);
        let span = data.span;
        let name = data.name.clone();
        let relations = relation_pairs(&fields, g.builtins.decidable);
        let mut methods = Vec::new();
        for (i, (field, _)) in fields.iter().enumerate() {
            let proj = projections[i];
            // `Proj: [a: Type] -> (r: I a) -> T` becomes
            // `I.f: [a: Type] -> [auto i: I a] -> T`, defined as `Proj [a] i`.
            let proj_ty = self.globals.def(proj).ty.clone();
            let Term::Pi(a, _, a_ty, rest) = &proj_ty else {
                unreachable!("a projection's type")
            };
            let Term::Pi(_, _, r_ty, result) = &**rest else {
                unreachable!("a projection's type")
            };
            let (a, a_ty, r_ty, result) = (a.clone(), a_ty.clone(), r_ty.clone(), result.clone());
            let dict_name: Name = dict.as_str().into();
            let ty = Term::Pi(
                a.clone(),
                Icit::Implicit,
                a_ty,
                Rc::new(Term::Pi(dict_name.clone(), Icit::Auto, r_ty, result)),
            );
            let body = Term::Lam(
                a,
                Icit::Implicit,
                Rc::new(Term::Lam(
                    dict_name,
                    Icit::Auto,
                    Rc::new(Term::app(
                        Term::app_icit(Term::Def(proj), Term::Var(1), Icit::Implicit),
                        Term::Var(0),
                    )),
                )),
            );
            let method: Name = format!("{name}.{field}").into();
            let id = kernel::declare_def(&mut self.globals, &method, &ty, false, false, span)?;
            kernel::define_def(&mut self.globals, id, &body)?;
            // `Ord.compare` is the compiler's (crates/js).
            if self.loading_prelude {
                self.bind_builtin_def(id)?;
            }
            methods.push(id);
            let key = Self::member_key(&data_key, field);
            self.scope.insert(&key, Global::Def(id), span, false);
            self.scope.mark_member(&key);
        }
        self.interfaces.insert(
            d,
            InterfaceInfo {
                dict,
                supers,
                projections,
                methods,
                relations,
            },
        );
        Ok(())
    }

    /// Every superclass path of interface `i`, through the whole closure:
    /// each step a field index and the interface it leads to.
    fn super_paths(&self, i: DataId) -> Vec<Vec<(usize, DataId)>> {
        let mut out = Vec::new();
        let mut pending: Vec<Vec<(usize, DataId)>> = Vec::new();
        for &(f, j) in &self.interfaces[&i].supers {
            pending.push(vec![(f, j)]);
        }
        while let Some(path) = pending.pop() {
            let last = path.last().expect("not empty").1;
            for &(f, j) in &self.interfaces[&last].supers {
                let mut longer = path.clone();
                longer.push((f, j));
                pending.push(longer);
            }
            out.push(path);
        }
        out.sort_by_key(|p| p.iter().map(|(f, d)| (*f, d.0)).collect::<Vec<_>>());
        out
    }

    /// Checks the signature of instance `id` (§5.2), its owner (§5.6 rules
    /// 1, 2) and that it's the only one for its interface and head (rule
    /// 3), and registers it. It's used once it's valid
    /// ([`Elaborator::validate_instance`]).
    pub(crate) fn register_instance(&mut self, id: DefId, def_name: &ast::Name) -> Result<()> {
        let g = &self.globals;
        let def = g.def(id);
        let span = def_name.span;
        let shown_name = def_name.text.clone();
        // The parameters, as variables.
        let mut params: Vec<(Name, Icit, Value)> = Vec::new();
        let mut ty = def.ty_value.clone();
        while let Value::Pi(x, icit, dom, cod) = force(g, ty.clone())? {
            let level = params.len();
            params.push((x, icit, (*dom).clone()));
            ty = cod.apply(g, Value::var(level))?;
        }
        let names: Vec<Name> = params.iter().map(|(x, _, _)| x.clone()).collect();
        let show = |v: &Value| pretty::value_for_message_in(g, self, &names, v);
        // The result as written, for the synonym note.
        let mut written = &def.ty;
        while let Term::Pi(_, _, _, cod) = written.strip_loc() {
            written = cod;
        }
        let ty = force(g, ty)?;
        // A decision procedure (D163): marked, so the search for one uses
        // it, and none of the rules below apply (§5.12).
        if let Value::Data(d, _) = &ty
            && Some(*d)
                == g.registry
                    .data(stitchwort_core::registry::Builtin::Decidable)
        {
            kernel::mark_instance(&mut self.globals, id);
            return Ok(());
        }
        let (interface, arg) = match &ty {
            Value::Data(i, args) if self.is_interface(*i) => (*i, args[0].clone()),
            _ => {
                return Err(error(
                    "E-INSTANCE-HEAD",
                    span,
                    format!(
                        "`{shown_name}` is declared as an instance, but `{}` isn't an interface",
                        show(&ty)
                    ),
                )
                .with_note(
                    "an instance's type is an interface applied to a type, like `Pretty (List a)`, \
                     or a `Decidable …` (a decision procedure)",
                ));
            }
        };
        let iface_name = g.data(interface).name.clone();
        let goal = show(&ty);
        // A synonym written as the head, for the notes: its name.
        let synonym = match written.strip_loc() {
            Term::Data(_, written_args) => {
                written_args
                    .first()
                    .and_then(|a| match a.strip_loc().spine().0.strip_loc() {
                        Term::Def(syn) => Some(g.def(*syn).name.to_string()),
                        _ => None,
                    })
            }
            _ => None,
        };
        let head_error = || {
            let d = error(
                "E-INSTANCE-HEAD",
                span,
                format!(
                    "an instance must be for a type name applied to distinct variables, like \
                     `{iface_name} (List a)`; `{goal}` isn't"
                ),
            )
            .with_note(
                "so two instances of one interface overlap exactly when they're for the same type \
                 name; use a named alternative (a `def` of the interface's type, passed by name) \
                 for anything more specific",
            );
            match &synonym {
                Some(name) => d.with_note(format!(
                    "`{name}` is another name for a type, and the instance is for that type"
                )),
                None => d,
            }
        };
        let (head, args) = match force(g, arg)? {
            Value::Data(d, args) => (d, args),
            _ => return Err(head_error()),
        };
        let mut position: Vec<Option<usize>> = vec![None; params.len()];
        for (k, a) in args.iter().enumerate() {
            match force(g, a.clone())? {
                Value::Neutral(Head::Var(l, _), s) if s.is_empty() && position[l].is_none() => {
                    position[l] = Some(k);
                }
                _ => return Err(head_error()),
            }
        }
        let mut kinds = Vec::new();
        for (l, (x, icit, dom)) in params.iter().enumerate() {
            match (position[l], icit) {
                (Some(k), _) => kinds.push(InstanceParam::Head(k)),
                (None, Icit::Auto) => {
                    let on_head = match force(g, dom.clone())? {
                        Value::Data(j, a) if self.is_interface(j) && a.len() == 1 => matches!(
                            force(g, a[0].clone())?,
                            Value::Neutral(Head::Var(m, _), s) if s.is_empty() && position[m].is_some()
                        ),
                        _ => false,
                    };
                    if !on_head {
                        let shown_param = if **x == *ast::NAMELESS {
                            format!("[auto {}]", show(dom))
                        } else {
                            format!("[auto {x}: {}]", show(dom))
                        };
                        return Err(error(
                            "E-INSTANCE-CONTEXT",
                            span,
                            format!(
                                "`{shown_param}`: an instance may only ask for interfaces of the \
                                 variables in `{goal}`"
                            ),
                        )
                        .with_note(
                            "each thing an instance asks for must be about a smaller type than \
                             the one it's for, so finding instances always ends",
                        ));
                    }
                    kinds.push(InstanceParam::Prerequisite);
                }
                (None, _) => {
                    return Err(error(
                        "E-INSTANCE-PARAMETER",
                        span,
                        format!(
                            "`{x}` isn't fixed by `{goal}`; an instance can't have other parameters"
                        ),
                    )
                    .with_note(
                        "the compiler finds an instance by its type alone, so it couldn't choose \
                         `x`; a function that builds a dictionary from arguments can be a plain \
                         `def`, passed by name"
                            .replace("`x`", &format!("`{x}`")),
                    ));
                }
            }
        }
        // Ownership (§5.6 rules 1, 2).
        let here = self.module_owner();
        let owner_of = |d: DataId| {
            self.data_owners
                .get(&d)
                .cloned()
                .unwrap_or_else(|| "Std".to_string())
        };
        let (iface_owner, head_owner) = (owner_of(interface), owner_of(head));
        if here != iface_owner && here != head_owner {
            let head_name = g.data(head).name.clone();
            let mut d = error(
                "E-INSTANCE-ORPHAN",
                span,
                format!(
                    "`{goal}` must be declared in `{iface_owner}` (which owns `{iface_name}`) or \
                     `{head_owner}` (which owns `{head_name}`)"
                ),
            )
            .with_note(format!(
                "this is `{here}`; a named alternative (a `def` of type `{goal}`) can be declared \
                 here and passed by name"
            ));
            // A synonym owns nothing: say what it stands for.
            if let Some(name) = &synonym {
                d = d.with_note(format!(
                    "`{name}` is another name for `{head_name}`, which `{head_owner}` owns"
                ));
            }
            return Err(d);
        }
        // Overlap (§5.6 rule 3).
        if let Some(first) = self.instances.get(&(interface, head)) {
            let head_name = g.data(head).name.clone();
            return Err(error(
                "E-INSTANCE-OVERLAP",
                span,
                format!(
                    "`{iface_name} {head_name}` already has an instance, `{}`",
                    first.name
                ),
            )
            .with_label(first.span, "the first instance is here")
            .with_note(
                "there's at most one instance of an interface for each type; declare another \
                 ordering, say, as a named alternative (a `def`), passed by name",
            ));
        }
        kernel::mark_instance(&mut self.globals, id);
        self.instances.insert(
            (interface, head),
            InstanceInfo {
                def: id,
                name: shown_name,
                span,
                params: kinds,
                valid: false,
            },
        );
        Ok(())
    }

    /// Once instance `id` is admitted: each superclass path of it must be
    /// the instance resolution finds for that parent, in the instance's own
    /// context (its prerequisites in scope, and nothing else), by
    /// computation (§5.8 (b)). It's never changed. Then it's valid.
    pub(crate) fn validate_instance(&mut self, id: DefId) -> Result<()> {
        let Some((&(interface, head), _)) = self.instances.iter().find(|(_, i)| i.def == id) else {
            return Ok(());
        };
        let paths = self.super_paths(interface);
        if !paths.is_empty() {
            self.check_supers(id, interface, &paths)?;
        }
        if let Some(info) = self.instances.get_mut(&(interface, head)) {
            info.valid = true;
        }
        Ok(())
    }

    fn check_supers(
        &self,
        id: DefId,
        interface: DataId,
        paths: &[Vec<(usize, DataId)>],
    ) -> Result<()> {
        let g = &self.globals;
        let def = g.def(id);
        let span = def.span;
        let inst_name = def.name.to_string();
        let mut env = Vec::new();
        let mut types = Vec::new();
        let mut names = Vec::new();
        let mut icits = Vec::new();
        let mut ty = def.ty_value.clone();
        while let Value::Pi(x, icit, dom, cod) = force(g, ty.clone())? {
            let level = env.len();
            env.push(Value::var(level));
            types.push((*dom).clone());
            names.push(x);
            icits.push(icit);
            ty = cod.apply(g, Value::var(level))?;
        }
        let level = env.len();
        let inst = icits
            .iter()
            .enumerate()
            .fold(Term::Def(id), |t, (l, icit)| {
                Term::app_icit(t, Term::Var(level - 1 - l), *icit)
            });
        let arg = match force(g, ty)? {
            Value::Data(_, args) => args[0].clone(),
            _ => unreachable!("an instance's type is an interface"),
        };
        for path in paths {
            self.clear_metas();
            let mut cx = Ctx::from_parts(self, env.clone(), types.clone(), names.clone(), span);
            // `N.p`, by the record's own projections.
            let mut term = inst.clone();
            let mut at = interface;
            let mut shown = Vec::new();
            for &(field, parent) in path {
                let proj = self.interfaces[&at].projections[field];
                let arg_term = cx.quote(&arg)?;
                term = Term::app(
                    Term::app_icit(Term::Def(proj), arg_term, Icit::Implicit),
                    term,
                );
                shown.push(g.data(at).ctors[0].fields[field].0.to_string());
                at = parent;
            }
            let goal = Value::Data(at, vec![arg.clone()]);
            let shown_goal = cx.show(&goal);
            let shown_path = shown.join(".");
            let meta = implicit_arg(&mut cx, Icit::Auto, &goal);
            let found = match self.solve_obligations() {
                Ok(()) => self.zonk(&meta, level)?,
                Err(e) if crate::undo::fatal(&e) => return Err(e),
                Err(e) => {
                    let mut d = Diagnostic::error(
                        "E-INSTANCE-SUPER",
                        format!(
                            "the `{shown_goal}` inside `{inst_name}` (its `{shown_path}`) must be \
                             the instance the compiler finds for `{shown_goal}`, but it can't \
                             find one"
                        ),
                    )
                    .with_label(span, "this instance");
                    d = d.with_note(e.message);
                    return Err(d);
                }
            };
            let (have, want) = (cx.eval(&term)?, cx.eval(&found)?);
            if !conv(g, level, &have, &want)? {
                // The instance found, by name if it's a global one (its
                // value would show as its body).
                let global = match force(g, arg.clone())? {
                    Value::Data(h, _) => self.instances.get(&(at, h)).map(|i| i.name.clone()),
                    _ => None,
                };
                let shown_found = global.unwrap_or_else(|| pretty::term(g, &names, &found));
                return Err(Diagnostic::error(
                    "E-INSTANCE-SUPER",
                    format!(
                        "the `{shown_goal}` inside `{inst_name}` (its `{shown_path}`) isn't \
                         `{shown_found}`"
                    ),
                )
                .with_label(span, "this instance")
                .with_note(format!(
                    "a global instance's superclasses must be the instances the compiler finds \
                     for them, so that every way of reaching a `{shown_goal}` agrees: leave \
                     `{}` out to have it filled in, or give `{shown_found}`",
                    shown[0]
                )));
            }
        }
        self.clear_metas();
        Ok(())
    }

    /// `E-INSTANCE-REDUNDANT`: a signature `ty` (a closed term) that asks for
    /// an interface and, on the same type, one of its superclasses (§5.8
    /// (c)).
    pub(crate) fn check_redundant(&self, ty: &Term, span: Span) -> Result<()> {
        // Only a signature asking for two interfaces or more can be
        // redundant: counted on the term, so an ordinary signature isn't
        // evaluated (its types may mention a definition that's expensive to
        // compute, which evaluating would).
        let mut asking = 0;
        let mut rest = ty;
        while let Term::Pi(_, icit, dom, cod) = rest.strip_loc() {
            if *icit == Icit::Auto
                && let Term::Data(i, _) = dom.strip_loc().spine().0.strip_loc()
                && self.is_interface(*i)
            {
                asking += 1;
            }
            rest = cod;
        }
        if asking < 2 {
            return Ok(());
        }
        let g = &self.globals;
        let mut asked: Vec<(Name, DataId, Value)> = Vec::new();
        let mut value = stitchwort_core::value::eval(g, &[], ty)?;
        let mut level = 0;
        let mut names = Vec::new();
        while let Value::Pi(x, icit, dom, cod) = force(g, value.clone())? {
            if icit == Icit::Auto
                && let Value::Data(i, args) = force(g, (*dom).clone())?
                && self.is_interface(i)
            {
                asked.push((x.clone(), i, args[0].clone()));
            }
            names.push(x);
            value = cod.apply(g, Value::var(level))?;
            level += 1;
        }
        for (x, i, a) in &asked {
            for path in self.super_paths(*i) {
                let parent = path.last().expect("not empty").1;
                for (y, j, b) in &asked {
                    if *j == parent && conv(g, level, a, b)? {
                        let shown = |d: DataId, v: &Value| {
                            format!(
                                "{} {}",
                                g.data(d).name,
                                pretty::value_for_message_in(g, self, &names, v)
                            )
                        };
                        let param = |n: &Name, d: DataId, v: &Value| {
                            if **n == *ast::NAMELESS {
                                format!("[auto {}]", shown(d, v))
                            } else {
                                format!("[auto {n}: {}]", shown(d, v))
                            }
                        };
                        return Err(error(
                            "E-INSTANCE-REDUNDANT",
                            span,
                            format!(
                                "`{}` already contains a `{}`; remove `{}`",
                                shown(*i, a),
                                shown(*j, b),
                                param(y, *j, b)
                            ),
                        )
                        .with_note(format!(
                            "asking for both would give two `{}` dictionaries, which needn't \
                             agree; use the one inside `{}`",
                            shown(*j, b),
                            param(x, *i, a)
                        )));
                    }
                }
            }
        }
        Ok(())
    }
}

impl Elaborator {
    /// Whether a definition of type `ty` is a dictionary, which stays folded
    /// by name until it's taken apart (`Def::fold`): its result, after its
    /// parameters, is an interface.
    /// Read from the type as written, so nothing in it is computed unless
    /// the result is a definition's application (a synonym, perhaps): `cost
    /// = cost` isn't evaluated.
    pub(crate) fn is_dictionary_type(&self, ty: &Term) -> Result<bool> {
        if self.interfaces.is_empty() {
            return Ok(false);
        }
        let g = &self.globals;
        let mut result = ty.strip_loc();
        let mut level = 0;
        while let Term::Pi(_, _, _, cod) = result {
            result = cod.strip_loc();
            level += 1;
        }
        Ok(match result.spine().0.strip_loc() {
            Term::Data(i, _) => self.is_interface(*i),
            Term::Def(_) => {
                let env: Vec<Value> = (0..level).map(Value::var).collect();
                matches!(
                    force(g, stitchwort_core::value::eval(g, &env, result)?)?,
                    Value::Data(i, _) if self.is_interface(i)
                )
            }
            _ => false,
        })
    }
}

/// Whether `goal` is an interface applied to a type: the interface and the
/// type.
pub(crate) fn interface_goal(e: &Elaborator, goal: &Value) -> Result<Option<(DataId, Value)>> {
    if e.interfaces.is_empty() {
        return Ok(None);
    }
    Ok(match force(&e.globals, goal.clone())? {
        Value::Data(i, args) if e.is_interface(i) && args.len() == 1 => Some((i, args[0].clone())),
        _ => None,
    })
}

/// Spends one step of obligation tree `tree`'s budget.
fn step(cx: &Ctx, tree: usize, goal: &Value) -> Result<()> {
    let budget = cx.e.instance_budget.unwrap_or(BUDGET);
    let mut steps = cx.e.instance_steps.borrow_mut();
    let used = steps.entry(tree).or_insert(0);
    *used += 1;
    if *used > budget {
        return Err(cx
            .error(
                "E-INSTANCE-BUDGET",
                format!(
                    "stopped looking for `{}` after {budget} steps; this is a limit, not a \
                     missing instance",
                    cx.show(goal)
                ),
                "while finding the instance for this",
            )
            .with_note("pass the dictionary by name to skip the search"));
    }
    Ok(())
}

/// One try at the interface obligation `ob`, whose goal is `interface`
/// applied to `arg` (§5.5), in its context `cx`.
pub(crate) fn attempt(
    cx: &mut Ctx,
    ob: &Obligation,
    interface: DataId,
    arg: &Value,
) -> Result<Attempt> {
    let g = cx.g();
    let placeholder = cx.eval(&ob.meta)?;
    // 1. Already solved, by unification.
    if !matches!(
        force(g, placeholder.clone())?,
        Value::Neutral(Head::Meta(_), _)
    ) {
        return Ok(Attempt::Solved);
    }
    let arg = &refresh(cx, arg)?;
    let goal = Value::Data(interface, vec![arg.clone()]);
    let iface_name = g.data(interface).name.to_string();
    let dict = cx.e.interfaces[&interface].dict.clone();
    step(cx, ob.tree, &goal)?;
    // 3. Wait while the type's head is unknown.
    let target = force(g, arg.clone())?;
    if let Value::Neutral(Head::Meta(_), _) = target {
        return Ok(Attempt::Wait(
            cx.error(
                "E-INSTANCE-UNKNOWN-TYPE",
                format!("can't tell which type's `{iface_name}` to use here"),
                format!("this needs `{}`", cx.show(&goal)),
            )
            .with_note("annotate, so the type is known: e.g. `(xs: List Nat)`"),
        ));
    }
    // 4. Dictionaries in scope.
    let candidates = locals(cx)?;
    let mut matched: Vec<Candidate> = Vec::new();
    for c in candidates {
        if c.interface != interface {
            continue;
        }
        step(cx, ob.tree, &goal)?;
        match tri(cx, &c.arg, arg)? {
            Tri::Equal => matched.push(c),
            Tri::Distinct => {}
            Tri::Blocked(m) => {
                return Ok(Attempt::Wait(stuck(
                    cx,
                    &goal,
                    m,
                    &format!("whether `{}` gives `{}`", c.path, cx.show(&goal)),
                )));
            }
        }
    }
    // Merge the candidates that are the same dictionary.
    let mut distinct: Vec<(Candidate, Value)> = Vec::new();
    'next: for c in matched {
        let value = cx.eval(&c.term)?;
        for (d, other) in &distinct {
            match tri(cx, &value, other)? {
                Tri::Equal => continue 'next,
                Tri::Distinct => {}
                Tri::Blocked(m) => {
                    return Ok(Attempt::Wait(stuck(
                        cx,
                        &goal,
                        m,
                        &format!(
                            "whether `{}` and `{}` are the same dictionary",
                            d.path, c.path
                        ),
                    )));
                }
            }
        }
        distinct.push((c, value));
    }
    match distinct.len() {
        0 => {}
        1 => {
            let (_, value) = distinct.pop().expect("one");
            return solve(cx, &placeholder, &value);
        }
        _ => {
            let mut paths: Vec<String> = distinct.iter().map(|(c, _)| c.path.clone()).collect();
            paths.sort();
            let listed = listed(&paths);
            return Err(cx
                .error(
                    "E-INSTANCE-AMBIGUOUS",
                    format!(
                        "{} different `{}` dictionaries are in scope: {listed}",
                        if paths.len() == 2 { "two" } else { "several" },
                        cx.show(&goal)
                    ),
                    format!("this needs `{}`", cx.show(&goal)),
                )
                .with_note(format!(
                    "nothing says they're the same, so the compiler won't choose: pass one by \
                     name, as in `[{dict} := {}]`",
                    paths[0]
                )));
        }
    }
    // 5. The global instance for the head.
    let (head, args) = match &target {
        Value::Data(d, args) => (*d, args.clone()),
        Value::Neutral(Head::Def(_), _) => {
            if let Some(m) = unsolved_in(cx, &target)? {
                return Ok(Attempt::Wait(stuck(
                    cx,
                    &goal,
                    m,
                    &format!("which type `{}` is", cx.show(&target)),
                )));
            }
            return Err(none(cx, interface, &goal, None));
        }
        _ => return Err(none(cx, interface, &goal, None)),
    };
    let Some(info) = cx.e.instances.get(&(interface, head)) else {
        return Err(none(cx, interface, &goal, Some(head)));
    };
    if !info.valid {
        let name = info.name.clone();
        let failed = g.def(info.def).state() == stitchwort_core::globals::State::Failed;
        let reason = if failed || cx.e.globals.def(info.def).body().is_some() {
            format!("`{name}` has errors")
        } else {
            format!(
                "`{name}` isn't finished here: it can't be used inside its own definition, or one it depends on"
            )
        };
        return Err(cx
            .error(
                "E-INSTANCE-NONE",
                format!(
                    "can't use the instance `{name}` for `{}` here",
                    cx.show(&goal)
                ),
                format!("this needs `{}`", cx.show(&goal)),
            )
            .with_note(reason));
    }
    let (def, params) = (info.def, info.params.clone());
    // An argument of the head that's a dictionary, equated with an unknown,
    // isn't a solution: wait for the unknown's own obligation (§5.5 step 5).
    let data = g.data(head);
    let binders = data.params.iter().chain(&data.indices);
    for ((_, ty), value) in binders.zip(&args) {
        if let Term::Data(j, _) = ty.strip_loc()
            && cx.e.is_interface(*j)
            && let Value::Neutral(Head::Meta(m), _) = force(g, value.clone())?
        {
            return Ok(Attempt::Wait(stuck(
                cx,
                &goal,
                m,
                &format!(
                    "the dictionary that `{}` gives `{}`",
                    cx.show(&target),
                    g.def(def).name
                ),
            )));
        }
    }
    // Commit: the instance, applied to the head's arguments and a new
    // obligation for each prerequisite.
    let mut term = Term::Def(def);
    let mut ty = g.def(def).ty_value.clone();
    for p in &params {
        let Value::Pi(_, icit, dom, cod) = force(g, ty.clone())? else {
            unreachable!("an instance's parameters")
        };
        let (arg_term, value) = match p {
            InstanceParam::Head(k) => (cx.quote(&args[*k])?, args[*k].clone()),
            InstanceParam::Prerequisite => {
                let meta = implicit_arg(cx, Icit::Auto, &dom);
                if let Some(last) = cx.e.obligations.borrow_mut().last_mut() {
                    last.tree = ob.tree;
                }
                let value = cx.eval(&meta)?;
                (meta, value)
            }
        };
        term = Term::app_icit(term, arg_term, icit);
        ty = cod.apply(g, value)?;
    }
    let value = cx.eval(&term)?;
    solve(cx, &placeholder, &value)
}

fn solve(cx: &mut Ctx, placeholder: &Value, value: &Value) -> Result<Attempt> {
    if !cx.unify(placeholder, value)? {
        return Err(cx.error(
            "E-INTERNAL",
            "internal error: a found instance doesn't fit",
            "here",
        ));
    }
    Ok(Attempt::Solved)
}

/// "`a`, `b` and `c`".
fn listed(items: &[String]) -> String {
    let quoted: Vec<String> = items.iter().map(|i| format!("`{i}`")).collect();
    match quoted.split_last() {
        Some((last, rest)) if !rest.is_empty() => format!("{} and {last}", rest.join(", ")),
        _ => quoted.join(""),
    }
}

/// The error for an obligation still blocked on unknown `m` when nothing
/// more can be solved: `E-INSTANCE-STUCK`.
fn stuck(cx: &Ctx, goal: &Value, m: usize, what: &str) -> Diagnostic {
    let shown_meta = cx.show(&Value::Neutral(
        Head::Meta(m),
        stitchwort_core::value::Spine::new(),
    ));
    let mut d = cx.error(
        "E-INSTANCE-STUCK",
        format!("can't tell {what} until `{shown_meta}` is known"),
        format!("this needs `{}`", cx.show(goal)),
    );
    let span = cx.g().metas.borrow()[m].span;
    if span != cx.span {
        d = d.with_label(span, format!("`{shown_meta}` is what goes here"));
    }
    d.with_note("pass the dictionary by name, or annotate")
}

/// `E-INSTANCE-NONE`, with what might help.
fn none(cx: &Ctx, interface: DataId, goal: &Value, head: Option<DataId>) -> Diagnostic {
    let g = cx.g();
    let e = cx.e;
    let iface_name = g.data(interface).name.to_string();
    let dict = e.interfaces[&interface].dict.clone();
    let arg = match goal {
        Value::Data(_, args) => args[0].clone(),
        _ => unreachable!(),
    };
    let mut d = cx.error(
        "E-INSTANCE-NONE",
        format!("no `{iface_name}` instance for `{}`", cx.show(&arg)),
        format!("this needs `{}`", cx.show(goal)),
    );
    // For equality: why `==` wasn't derived, or why it can't be.
    if Some(interface) == dec_eq(e) {
        match force(g, arg.clone()).unwrap_or(arg.clone()) {
            Value::Data(t, _) => {
                if let Some(why) = e.no_eq.get(&t) {
                    d = d.with_note(format!(
                        "`==` isn't derived for `{}`: {why}",
                        g.data(t).name
                    ));
                }
            }
            Value::Pi(..) => {
                d = d.with_note("functions can't be compared: there's no `==` on them");
            }
            other if crate::quot::is_quotient_type(&other) => {
                d = d.with_note(crate::quot::NO_DERIVED_EQ);
            }
            _ => {}
        }
    }
    // For `Show`: why it wasn't derived.
    if Some(interface) == show(e) {
        match force(g, arg.clone()).unwrap_or(arg.clone()) {
            Value::Data(t, _) => {
                if let Some(why) = e.no_show.get(&t) {
                    d = d.with_note(format!(
                        "`Show` isn't derived for `{}`: {why}",
                        g.data(t).name
                    ));
                }
            }
            Value::Pi(..) => {
                d = d.with_note("functions can't be shown");
            }
            _ => {}
        }
    }
    // For `Ord`: why it wasn't derived.
    if Some(interface) == ord(e) {
        match force(g, arg.clone()).unwrap_or(arg.clone()) {
            Value::Data(t, _) => {
                if let Some(why) = e.no_ord.get(&t) {
                    d = d.with_note(format!(
                        "`Ord` isn't derived for `{}`: {why}",
                        g.data(t).name
                    ));
                }
            }
            Value::Pi(..) => {
                d = d.with_note("functions can't be ordered");
            }
            _ => {}
        }
    }
    match head {
        Some(h) => {
            let owner = |d: DataId| {
                e.data_owners
                    .get(&d)
                    .cloned()
                    .unwrap_or_else(|| "Std".to_string())
            };
            let (io, ho) = (owner(interface), owner(h));
            // A program can't add to `Std`, so only the other owner is any
            // use to it.
            let user = !e.loading_prelude;
            let where_ = if io == ho || (user && io == "Std") {
                format!("in `{ho}`")
            } else if user && ho == "Std" {
                format!("in `{io}`")
            } else {
                format!(
                    "in `{io}` (which owns `{iface_name}`) or `{ho}` (which owns `{}`)",
                    g.data(h).name
                )
            };
            if !(user && io == "Std" && ho == "Std") {
                d = d.with_note(format!(
                    "an instance of `{iface_name}` for `{}` can be declared {where_}",
                    g.data(h).name
                ));
            }
        }
        None => {
            if let Value::Neutral(Head::Var(_, _), _) = force(g, arg.clone()).unwrap_or(arg.clone())
            {
                d = d.with_note(format!(
                    "`{}` is a type variable: ask for its instance with `[auto {dict}: {}]`",
                    cx.show(&arg),
                    cx.show(goal)
                ));
            }
        }
    }
    // Instances of this module that aren't checked where this is.
    for name in e.unchecked_instances(interface) {
        d = d.with_note(format!(
            "`{name}` is an instance in this module, but it's checked after this, since it \
             depends on it: move what it needs out of this declaration, or pass it by name"
        ));
    }
    // Named alternatives of the right type.
    let mut hints = 0;
    for (k, def) in g.defs.iter().enumerate() {
        if hints == 3 {
            break;
        }
        if def.body().is_none() || def.instance {
            continue;
        }
        if let Value::Data(i, args) = &def.ty_value
            && *i == interface
            && conv(g, cx.level(), &args[0], &arg).unwrap_or(false)
            && !e.helper_keys.contains(&def.name.to_string())
        {
            let _ = k;
            d = d.with_note(format!(
                "`{}` has type `{}`: pass it with `[{dict} := {}]`",
                def.name,
                cx.show(goal),
                def.name
            ));
            hints += 1;
        }
    }
    d
}

/// Every dictionary in scope (§5.5 step 4): each variable whose type is an
/// interface, and every superclass path from one.
fn locals(cx: &Ctx) -> Result<Vec<Candidate>> {
    let g = cx.g();
    let mut out = Vec::new();
    for level in (0..cx.level()).rev() {
        let Value::Data(i, args) = force(g, cx.types[level].clone())? else {
            continue;
        };
        if !cx.e.is_interface(i) {
            continue;
        }
        let mut pending = vec![Candidate {
            term: Term::Var(cx.level() - 1 - level),
            path: cx.names[level].to_string(),
            interface: i,
            arg: args[0].clone(),
        }];
        while let Some(c) = pending.pop() {
            let info = &cx.e.interfaces[&c.interface];
            for &(field, parent) in &info.supers {
                let proj = info.projections[field];
                let arg_term = cx.quote(&c.arg)?;
                let field_name = &g.data(c.interface).ctors[0].fields[field].0;
                pending.push(Candidate {
                    term: Term::app(
                        Term::app_icit(Term::Def(proj), arg_term, Icit::Implicit),
                        c.term.clone(),
                    ),
                    path: format!("{}.{field_name}", c.path),
                    interface: parent,
                    arg: c.arg.clone(),
                });
            }
            out.push(c);
        }
    }
    Ok(out)
}

/// Compares `a` and `b` without assigning any unknown that exists now
/// (§5.5): equal, rigidly distinct, or blocked on an unknown.
fn tri(cx: &mut Ctx, a: &Value, b: &Value) -> Result<Tri> {
    // A computation that was stuck on an unknown solved since is run again.
    let (a, b) = (&refresh(cx, a)?, &refresh(cx, b)?);
    let snapshot = crate::undo::Snapshot::take(cx);
    let before = cx.g().metas.borrow().len();
    let unified = cx.unify(a, b);
    let solved = snapshot.solved_since(cx);
    snapshot.restore(cx);
    let unified = unified?;
    if unified {
        return Ok(match solved.into_iter().find(|m| *m < before) {
            Some(m) => Tri::Blocked(m),
            None => Tri::Equal,
        });
    }
    if rigidly_distinct(cx, a, b)? {
        return Ok(Tri::Distinct);
    }
    if let Some(m) = unsolved_in(cx, a)? {
        return Ok(Tri::Blocked(m));
    }
    if let Some(m) = unsolved_in(cx, b)? {
        return Ok(Tri::Blocked(m));
    }
    Ok(Tri::Distinct)
}

/// Whether `a` and `b` differ in a way no solution of the unknowns could
/// change: different type or constructor names, numbers, sorts or rigid
/// variables, or different rigid heads (`unify::rigid_head`, which the row
/// rule uses too), here or in arguments of the same name.
fn rigidly_distinct(cx: &Ctx, a: &Value, b: &Value) -> Result<bool> {
    let g = cx.g();
    let mut pending = vec![(a.clone(), b.clone())];
    while let Some((a, b)) = pending.pop() {
        let (a, b) = (force(g, a)?, force(g, b)?);
        let a = unfold_folded(g, &a)?.unwrap_or(a);
        let b = unfold_folded(g, &b)?.unwrap_or(b);
        match (&a, &b) {
            (Value::Data(d1, a1), Value::Data(d2, a2)) => {
                if d1 != d2 || a1.len() != a2.len() {
                    return Ok(true);
                }
                pending.extend(a1.iter().cloned().zip(a2.iter().cloned()));
            }
            (Value::Ctor(d1, c1, f1), Value::Ctor(d2, c2, f2)) => {
                if d1 != d2 || c1 != c2 || f1.len() != f2.len() {
                    return Ok(true);
                }
                pending.extend(f1.iter().cloned().zip(f2.iter().cloned()));
            }
            (Value::Nat(m), Value::Nat(n)) if m != n => return Ok(true),
            (Value::Sort(s), Value::Sort(t)) if s != t => return Ok(true),
            (Value::Neutral(Head::Var(x, _), s), Value::Neutral(Head::Var(y, _), t))
                if s.is_empty() && t.is_empty() && x != y =>
            {
                return Ok(true);
            }
            // Different rigid heads, as the row rule classifies them
            // (`unify::rigid_head`); two data types were compared above.
            _ => {
                if let (Some(k), Some(l)) = (rigid_head(g, &a), rigid_head(g, &b))
                    && k != l
                {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

/// `v` read back for the scans and recomputation below: its normal form,
/// unless that has more than [`SCAN_LIMIT`] nodes (a call whose unfolding
/// computes a large structure). Then calls are read back as calls, which is
/// the same value and still shows the unknowns among their arguments.
fn scanned(cx: &Ctx, v: &Value) -> Result<Term> {
    match quote_at_most(cx.g(), cx.level(), v, SCAN_LIMIT)? {
        Some(term) => Ok(term),
        None => cx.quote_folded(v),
    }
}

/// `v` with the solutions of its unknowns substituted, computed again: a
/// definition left folded because it was stuck on an unknown that's solved
/// now takes its step.
pub(crate) fn refresh(cx: &Ctx, v: &Value) -> Result<Value> {
    let term = scanned(cx, v)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    cx.eval(&term)
}

/// An unknown that `v` mentions and that nothing has solved, if any.
pub(crate) fn unsolved_in(cx: &Ctx, v: &Value) -> Result<Option<usize>> {
    let term = scanned(cx, v)?;
    let term = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    Ok(term.subterms().find_map(|(t, _)| match t {
        Term::Meta(m) if cx.g().meta_solution(*m).is_none() => Some(*m),
        _ => None,
    }))
}

impl Elaborator {
    /// The instances declared in the module being elaborated, of interface
    /// `interface`, that aren't checked yet: their names.
    fn unchecked_instances(&self, interface: DataId) -> Vec<String> {
        let mut out = Vec::new();
        for (i, item) in self.module.items.iter().enumerate() {
            if !item.instance || item.status != crate::module::Status::Waiting {
                continue;
            }
            if self.module.in_current(i) {
                continue;
            }
            if item.interface == Some(Global::Data(interface)) {
                out.push(item.name.clone());
            }
        }
        out
    }

    /// Tries to solve the obligation for metavariable `meta` (just made, for
    /// an omitted superclass field) now, with any prerequisites it makes:
    /// whatever can't be solved yet is left for the end of the declaration
    /// (§5.8 (a)).
    pub(crate) fn solve_now(&self, meta: &Term) -> Result<()> {
        self.solve_tree(meta, false)
    }

    /// [`Elaborator::solve_now`], but an obligation of the tree that fails
    /// (no instance, an ambiguity) is an error now; only waiting leaves it
    /// for later.
    pub(crate) fn solve_tree(&self, meta: &Term, strict: bool) -> Result<()> {
        let Term::Meta(root) = meta.spine().0 else {
            return Ok(());
        };
        let root = *root;
        let tree = {
            let obligations = self.obligations.borrow();
            match obligations
                .iter()
                .find(|ob| matches!(ob.meta.spine().0, Term::Meta(m) if *m == root))
            {
                Some(ob) => ob.tree,
                None => return Ok(()),
            }
        };
        // Obligations stay in the list, solved or not (a solved one is
        // skipped later): `undo.rs` restores the list by its length, so
        // removing one made before a transaction that's then undone would
        // lose it.
        let mut tried = stitchwort_core::collections::HashSet::default();
        loop {
            // The next obligation of this tree not tried yet.
            let ob = self
                .obligations
                .borrow()
                .iter()
                .find(|ob| {
                    ob.tree == tree
                        && !matches!(ob.meta.spine().0, Term::Meta(m) if tried.contains(m))
                })
                .cloned();
            let Some(ob) = ob else { break };
            if let Term::Meta(m) = ob.meta.spine().0 {
                tried.insert(*m);
            }
            let mut ob_cx = Ctx::from_parts(
                self,
                ob.env.clone(),
                ob.types.clone(),
                ob.names.clone(),
                ob.span,
            );
            let goal = interface_goal(self, &ob.goal)?;
            let mut failed = None;
            if let Some((i, arg)) = goal {
                crate::undo::transaction(&mut ob_cx, |cx| match attempt(cx, &ob, i, &arg) {
                    Ok(Attempt::Solved) => Ok(Some(())),
                    Ok(Attempt::Wait(_)) => Ok(None),
                    Err(e) if crate::undo::fatal(&e) => Err(e),
                    Err(e) => {
                        failed = Some(e);
                        Ok(None)
                    }
                })?;
            }
            if strict && let Some(e) = failed {
                return Err(e);
            }
        }
        Ok(())
    }
}

/// The library's `DecEq`, once it's declared (docs/proposals/interfaces.md
/// §6.1).
pub(crate) fn dec_eq(e: &Elaborator) -> Option<DataId> {
    match e.scope.get("Std.DecEq") {
        Some((Global::Data(d), _)) if e.is_interface(d) => Some(d),
        _ => None,
    }
}

/// The library's `Show`, once it's declared (§5.14).
pub(crate) fn show(e: &Elaborator) -> Option<DataId> {
    match e.scope.get("Std.Show") {
        Some((Global::Data(d), _)) if e.is_interface(d) => Some(d),
        _ => None,
    }
}

/// The library's `Ord`, once it's declared (§6.2).
pub(crate) fn ord(e: &Elaborator) -> Option<DataId> {
    match e.scope.get("Std.Ord") {
        Some((Global::Data(d), _)) if e.is_interface(d) => Some(d),
        _ => None,
    }
}

/// A decision of `x = y`, for `x y: ty`, from the `DecEq` instance for `ty`
/// (§5.12). It's found now if it can be; an error if there's none. If the
/// instance found is a global instance whose body is a record literal
/// (unfolded from its name, `Def::fold`), the
/// decision is its `decide` field applied to `x` and `y`, which is the term a
/// search for a decision procedure used to give (`Nat.decEq x y`); otherwise
/// it's `DecEq.decide x y` with that dictionary, found later if it can't be
/// yet.
pub(crate) fn decide_eq(cx: &mut Ctx, ty: &Value, x: &Value, y: &Value) -> Result<Term> {
    let (xt, yt) = (cx.quote(x)?, cx.quote(y)?);
    decide_eq_of(cx, ty, xt, yt)
}

/// [`decide_eq`] for operands given as terms, as written: reading them back
/// from their values would write out what a `let`-bound variable stands for
/// (SW-345).
pub(crate) fn decide_eq_of(cx: &mut Ctx, ty: &Value, xt: Term, yt: Term) -> Result<Term> {
    let Some(dec) = dec_eq(cx.e) else {
        return Err(cx.error(
            "E-AUTO-NONE",
            "no way to decide an equation here",
            "the library's `DecEq` isn't available yet",
        ));
    };
    let goal = Value::Data(dec, vec![ty.clone()]);
    let meta = implicit_arg(cx, Icit::Auto, &goal);
    cx.e.solve_tree(&meta, true)?;
    // A definition, applied or not (not a lambda, whose type the kernel
    // can't infer where it's applied).
    let dict = force(cx.g(), cx.eval(&meta)?)?;
    if let Value::Ctor(_, 0, fields) = unfold_folded(cx.g(), &dict)?.unwrap_or(dict)
        && let Some(decide) = fields.first()
        && matches!(decide, Value::Neutral(Head::Def(_), _))
    {
        let decide = cx.quote(decide)?;
        return Ok(Term::app(Term::app(decide, xt), yt));
    }
    let Some((Global::Def(method), _)) = cx.e.scope.get("Std.DecEq.decide") else {
        unreachable!("`DecEq` has its method")
    };
    note_operator_dictionary(cx, &meta, method, 0);
    let ty = cx.quote(ty)?;
    let call = Term::app_icit(
        Term::app_icit(Term::Def(method), ty, Icit::Implicit),
        meta,
        Icit::Auto,
    );
    Ok(Term::app(Term::app(call, xt), yt))
}

/// Whether an instance of `goal` (an interface applied to a type) can be
/// found in `cx` now: `Ok(None)` if so (or if it has to wait), the error if
/// not. What it found is undone.
pub(crate) fn findable(cx: &mut Ctx, goal: &Value) -> Result<Option<Diagnostic>> {
    let mut why = None;
    crate::undo::transaction(cx, |cx| {
        let meta = implicit_arg(cx, Icit::Auto, goal);
        match cx.e.solve_tree(&meta, true) {
            Ok(()) => {}
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => why = Some(e),
        }
        Ok(None::<()>)
    })?;
    Ok(why)
}

impl Elaborator {
    /// Finds now the instances still to be found whose type has no unknowns
    /// left, so the answer can't depend on when they're found: for a
    /// comparison that failed, perhaps on one of their metavariables
    /// (`check::compare`). Whether any was found.
    pub(crate) fn solve_ready_instances(&self) -> Result<bool> {
        self.solve_ready_instances_keeping(&[], None)
    }

    /// [`Elaborator::solve_ready_instances`], except for the obligations of
    /// the metavariables `keep`: those unification may still solve (§5.5
    /// step 1), so finding them now could choose differently. With `only`,
    /// just those of these metavariables.
    pub(crate) fn solve_ready_instances_keeping(
        &self,
        keep: &[usize],
        only: Option<&[usize]>,
    ) -> Result<bool> {
        if self.interfaces.is_empty() {
            return Ok(false);
        }
        let mut ready = Vec::new();
        {
            let obligations = self.obligations.borrow();
            for ob in obligations.iter() {
                let Term::Meta(m) = ob.meta.spine().0 else {
                    continue;
                };
                if keep.contains(m) || only.is_some_and(|only| !only.contains(m)) {
                    continue;
                }
                let Some((_, arg)) = interface_goal(self, &ob.goal)? else {
                    continue;
                };
                let cx = Ctx::from_parts(
                    self,
                    ob.env.clone(),
                    ob.types.clone(),
                    ob.names.clone(),
                    ob.span,
                );
                // Solved by unification, unless only pruned: then its
                // solution is a new unknown, still to be found here.
                if !unsolved_placeholder(&cx, &ob.meta)? {
                    continue;
                }
                if unsolved_in(&cx, &arg)?.is_none() {
                    ready.push(ob.clone());
                }
            }
        }
        let mut found = false;
        for ob in ready {
            self.solve_now(&ob.meta)?;
            let cx = Ctx::from_parts(self, ob.env, ob.types, ob.names, ob.span);
            found |= !unsolved_placeholder(&cx, &ob.meta)?;
        }
        Ok(found)
    }
}

/// Whether the dictionary `meta` stands for is still unknown: an unsolved
/// metavariable, or one solved only by pruning to another unsolved one.
fn unsolved_placeholder(cx: &Ctx, meta: &Term) -> Result<bool> {
    Ok(matches!(
        force(cx.g(), cx.eval(meta)?)?,
        Value::Neutral(Head::Meta(_), _)
    ))
}

/// Whether `v` has a projection that was stuck on a dictionary found since:
/// read back, an interface's projection applied to a record literal or a
/// dictionary's name (`Add.%add {…} x y`, `Add.%add Nat.instAdd x y`), which
/// [`refresh`] computes.
pub(crate) fn stuck_on_found(cx: &Ctx, v: &Value) -> Result<bool> {
    Ok(stuck_term(cx, &scanned(cx, v)?))
}

fn stuck_term(cx: &Ctx, term: &Term) -> bool {
    term.subterms().any(|(t, _)| {
        if !matches!(t, Term::App(..)) {
            return false;
        }
        let (head, args) = t.spine();
        matches!(head.strip_loc(), Term::Def(p) if cx.e.interfaces.values().any(|i| i.projections.contains(p)))
            && args.len() >= 2
            && match args[1].strip_loc().spine().0 {
                Term::Ctor(..) => true,
                Term::Def(d) => cx.g().def(*d).fold,
                _ => false,
            }
    })
}

/// Finds the dictionaries still to be found whose type is known (of the
/// metavariables `only`, if given), except
/// those that unification may still solve through `ty`: unknowns that are
/// arguments of a type in it, as `Tree k [ord := ?d]`'s (stage 4). (One
/// inside a stuck computation, `Add.%add ?d x y`, can't be solved that way.)
/// `ty` computed again if it is an equation (a proof `rewrite` or `calc` uses)
/// stuck on one found now or before, so its sides compute; other types are
/// left as they are, so the terms built from them are what they were
/// (docs/proposals/interfaces.md, "As built (stage 5)").
pub(crate) fn find_ready_dictionaries(
    cx: &Ctx,
    ty: &Value,
    only: Option<&[usize]>,
) -> Result<Option<Value>> {
    let term = scanned(cx, ty)?;
    let g = cx.g();
    let mut stale = stuck_term(cx, &term);
    let zonked = cx.e.zonk_keeping(&term, cx.level(), &|_| true)?;
    let mut keep = Vec::new();
    for (t, _) in zonked.subterms() {
        if let Term::Data(_, args) = t {
            for arg in args {
                if let Term::Meta(m) = arg.strip_loc().spine().0
                    && g.meta_solution(*m).is_none()
                {
                    keep.push(*m);
                }
            }
        }
    }
    if cx.e.solve_ready_instances_keeping(&keep, only)? {
        stale |= stuck_term(cx, &cx.e.zonk_keeping(&term, cx.level(), &|_| true)?);
    }
    if stale && matches!(force(g, ty.clone())?, Value::Eq(..)) {
        Ok(Some(refresh(cx, ty)?))
    } else {
        Ok(None)
    }
}

/// The library's interface called `path` (`Std.Add`), once it's declared.
pub(crate) fn library_interface(e: &Elaborator, path: &str) -> Option<DataId> {
    match e.scope.get(path) {
        Some((Global::Data(d), _)) if e.is_interface(d) => Some(d),
        _ => None,
    }
}

/// Whether the global instance of `interface` for the type `head` is
/// declared and valid (§5.8 (b)): before that, in the prelude's bootstrap
/// phase, operators on `Nat` and `Int` are built directly (D187).
pub(crate) fn instance_ready(e: &Elaborator, interface: DataId, head: DataId) -> bool {
    e.instances
        .get(&(interface, head))
        .is_some_and(|info| info.valid)
}

/// Whether a dictionary of `interface` is in scope, directly or by a
/// superclass path (§5.5 step 4), whatever its type.
pub(crate) fn local_dictionary(cx: &Ctx, interface: DataId) -> Result<bool> {
    Ok(locals(cx)?.iter().any(|c| c.interface == interface))
}

/// The method `field` of `interface` at type `ty`, applied to `args`, with
/// its dictionary found by §5.5 (now, if it can be; an error if there's
/// none). If the dictionary found is a record literal (a global instance's,
/// unfolded from its name) whose field is a definition, applied or not, the
/// result is that
/// field applied to `args` (§5.13's known-instance projection: `x + y` on
/// `Nat` is `Nat.add x y`); otherwise it's the method, `Add.add [add := d] x
/// y`.
pub(crate) fn method_call(
    cx: &mut Ctx,
    interface: DataId,
    field: &str,
    ty: &Value,
    args: Vec<Term>,
) -> Result<Term> {
    let goal = Value::Data(interface, vec![ty.clone()]);
    let meta = implicit_arg(cx, Icit::Auto, &goal);
    cx.e.solve_tree(&meta, true)?;
    let g = cx.g();
    let index = g.data(interface).ctors[0]
        .fields
        .iter()
        .position(|(n, _)| &**n == field)
        .expect("the interface has the field");
    // A global instance is found by name; its record is what's projected.
    let found = force(g, cx.eval(&meta)?)?;
    let found = unfold_folded(g, &found)?.unwrap_or(found);
    let head = match found {
        Value::Ctor(_, 0, fields) if matches!(fields[index], Value::Neutral(Head::Def(_), _)) => {
            cx.quote(&fields[index])?
        }
        _ => {
            let method = cx.e.interfaces[&interface].methods[index];
            note_operator_dictionary(cx, &meta, method, index);
            let ty = cx.quote(ty)?;
            Term::app_icit(
                Term::app_icit(Term::Def(method), ty, Icit::Implicit),
                meta,
                Icit::Auto,
            )
        }
    };
    Ok(args.into_iter().fold(head, Term::app))
}

/// Notes that an operator's call is `method [a] [meta] …`, its dictionary
/// `meta` not found yet: one found later is projected then
/// ([`Elaborator::specialise_operators`]).
fn note_operator_dictionary(cx: &Ctx, meta: &Term, method: DefId, field: usize) {
    if let Term::Meta(m) = meta.spine().0 {
        (cx.e.operator_dictionaries.borrow_mut()).insert(*m, (method, field));
    }
}

impl Elaborator {
    /// `term`, in a context of `depth` variables, with each operator call
    /// whose dictionary wasn't found at the operator ([`method_call`],
    /// [`decide_eq_of`]) but is now a global instance, written as that
    /// instance's field applied to the operator's arguments, as it is when
    /// the dictionary is found at once (`x == y` on `Nat` is `Nat.decEq x
    /// y`). So the term doesn't depend on when the dictionary was found
    /// (docs/proposals/postponement.md §5.10). `None` if there's none.
    pub(crate) fn specialise_operators(&self, term: &Term, depth: usize) -> Result<Option<Term>> {
        if self.operator_dictionaries.borrow().is_empty() {
            return Ok(None);
        }
        let failed = std::cell::Cell::new(None);
        let out = self.specialise_in(term, depth, &failed);
        match (failed.take(), out) {
            (Some(e), _) | (None, Err(e)) => Err(e),
            (None, Ok(out)) => Ok(out),
        }
    }

    fn specialise_in(
        &self,
        term: &Term,
        depth: usize,
        failed: &std::cell::Cell<Option<Diagnostic>>,
    ) -> Result<Option<Term>> {
        let g = &self.globals;
        let hook = |t: &Term, under: usize| -> Option<Term> {
            if !matches!(t, Term::App(..)) {
                return None;
            }
            let (head, args) = t.spine();
            let (Term::Def(method), [_, dict, rest @ ..]) = (head, &args[..]) else {
                return None;
            };
            let Term::Meta(m) = dict.spine().0 else {
                return None;
            };
            let (noted, field) = *self.operator_dictionaries.borrow().get(m)?;
            if noted != *method {
                return None;
            }
            match self.projected(dict, field, depth + under) {
                Ok(Some(projected)) => {
                    let mut out = projected;
                    for arg in rest {
                        match self.specialise_in(arg, depth + under, failed) {
                            Ok(arg2) => {
                                out = Term::app(out, arg2.unwrap_or_else(|| (*arg).clone()))
                            }
                            Err(e) => {
                                failed.set(Some(e));
                                return None;
                            }
                        }
                    }
                    Some(out)
                }
                Ok(None) => None,
                Err(e) => {
                    failed.set(Some(e));
                    None
                }
            }
        };
        Ok(crate::unify::fold_back(g, term, 0, &hook)?)
    }

    /// The field `field` of the dictionary `dict` (a term in `depth`
    /// variables), if it is now a global instance's record literal whose
    /// field is a definition, applied or not: what [`method_call`] projects.
    fn projected(&self, dict: &Term, field: usize, depth: usize) -> Result<Option<Term>> {
        let g = &self.globals;
        let env: Vec<Value> = (0..depth).map(Value::var).collect();
        let found = force(g, stitchwort_core::value::eval(g, &env, dict)?)?;
        let found = unfold_folded(g, &found)?.unwrap_or(found);
        Ok(match found {
            Value::Ctor(_, 0, fields)
                if matches!(fields[field], Value::Neutral(Head::Def(_), _)) =>
            {
                Some(stitchwort_core::value::quote(g, depth, &fields[field])?)
            }
            _ => None,
        })
    }
}

/// §5.16 step 2: if `prop` is a relation field of a dictionary applied to
/// its arguments, `Ord.%lessThan [a] d x y` (as `x < y` through a dictionary
/// `d` evaluates), the paired decider applied to the same dictionary and
/// arguments, `Ord.decLessThan [a] [d] x y`. No new search is made, so it
/// can't find a different dictionary.
pub(crate) fn relation_decider(cx: &Ctx, prop: &Value) -> Result<Option<Term>> {
    if cx.e.interfaces.is_empty() {
        return Ok(None);
    }
    let Value::Neutral(Head::Def(p), spine) = force(cx.g(), prop.clone())? else {
        return Ok(None);
    };
    for info in cx.e.interfaces.values() {
        let Some(&(_, d)) = info
            .relations
            .iter()
            .find(|(r, _)| info.projections[*r] == p)
        else {
            continue;
        };
        // `[a]`, the dictionary, then the relation's arguments.
        let mut term = Term::Def(info.methods[d]);
        for (k, elim) in spine.iter().enumerate() {
            let stitchwort_core::value::Elim::App(v, icit) = elim else {
                return Ok(None);
            };
            let icit = if k == 1 { Icit::Auto } else { *icit };
            term = Term::app_icit(term, cx.quote(v)?, icit);
        }
        if spine.len() < 2 {
            return Ok(None);
        }
        return Ok(Some(term));
    }
    Ok(None)
}

/// §5.16 step 2 on a proposition as written: a relation method applied to
/// its type, its dictionary and its arguments, `Ord.lessThan [a] [d] x y`,
/// gives the paired decider's method applied to the same ones,
/// `Ord.decLessThan [a] [d] x y`. (A dictionary that's a record literal
/// would compute the relation away before [`relation_decider`] sees it.)
pub(crate) fn written_relation_decider(e: &Elaborator, prop: &Term) -> Option<Term> {
    if e.interfaces.is_empty() {
        return None;
    }
    let mut args = Vec::new();
    let mut head = prop.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push((a.clone(), *icit));
        head = f.strip_loc();
    }
    let Term::Def(m) = head else { return None };
    args.reverse();
    if args.len() < 2 {
        return None;
    }
    for info in e.interfaces.values() {
        if let Some(&(_, d)) = info.relations.iter().find(|(r, _)| info.methods[*r] == *m) {
            let decider = Term::Def(info.methods[d]);
            return Some(
                args.into_iter()
                    .fold(decider, |f, (a, icit)| Term::App(Rc::new(f), a, icit)),
            );
        }
    }
    None
}
