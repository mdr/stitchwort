//! Shared fields (docs/proposals/variant-fields.md §5): a field every
//! constructor of a data type has, explicitly and at the same type, gets a
//! generated accessor `T.f`, one `case` with a branch per constructor, which
//! dot notation (`a.id`), sections (`.id`), pipes and proofs use like any
//! function in `T`'s namespace. A record's projections are the
//! one-constructor case (`records.rs`).
//!
//! Which fields are shared (§5.1) is decided from the type's declaration
//! alone, so it's the same whenever and however the type is loaded:
//!
//! 1. every constructor has an explicit field of that name;
//! 2. the fields its type mentions (syntactically, D603 (a), as records mean
//!    it: `Term::mentions`) are shared fields, with no cycle through it;
//!    parameters may be mentioned freely;
//! 3. its type is the same in every constructor: convertible by the
//!    kernel's `conv`, with the parameters and the shared fields it
//!    mentions as rigid variables;
//! 4. it can be taken out: the type is in `Type`, or the field is a proof.
//!
//! A field whose type mentions one that fails any rule fails too. Why a
//! field isn't shared is kept for the message when `a.f` is used (§5.3).

use std::collections::HashMap;
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{conv, eval, force, quote, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Bracket, Expr, MatchKind, Pattern, Scrutinee};

use crate::check::{Ctx, check};
use crate::{Elaborator, Global, Result};

/// Why a field every constructor names isn't shared.
pub(crate) enum Unshared {
    /// It's an implicit field of `ctor`.
    Implicit { ctor: Name },
    /// Its type in `ctor` mentions `dep`, a field not every constructor has
    /// explicitly (`implicit` says it's an implicit one).
    MentionsOwn {
        ctor: Name,
        dep: Name,
        implicit: bool,
    },
    /// Its type mentions `dep`, which every constructor has but isn't
    /// shared.
    MentionsFailed { dep: Name },
    /// Its type mentions `dep`, whose type (in another constructor) mentions
    /// it.
    Cycle { dep: Name },
    /// Its type in `first` and in `other` differ (each as declared).
    Differs {
        first: (Name, String),
        other: (Name, String),
    },
    /// The type is a proposition, and the field is data.
    PropElim,
}

/// The fields of a data type every constructor names, shared or not.
pub(crate) struct SharedFields {
    /// The shared fields, in the order their accessors are generated (an
    /// earlier one never mentions a later one), each with its position in
    /// each constructor.
    pub shared: Vec<(Name, Vec<usize>)>,
    /// The fields every constructor names that aren't shared, and why.
    pub unshared: Vec<(Name, Unshared)>,
}

impl Elaborator {
    /// Which fields of `d` are shared (the module's rules). An error is the
    /// kernel's conversion running out of resources: never "not shared",
    /// so which accessors exist doesn't depend on the budget (§12.1).
    pub(crate) fn shared_fields(&self, d: DataId) -> Result<SharedFields> {
        let g = &self.globals;
        let data = g.data(d);
        let np = data.params.len();
        let mut out = SharedFields {
            shared: Vec::new(),
            unshared: Vec::new(),
        };
        let Some(first) = data.ctors.first() else {
            return Ok(out);
        };
        let implicit = |c: usize, j: usize| data.ctors[c].implicit.get(j).copied() == Some(true);
        // Every name each constructor has, in the first constructor's order,
        // with its position in each.
        let candidates: Vec<(Name, Vec<usize>)> = first
            .fields
            .iter()
            .filter_map(|(f, _)| {
                let positions: Option<Vec<usize>> = data
                    .ctors
                    .iter()
                    .map(|c| c.fields.iter().position(|(x, _)| x == f))
                    .collect();
                positions.map(|p| (f.clone(), p))
            })
            .collect();
        let index_of = |x: &Name| candidates.iter().position(|(f, _)| f == x);
        // `None` while undecided; then shared (`Ok`) or not.
        let mut status: Vec<Option<std::result::Result<(), Unshared>>> =
            (0..candidates.len()).map(|_| None).collect();
        // What each candidate's type mentions: other candidates.
        let mut deps: Vec<Vec<usize>> = vec![Vec::new(); candidates.len()];
        for (k, (_, positions)) in candidates.iter().enumerate() {
            for (c, &pos) in positions.iter().enumerate() {
                let ctor = &data.ctors[c];
                if implicit(c, pos) {
                    status[k].get_or_insert(Err(Unshared::Implicit {
                        ctor: ctor.name.clone(),
                    }));
                }
                let ty = &ctor.fields[pos].1;
                for j in 0..pos {
                    if !ty.mentions(pos - 1 - j) {
                        continue;
                    }
                    let dep = &ctor.fields[j].0;
                    match index_of(dep) {
                        Some(i) if !implicit(c, j) => {
                            if !deps[k].contains(&i) {
                                deps[k].push(i);
                            }
                        }
                        _ => {
                            status[k].get_or_insert(Err(Unshared::MentionsOwn {
                                ctor: ctor.name.clone(),
                                dep: dep.clone(),
                                implicit: implicit(c, j),
                            }));
                        }
                    }
                }
            }
        }
        // Decided in dependency order, ties by the first constructor's: the
        // shared fields so far are rigid variables after the parameters.
        let mut level_of: HashMap<usize, usize> = HashMap::new();
        loop {
            let next = (0..candidates.len())
                .find(|&k| status[k].is_none() && deps[k].iter().all(|&i| status[i].is_some()));
            let Some(k) = next else { break };
            if let Some(&i) = deps[k]
                .iter()
                .find(|&&i| !matches!(status[i], Some(Ok(()))))
            {
                status[k] = Some(Err(Unshared::MentionsFailed {
                    dep: candidates[i].0.clone(),
                }));
                continue;
            }
            let positions = &candidates[k].1;
            if data.sort == Sort::Prop && first.field_sorts[positions[0]] != Sort::Prop {
                status[k] = Some(Err(Unshared::PropElim));
                continue;
            }
            // Each constructor's type for it, over the parameters and the
            // shared fields.
            let level = np + level_of.len();
            let declared = |c: usize| -> Result<Value> {
                let ctor = &data.ctors[c];
                let mut env: Vec<Value> = (0..np).map(Value::var).collect();
                for (x, _) in &ctor.fields[..positions[c]] {
                    env.push(match index_of(x).and_then(|i| level_of.get(&i)) {
                        Some(&l) => Value::var(l),
                        None => unused(),
                    });
                }
                Ok(eval(g, &env, &ctor.fields[positions[c]].1)?)
            };
            let mut differs = None;
            if data.ctors.len() > 1 {
                let in_first = declared(0)?;
                for c in 1..data.ctors.len() {
                    if !conv(g, level, &in_first, &declared(c)?)? {
                        differs = Some(c);
                        break;
                    }
                }
            }
            if let Some(c) = differs {
                let shown = |c: usize| {
                    let ctor = &data.ctors[c];
                    let mut names: Vec<Name> = data.params.iter().map(|(x, _)| x.clone()).collect();
                    names.extend(ctor.fields.iter().map(|(x, _)| x.clone()));
                    names.truncate(np + positions[c]);
                    let ty = stitchwort_core::pretty::term(g, &names, &ctor.fields[positions[c]].1);
                    (ctor.name.clone(), ty)
                };
                status[k] = Some(Err(Unshared::Differs {
                    first: shown(0),
                    other: shown(c),
                }));
                continue;
            }
            level_of.insert(k, np + level_of.len());
            status[k] = Some(Ok(()));
            out.shared.push(candidates[k].clone());
        }
        let undecided: Vec<bool> = status.iter().map(Option::is_none).collect();
        for (k, (f, _)) in candidates.iter().enumerate() {
            match status[k].take() {
                Some(Ok(())) => {}
                Some(Err(why)) => out.unshared.push((f.clone(), why)),
                None => {
                    let dep = deps[k]
                        .iter()
                        .find(|&&i| undecided[i])
                        .map_or_else(|| f.clone(), |&i| candidates[i].0.clone());
                    out.unshared.push((f.clone(), Unshared::Cycle { dep }));
                }
            }
        }
        Ok(out)
    }

    /// Defines `T.f : [params] [indices] -> (r : T params indices) -> F`
    /// for each shared field `f` of `d`, by a `case` on `r` returning each
    /// constructor's field, in the order [`Self::shared_fields`] gives. In
    /// `F`, the shared fields it mentions are their accessors applied to
    /// `r`. `hidden` is put before each field's name (an interface's own
    /// projections are `R.%field`, out of the way of its methods). Returns
    /// each field's accessor, by name.
    pub(crate) fn accessors(&mut self, d: DataId, hidden: &str) -> Result<HashMap<Name, DefId>> {
        let shared = self.shared_fields(d)?.shared;
        let mut made: HashMap<Name, DefId> = HashMap::new();
        for (field, positions) in shared {
            let g = &self.globals;
            let data = g.data(d);
            let (np, ni) = (data.params.len(), data.indices.len());
            let n = np + ni;
            let first = &data.ctors[0];
            // In the context of the parameters, indices and `r`: the earlier
            // fields as accessors of `r`.
            let with_r: Vec<Value> = (0..=n).map(Value::var).collect();
            let mut env: Vec<Value> = with_r[..np].to_vec();
            for (x, _) in &first.fields[..positions[0]] {
                env.push(match made.get(x) {
                    Some(p) => eval(g, &with_r, &applied(*p, n))?,
                    None => unused(),
                });
            }
            let result = quote(g, n + 1, &eval(g, &env, &first.fields[positions[0]].1)?)?;
            let args: Vec<Term> = (0..n).map(|k| Term::Var(n - 1 - k)).collect();
            let mut ty = Term::Pi(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::data(d, args)),
                Rc::new(result),
            );
            let branches: Vec<Branch> = data
                .ctors
                .iter()
                .zip(&positions)
                .map(|(ctor, &pos)| Branch {
                    body: Some(Rc::new(Term::Var(ctor.fields.len() - 1 - pos))),
                    names: ctor.fields.iter().map(|(x, _)| x.clone()).collect(),
                })
                .collect();
            let mut body = Term::Lam(
                "r".into(),
                Icit::Explicit,
                Rc::new(Term::Case(0, d, branches.into())),
            );
            for (x, t) in data.params.iter().chain(&data.indices).rev() {
                ty = Term::Pi(x.clone(), Icit::Implicit, Rc::new(t.clone()), Rc::new(ty));
                body = Term::Lam(x.clone(), Icit::Implicit, Rc::new(body));
            }
            let name: Name = format!("{}.{hidden}{field}", data.name).into();
            let span = data.span;
            // A proof field's accessor is a theorem, as one written by hand
            // would be (the core's `And.left` was): it isn't unfolded while
            // checking. A record's projections stay definitions, as they
            // were before records shared this generator, so their hashes
            // don't move.
            let theorem = !data.record && first.field_sorts[positions[0]] == Sort::Prop;
            let id = kernel::declare_def(&mut self.globals, &name, &ty, theorem, false, span)?;
            kernel::define_def(&mut self.globals, id, &body)?;
            // In the type's namespace, but not visible by its short name:
            // reached through a value (`a.id`), or written in full
            // (`Shape.id`).
            let key = Self::member_key(&self.data_key(d), &format!("{hidden}{field}"));
            self.scope.insert(&key, Global::Def(id), span, false);
            self.scope.mark_member(&key);
            // `Pair.fst` and `Pair.snd` are the compiler's.
            if self.loading_prelude {
                self.bind_builtin_def(id)?;
            }
            made.insert(field, id);
        }
        Ok(made)
    }
}

/// Accessor `p` applied to the `n` parameters and indices and to `r`, in
/// their context (`r` last).
pub(crate) fn applied(p: DefId, n: usize) -> Term {
    let mut term = Term::Def(p);
    for k in 0..n {
        term = Term::app_icit(term, Term::Var(n - k), Icit::Implicit);
    }
    Term::app(term, Term::Var(0))
}

/// "`A`", "`A` and `B`", "`A`, `B` and `C`".
fn listed(names: &[&Name]) -> String {
    let quoted: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
    match quoted.split_last() {
        None => String::new(),
        Some((last, [])) => last.clone(),
        Some((last, rest)) => format!("{} and {last}", rest.join(", ")),
    }
}

impl Elaborator {
    /// Why `a.f` finds nothing when `a`'s type is data type `d` and some
    /// constructor of `d` has a field `f` that isn't shared
    /// (docs/proposals/variant-fields.md §5.3): the error's message and
    /// note. `None` if no constructor has a field `f`. `recv` is how the
    /// value is shown (`` `a` ``).
    pub(crate) fn unshared_member(
        &self,
        d: DataId,
        f: &str,
        recv: &str,
    ) -> Option<(String, String)> {
        self.unshared_member_for(d, f, recv, "read")
    }

    /// [`Self::unshared_member`], for a use that would `read` the field or
    /// `update` it (`{ a | f = … }`, §6.1), which the note's advice suits.
    pub(crate) fn unshared_member_for(
        &self,
        d: DataId,
        f: &str,
        recv: &str,
        use_: &str,
    ) -> Option<(String, String)> {
        let g = &self.globals;
        let data = g.data(d);
        let has = |c: &&stitchwort_core::globals::Ctor| c.fields.iter().any(|(x, _)| **x == *f);
        if !data.ctors.iter().any(|c| has(&c)) {
            return None;
        }
        let message = format!(
            "`{}` has no shared field `{f}`",
            crate::scope::display(&self.data_key(d))
        );
        let lacking: Vec<&Name> = data
            .ctors
            .iter()
            .filter(|c| !has(c))
            .map(|c| &c.name)
            .collect();
        if !lacking.is_empty() {
            let holders: Vec<&Name> = data.ctors.iter().filter(has).map(|c| &c.name).collect();
            let who = if holders.len() == 1 {
                format!("only {} has `{f}`", listed(&holders))
            } else if lacking.len() == 1 {
                format!(
                    "{} have `{f}`, but {} doesn't",
                    listed(&holders),
                    listed(&lacking)
                )
            } else {
                format!("only {} have `{f}`", listed(&holders))
            };
            let note = if use_ == "update" {
                format!(
                    "{who}; match on {recv} and rebuild the constructor: `| {} {{ .. }} => …`",
                    holders[0]
                )
            } else {
                format!(
                    "{who}; match on {recv} to read it: `| {} {{ {f}, .. }} => …`",
                    holders[0]
                )
            };
            return Some((message, note));
        }
        let unshared = self.shared_fields(d).ok()?.unshared;
        let why = |x: &str| unshared.iter().find(|(n, _)| **n == *x).map(|(_, w)| w);
        let mut notes = Vec::new();
        let mut field: Name = f.into();
        // Follows "mentions a field that isn't shared" to the root cause.
        for _ in 0..=unshared.len() {
            let Some(reason) = why(&field) else { break };
            let (note, next) = self.unshared_reason(d, &field, reason);
            notes.push(note);
            match next {
                Some(dep) => field = dep,
                None => break,
            }
        }
        Some((message, notes.join(": ")))
    }

    /// One step of [`Self::unshared_member`]'s explanation, and the field to
    /// explain next, if the reason is another field's.
    fn unshared_reason(&self, d: DataId, f: &Name, why: &Unshared) -> (String, Option<Name>) {
        let data = self.globals.data(d);
        match why {
            Unshared::Implicit { ctor } => {
                (format!("`{f}` is an implicit field of `{ctor}`"), None)
            }
            Unshared::MentionsOwn {
                ctor,
                dep,
                implicit: true,
            } => (
                format!("`{f}`'s type in `{ctor}` mentions `{dep}`, an implicit field of `{ctor}`"),
                None,
            ),
            Unshared::MentionsOwn { dep, .. } => {
                let holders: Vec<&Name> = data
                    .ctors
                    .iter()
                    .filter(|c| c.fields.iter().any(|(x, _)| x == dep))
                    .map(|c| &c.name)
                    .collect();
                let verb = if holders.len() == 1 { "has" } else { "have" };
                (
                    format!(
                        "`{f}`'s type mentions `{dep}`, which only {} {verb}",
                        listed(&holders)
                    ),
                    None,
                )
            }
            Unshared::MentionsFailed { dep } => (
                format!("`{f}`'s type mentions `{dep}`, which isn't shared"),
                Some(dep.clone()),
            ),
            Unshared::Cycle { dep } => (
                format!(
                    "`{f}`'s type mentions `{dep}` in one constructor, and `{dep}`'s type \
                     depends on `{f}` in another"
                ),
                None,
            ),
            Unshared::Differs {
                first: (a, ta),
                other: (b, tb),
            } => (
                format!("`{f}` is `{ta}` in `{a}` but `{tb}` in `{b}`"),
                None,
            ),
            Unshared::PropElim => (
                format!(
                    "`{}` is a proposition, and `{f}` is data, which can't be taken out of a proof",
                    data.name
                ),
                None,
            ),
        }
    }

    /// The accessor of `d`'s shared field `f`.
    fn accessor(&self, d: DataId, f: &str) -> Option<DefId> {
        let key = Self::member_key(&self.data_key(d), f);
        match self.scope.get(&key) {
            Some((Global::Def(id), _)) => Some(id),
            _ => None,
        }
    }
}

// Updates (docs/proposals/variant-fields.md §6).

/// One `let` an update binds around its `match`: name, type, value.
type Bound = (Name, Term, Term);

/// `{ base | f = e, … }` where `base : ty`, a data type that isn't a record
/// (§6): every `f` is a shared field, and the result is the constructor
/// `base` is, rebuilt with those fields replaced. Elaborated as
///
/// ```text
/// let %base := base            (unless it's a variable)
/// let %new%f := e  …           (in the shared fields' order)
/// match %base with
///   | C x₁ … xₙ => C x₁ … %new%f … xₙ
///   | …
/// ```
///
/// through the ordinary `match`, so the base and each new value are
/// evaluated once, and a new value whose type mentions the base is refined
/// in each alternative (its `let` is copied there as a hypothesis). Every
/// field whose type mentions a replaced one, in any constructor, must be
/// replaced too (the closure, §6.1); an indexed family's values aren't
/// updated. The `match` is code the compiler writes, so navigation notes
/// nothing in it.
pub(crate) fn variant_update(
    cx: &mut Ctx,
    base: Term,
    ty: &Value,
    fields: &[(ast::Name, Expr)],
) -> Result<Term> {
    let g = cx.g();
    let Value::Data(d, args) = force(g, ty.clone())? else {
        unreachable!("only called on a data type")
    };
    let shared = cx.e.shared_fields(d)?.shared;
    let data = g.data(d);
    let type_name = crate::scope::display(&cx.e.data_key(d)).to_string();
    let mut seen: Vec<&ast::Name> = Vec::new();
    for (name, _) in fields {
        if let Some(first) = seen.iter().find(|s| s.text == name.text) {
            return Err(crate::error(
                "E-RECORD-FIELD",
                name.span,
                format!("field `{}` is given twice", name.text),
            )
            .with_label(first.span, "first given here"));
        }
        seen.push(name);
        if shared.iter().any(|(f, _)| **f == *name.text) {
            cx.e.note_field(d, name);
            continue;
        }
        let (message, note) = match cx
            .e
            .unshared_member_for(d, &name.text, "the value", "update")
        {
            Some(found) => found,
            None => {
                let names: Vec<String> = shared.iter().map(|(f, _)| format!("`{f}`")).collect();
                let note = if names.is_empty() {
                    "it has no shared fields".to_string()
                } else {
                    format!("its shared fields are {}", names.join(", "))
                };
                (format!("`{type_name}` has no field `{}`", name.text), note)
            }
        };
        return Err(crate::error("E-UNKNOWN-FIELD", name.span, message).with_note(note));
    }
    if !data.indices.is_empty() {
        return Err(cx
            .error(
                "E-RECORD-UPDATE",
                format!("a value of the indexed family `{type_name}` can't be updated by field"),
                "this update",
            )
            .with_note(
                "a replaced field could be one an index is computed from; match on the value \
                 and rebuild its constructor",
            ));
    }
    let named = |f: &Name| fields.iter().any(|(n, _)| *n.text == **f);
    closed(cx, d, &shared, &named, &type_name)?;

    let params: Vec<Value> = args[..data.params.len()].to_vec();
    let mark = cx.mark();
    let mut bound: Vec<Bound> = Vec::new();
    let result = update_match(cx, d, base, ty, &params, &shared, fields, &mut bound);
    cx.reset(mark);
    let mut term = result?;
    for (x, ty_term, value) in bound.into_iter().rev() {
        term = Term::let_(x, ty_term, value, term);
    }
    Ok(term)
}

/// [`variant_update`]'s `let`s, bound in `cx` and pushed on `bound`, and
/// its `match`, in their context.
#[allow(clippy::too_many_arguments)]
fn update_match(
    cx: &mut Ctx,
    d: DataId,
    base: Term,
    ty: &Value,
    params: &[Value],
    shared: &[(Name, Vec<usize>)],
    fields: &[(ast::Name, Expr)],
    bound: &mut Vec<Bound>,
) -> Result<Term> {
    let g = cx.g();
    let data = g.data(d);
    let named = |f: &Name| fields.iter().any(|(n, _)| *n.text == **f);
    // The base, as a variable.
    let base_name = "%base";
    match base.strip_loc() {
        Term::Var(ix) => {
            let level = cx.level() - 1 - ix;
            cx.alias(base_name, level);
        }
        _ => {
            let ty_term = cx.quote(ty)?;
            cx.define(
                Some(base_name),
                base_name.into(),
                ty.clone(),
                ty_term.clone(),
                base.clone(),
            )?;
            bound.push((base_name.into(), ty_term, base));
        }
    }
    let base_level = cx.lookup(base_name).expect("just bound");
    let new_name = |f: &str| format!("%new%{f}");
    // The new values, in the shared fields' order: a field's type mentions
    // only earlier ones, each its new value if replaced and its accessor of
    // the base if kept.
    let first = &data.ctors[0];
    for (field, positions) in shared {
        let Some((_, expr)) = fields.iter().find(|(n, _)| *n.text == **field) else {
            continue;
        };
        let mut env = params.to_vec();
        for (x, _) in &first.fields[..positions[0]] {
            let accessor = shared
                .iter()
                .any(|(f, _)| f == x)
                .then(|| cx.e.accessor(d, x))
                .flatten();
            let value = if let Some(level) = cx.lookup(&new_name(x)) {
                cx.env[level].clone()
            } else if let Some(p) = accessor {
                let mut term = Term::Def(p);
                for v in params {
                    term = Term::app_icit(term, cx.quote(v)?, Icit::Implicit);
                }
                let base_var = Term::Var(cx.level() - 1 - base_level);
                cx.eval(&Term::app(term, base_var))?
            } else {
                unused()
            };
            env.push(value);
        }
        let field_ty = eval(g, &env, &first.fields[positions[0]].1)?;
        let term = check(cx, expr, &field_ty)?;
        let ty_term = cx.quote(&field_ty)?;
        let x = new_name(field);
        cx.define(
            Some(&x),
            x.as_str().into(),
            field_ty,
            ty_term.clone(),
            term.clone(),
        )?;
        bound.push((x.as_str().into(), ty_term, term));
    }
    // The `match`, one alternative per constructor, which names each
    // constructor by its key, so whatever `C` means here doesn't matter.
    let span = cx.span;
    let name = |text: String| ast::Name { text, span };
    let var = |text: String| Expr::Var(name(text));
    let owner = cx.e.data_key(d);
    let old = |k: usize| format!("%old%{k}");
    let alts: Vec<Alt> = data
        .ctors
        .iter()
        .map(|ctor| {
            let key = format!(
                "{}{}",
                crate::scope::EXACT_KEY,
                Elaborator::member_key(&owner, &ctor.name)
            );
            let mut patterns = Vec::new();
            let mut body = var(key.clone());
            for (k, (f, _)) in ctor.fields.iter().enumerate() {
                let (pattern, arg) = if ctor.implicit.get(k).copied() == Some(true) {
                    (
                        Pattern::Named(
                            name(f.to_string()),
                            Box::new(Pattern::Var(name(old(k)))),
                            span,
                        ),
                        Expr::NamedArg(
                            name(f.to_string()),
                            Box::new(var(old(k))),
                            span,
                            Bracket::Square,
                        ),
                    )
                } else if named(f) {
                    (Pattern::Wildcard(span), var(new_name(f)))
                } else {
                    (Pattern::Var(name(old(k))), var(old(k)))
                };
                patterns.push(pattern);
                body = Expr::App(Box::new(body), Box::new(arg));
            }
            Alt {
                patterns: vec![Pattern::Ctor(name(key), patterns, span)],
                body,
                span,
            }
        })
        .collect();
    let expr = Expr::Match {
        scrutinees: vec![Scrutinee {
            name: None,
            expr: var(base_name.to_string()),
        }],
        alts,
        span,
        kind: MatchKind::Match,
    };
    Elaborator::unnoted_in(cx, |cx| crate::matching::check_match(cx, &expr, ty))
}

/// Refuses an update of the shared fields `named` of `d` unless, in every
/// constructor, each field whose type mentions a replaced one (explicit or
/// implicit, data or proof, transitively) is named too (§6.1).
fn closed(
    cx: &Ctx,
    d: DataId,
    shared: &[(Name, Vec<usize>)],
    named: &dyn Fn(&Name) -> bool,
    type_name: &str,
) -> Result<()> {
    let data = cx.g().data(d);
    for ctor in &data.ctors {
        // For each field: if it's replaced, the named field that forces it.
        let mut forced: Vec<Option<Name>> = Vec::new();
        for (j, (field, field_ty)) in ctor.fields.iter().enumerate() {
            if named(field) {
                forced.push(Some(field.clone()));
                continue;
            }
            let Some(i) = (0..j).find(|&i| forced[i].is_some() && field_ty.mentions(j - 1 - i))
            else {
                forced.push(None);
                continue;
            };
            let root = forced[i].clone().expect("just found");
            let dep = &ctor.fields[i].0;
            if shared.iter().any(|(f, _)| f == field) {
                return Err(cx
                    .error(
                        "E-RECORD-UPDATE",
                        format!("updating `{root}` needs `{field}` updated too"),
                        format!("the type of `{field}` mentions `{dep}`"),
                    )
                    .with_note(format!(
                        "give a new `{field}` for the new `{dep}`: `{{ … | {dep} = …, {field} = … }}`"
                    )));
            }
            let what = if ctor.implicit.get(j).copied() == Some(true) {
                format!("the implicit field `{field}`")
            } else {
                format!("`{field}`, which isn't shared,")
            };
            return Err(cx
                .error(
                    "E-RECORD-UPDATE",
                    format!("`{root}` can't be updated on every `{type_name}`"),
                    "this update",
                )
                .with_note(format!(
                    "in `{}`, the type of {what} mentions `{dep}`, and an update can only give \
                     shared fields: match on the value and rebuild `{}`",
                    ctor.name, ctor.name
                )));
        }
    }
    Ok(())
}
