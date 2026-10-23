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
use stitchwort_core::value::{conv, eval, quote, unused};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};

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
            let note = format!(
                "{who}; match on {recv} to read it: `| {} {{ {f}, .. }} => …`",
                holders[0]
            );
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
}
