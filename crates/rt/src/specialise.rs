//! Specialisation at the empty row (docs/proposals/effect-polymorphism.md,
//! design E), shared by the runtime's lowering and the JS backend.
//!
//! A definition with effect-row parameters (`[e: Effects]`, which `{e}` in a
//! signature introduces) is generic code: at run time the row is a value,
//! and the library's row eliminators (`Effect.bindIn`, `doneIn`, `liftIn`,
//! `lowerIn`, `widenIn`) test it on every call. Where a call passes the empty
//! row as a constant, which is how the elaborator writes a pure use
//! (`List.map [Empty] f xs`), the backend calls a copy of the definition
//! made for that row instead: its *empty-row variant*. The variant is the
//! definition's body with
//!
//! 1. each row parameter replaced by the constant `Empty` (and a `case` on
//!    one replaced by its `Empty` branch), then
//! 2. every call of a small non-recursive definition that is a single case
//!    on a row parameter, given `Empty` there, replaced by that branch
//!    (`bindIn Empty c k` is `k c`, `doneIn Empty v` is `v`), and
//! 3. the lambdas applied where they're made beta-reduced: an argument used
//!    once, and not inside a lambda, or a value, is put in place of the
//!    parameter; any other is bound by a `let`.
//!
//! Its calls that pass `Empty` are in turn calls of variants, so variants are
//! made transitively from each use, at most one per definition. The variant
//! keeps every parameter of the original, so variables keep their indices:
//! the backends treat a row parameter of a variant as erased. Nothing here is
//! about computations: the pass knows only the parameter types that drive
//! specialisation and the constructor each is specialised on: `Effects` at
//! `Empty`, and `Divergence` at `Total` (D1216,
//! docs/proposals/partial-stage-3.md §5.2), which a bare row's divergence
//! index is in a pure use (`List.map [Empty] [Total] xs f`). "Row
//! parameter" below means a parameter of either type, and "the empty row"
//! its constructor.
//!
//! Generated code is pure and total (a partial computation is a value until
//! the runner runs it), so moving a computation to where its value is used,
//! or dropping one nothing uses, doesn't change what a program does.

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_core::check::telescope;
use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::force;
use stitchwort_core::{DataId, DefId, Globals, Term, Value};
use stitchwort_syntax::Diagnostic;

use crate::erasure::def_shape;

const PASS: &str = "empty-row specialisation";
/// The largest branch (in subterms) inlined at a call with the empty row.
const INLINE_SIZE: usize = 64;
/// Inlining and beta steps per variant, so that nothing runs away.
const FUEL: usize = 1000;
/// The deepest body taken on: one nested more deeply (a long list literal,
/// say) is left as it is, since the passes here recurse over it.
const MAX_NESTING: usize = 1000;

/// Why a variant can't be made: the backends then call the generic code.
enum Fail {
    Resource(stitchwort_core::ResourceError),
    /// A shape this pass doesn't handle (a `case` on a value that isn't a
    /// variable, say).
    Unsupported,
}

impl From<stitchwort_core::ResourceError> for Fail {
    fn from(e: stitchwort_core::ResourceError) -> Self {
        Fail::Resource(e)
    }
}

type Step<T> = std::result::Result<T, Fail>;

/// A row eliminator that inlines at `Empty`: its arity, the level of its row
/// parameter, and its `Empty` branch (under its parameters).
struct Inline {
    arity: usize,
    row: usize,
    branch: Rc<Term>,
}

/// Decides which calls are at the empty row and makes the variants, with
/// what it has worked out about each definition kept.
pub struct Specialiser<'g> {
    g: &'g Globals,
    /// The types that drive specialisation, each with the constructor it's
    /// specialised on: `Effect.Effects` and `Empty`, then `Effect.Divergence`
    /// and `Total`, those the core has.
    drivers: Vec<(DataId, usize)>,
    /// Per definition: the levels of its row parameters, among those its
    /// body takes (empty if none, or if it can't be specialised).
    rows: RefCell<HashMap<DefId, Rc<[usize]>>>,
    /// Per definition: its empty-row variant's body (under its parameters),
    /// or `None` if it can't be made.
    bodies: RefCell<HashMap<DefId, Option<Rc<Term>>>>,
    inlines: RefCell<HashMap<DefId, Option<Rc<Inline>>>>,
    /// Per definition: its body simplified, if it calls a row eliminator
    /// with `Empty`.
    generics: RefCell<HashMap<DefId, Option<Rc<Term>>>>,
}

impl<'g> Specialiser<'g> {
    pub fn new(g: &'g Globals) -> Self {
        let driver = |b: Builtin, ctor: &str| {
            g.registry.loaded_data(b).and_then(|d| {
                let c = g.data(d).ctors.iter().position(|c| &*c.name == ctor)?;
                Some((d, c))
            })
        };
        let drivers = [
            driver(Builtin::Row, "Empty"),
            driver(Builtin::Divergence, "Total"),
        ]
        .into_iter()
        .flatten()
        .collect();
        Specialiser {
            g,
            drivers,
            rows: RefCell::default(),
            bodies: RefCell::default(),
            inlines: RefCell::default(),
            generics: RefCell::default(),
        }
    }

    /// Whether `term` is the constant a row parameter is specialised on
    /// (`Empty`, or `Total`).
    pub fn is_empty_row(&self, term: &Term) -> bool {
        self.empty_ctor(term).is_some()
    }

    /// The constructor `term` is, if it's the constant a row parameter is
    /// specialised on.
    fn empty_ctor(&self, term: &Term) -> Option<usize> {
        match term.strip_loc() {
            Term::Ctor(d, c, fields) if fields.is_empty() && self.drivers.contains(&(*d, *c)) => {
                Some(*c)
            }
            _ => None,
        }
    }

    /// The constant a row parameter of type `d` is specialised on.
    fn driver_of(&self, d: DataId) -> Option<(DataId, usize)> {
        self.drivers.iter().copied().find(|(x, _)| *x == d)
    }

    /// The levels of `id`'s row parameters among the parameters its body
    /// takes. Empty if it has none, or if it has no body or its result is a
    /// partial computation (which isn't specialised).
    pub fn rows(&self, id: DefId) -> std::result::Result<Rc<[usize]>, Diagnostic> {
        if let Some(rows) = self.rows.borrow().get(&id) {
            return Ok(rows.clone());
        }
        let rows = self.find_rows(id)?;
        self.rows.borrow_mut().insert(id, rows.clone());
        Ok(rows)
    }

    fn find_rows(&self, id: DefId) -> std::result::Result<Rc<[usize]>, Diagnostic> {
        let g = self.g;
        let def = g.def(id);
        let none: Rc<[usize]> = Rc::from(Vec::new());
        if self.drivers.is_empty() {
            return Ok(none);
        }
        if def.run_body().is_none() || def.arity == 0 {
            return Ok(none);
        }
        let shape = def_shape(g, id, false)?;
        if shape.partial || shape.result_erased {
            return Ok(none);
        }
        let tel = telescope(g, &def.ty_value, def.span)?;
        let mut rows = Vec::new();
        for (level, (_, ty, _)) in tel.params.iter().enumerate().take(def.arity) {
            if matches!(force(g, ty.clone())?, Value::Data(d, _) if self.driver_of(d).is_some()) {
                rows.push(level);
            }
        }
        Ok(Rc::from(rows))
    }

    /// Whether `id` applied to `args` passes the empty row as a constant for
    /// every one of its row parameters, and its variant can be made.
    pub fn empty_call(&self, id: DefId, args: &[&Term]) -> std::result::Result<bool, Diagnostic> {
        let rows = self.rows(id)?;
        if rows.is_empty()
            || !rows
                .iter()
                .all(|level| args.get(*level).is_some_and(|a| self.is_empty_row(a)))
        {
            return Ok(false);
        }
        Ok(self.empty_body(id)?.is_some())
    }

    /// The body of `id`'s empty-row variant, under all of its parameters
    /// (as `Term::peel_lams` gives the original's), or `None` if it can't be
    /// made. The variant's row parameters are unused.
    pub fn empty_body(&self, id: DefId) -> std::result::Result<Option<Rc<Term>>, Diagnostic> {
        if let Some(body) = self.bodies.borrow().get(&id) {
            return Ok(body.clone());
        }
        let rows = self.rows(id)?;
        let body = if rows.is_empty() {
            None
        } else {
            match self.make_body(id, &rows) {
                Ok(body) => Some(Rc::new(body)),
                Err(Fail::Unsupported) => None,
                Err(Fail::Resource(e)) => return Err(Diagnostic::from(e)),
            }
        };
        self.bodies.borrow_mut().insert(id, body.clone());
        Ok(body)
    }

    /// The erasure mask of `id`'s variant: the original's `mask`, with its
    /// row parameters erased too.
    pub fn empty_mask(
        &self,
        id: DefId,
        mask: &[bool],
    ) -> std::result::Result<Vec<bool>, Diagnostic> {
        let rows = self.rows(id)?;
        Ok(mask
            .iter()
            .enumerate()
            .map(|(level, erased)| *erased || rows.contains(&level))
            .collect())
    }

    fn make_body(&self, id: DefId, rows: &[usize]) -> Step<Term> {
        let def = self.g.def(id);
        let arity = def.arity;
        let body = def.run_body().ok_or(Fail::Unsupported)?;
        let tree = body.peel_lams(arity);
        if nesting(tree) > MAX_NESTING {
            return Err(Fail::Unsupported);
        }
        // The constant each row parameter is specialised on, by level.
        let tel = telescope(self.g, &def.ty_value, def.span).map_err(|_| Fail::Unsupported)?;
        let mut constants: HashMap<usize, (DataId, usize)> = HashMap::default();
        for &level in rows {
            let (_, ty, _) = tel.params.get(level).ok_or(Fail::Unsupported)?;
            let Value::Data(d, _) = force(self.g, ty.clone())? else {
                return Err(Fail::Unsupported);
            };
            constants.insert(level, self.driver_of(d).ok_or(Fail::Unsupported)?);
        }
        // Variable `ix` under `depth` binders is the parameter at level
        // `arity - 1 - (ix - depth)`.
        let row_at = |ix: usize, depth: usize| {
            (ix >= depth && ix - depth < arity)
                .then(|| constants.get(&(arity - 1 - (ix - depth))).copied())
                .flatten()
        };
        let fixed = self.subst(
            tree,
            0,
            &|ix, depth| {
                Ok(match row_at(ix, depth) {
                    Some((d, c)) => Term::Ctor(d, c, Vec::new()),
                    None => Term::Var(ix),
                })
            },
            &|ix, depth| {
                Ok(match row_at(ix, depth) {
                    Some((_, c)) => Scrutinee::Known(c),
                    None => Scrutinee::Var(ix),
                })
            },
        )?;
        let mut fuel = FUEL;
        self.simp(&fixed, &mut fuel)
    }

    /// The body to generate for `id` (under its parameters), if it isn't
    /// its own: where it calls a row eliminator with `Empty` (a pure
    /// callback is `x => doneIn Empty v`, say), that call inlined, as in a
    /// variant. `None` if it has no such call.
    pub fn generic_body(&self, id: DefId) -> std::result::Result<Option<Rc<Term>>, Diagnostic> {
        if let Some(body) = self.generics.borrow().get(&id) {
            return Ok(body.clone());
        }
        let def = self.g.def(id);
        let tree = def.run_body().map(|b| b.peel_lams(def.arity));
        let body = match tree {
            Some(tree) if nesting(tree) <= MAX_NESTING && self.calls_empty_eliminator(tree) => {
                let mut fuel = FUEL;
                match self.simp(tree, &mut fuel) {
                    Ok(body) => Some(Rc::new(body)),
                    Err(Fail::Unsupported) => None,
                    Err(Fail::Resource(e)) => return Err(Diagnostic::from(e)),
                }
            }
            _ => None,
        };
        self.generics.borrow_mut().insert(id, body.clone());
        Ok(body)
    }

    /// Whether `term` calls a row eliminator with `Empty` for its row.
    fn calls_empty_eliminator(&self, term: &Term) -> bool {
        term.subterms().any(|(t, _)| {
            let Term::App(..) = t else {
                return false;
            };
            let (head, args) = t.spine();
            let Term::Def(id) = head.strip_loc() else {
                return false;
            };
            self.inline(*id).is_some_and(|inline| {
                args.len() >= inline.arity && self.is_empty_row(args[inline.row])
            })
        })
    }

    // ------------------------------------------------------------ inlining

    /// `id`'s `Empty` branch, if it's a row eliminator to inline: not
    /// recursive, its body a single `case` on a row parameter, and the
    /// branch small, with no `case` of its own.
    fn inline(&self, id: DefId) -> Option<Rc<Inline>> {
        if let Some(found) = self.inlines.borrow().get(&id) {
            return found.clone();
        }
        let found = self.find_inline(id).map(Rc::new);
        self.inlines.borrow_mut().insert(id, found.clone());
        found
    }

    fn find_inline(&self, id: DefId) -> Option<Inline> {
        let def = self.g.def(id);
        if def.group.as_ref().is_some_and(|m| m.len() > 1) {
            return None;
        }
        let body = def.run_body()?;
        let arity = def.arity;
        let Term::Case(ix, d, branches) = body.peel_lams(arity).strip_loc() else {
            return None;
        };
        let (_, empty) = self.driver_of(*d)?;
        if *ix >= arity {
            return None;
        }
        let branch = branches.get(empty)?.body.clone()?;
        let mut size = 0;
        for (t, _) in branch.subterms() {
            size += 1;
            if size > INLINE_SIZE || matches!(t, Term::Case(..) | Term::NumCase(..)) {
                return None;
            }
            if matches!(t, Term::Def(d) if *d == id) {
                return None;
            }
        }
        Some(Inline {
            arity,
            row: arity - 1 - ix,
            branch,
        })
    }

    // -------------------------------------------------------- simplifying

    /// `term` with the row eliminators applied to `Empty` inlined and the
    /// redexes that makes reduced.
    fn simp(&self, term: &Term, fuel: &mut usize) -> Step<Term> {
        self.g.budget.nesting(PASS)?;
        let go =
            |t: &Rc<Term>, fuel: &mut usize| -> Step<Rc<Term>> { Ok(Rc::new(self.simp(t, fuel)?)) };
        Ok(match term {
            Term::App(..) => {
                let (head, args) = term.spine();
                let head = self.simp(head, fuel)?;
                let args = args
                    .into_iter()
                    .map(|a| self.simp(a, fuel))
                    .collect::<Step<Vec<_>>>()?;
                self.reduce(head, args, fuel)?
            }
            Term::Loc(span, t) => Term::Loc(*span, go(t, fuel)?),
            Term::Ann(t, ty) => Term::Ann(go(t, fuel)?, ty.clone()),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, fuel)?),
            Term::Let(x, ty, v, b, erased) => {
                Term::Let(x.clone(), ty.clone(), go(v, fuel)?, go(b, fuel)?, *erased)
            }
            Term::Ctor(d, c, args) => Term::Ctor(
                *d,
                *c,
                args.iter().map(|a| go(a, fuel)).collect::<Step<_>>()?,
            ),
            Term::Quot(form, args, erased) => Term::Quot(
                *form,
                args.iter().map(|a| go(a, fuel)).collect::<Step<_>>()?,
                *erased,
            ),
            Term::J(m, b, p) => Term::J(m.clone(), go(b, fuel)?, p.clone()),
            Term::Case(ix, d, branches) => Term::Case(
                *ix,
                *d,
                branches
                    .iter()
                    .map(|b| {
                        Ok(Branch {
                            names: b.names.clone(),
                            body: b.body.as_ref().map(|t| go(t, fuel)).transpose()?,
                        })
                    })
                    .collect::<Step<_>>()?,
            ),
            Term::NumCase(ix, arms, default) => Term::NumCase(
                *ix,
                arms.iter()
                    .map(|a| {
                        Ok(NumArm {
                            value: a.value.clone(),
                            body: go(&a.body, fuel)?,
                        })
                    })
                    .collect::<Step<_>>()?,
                go(default, fuel)?,
            ),
            Term::Var(_)
            | Term::Def(_)
            | Term::Data(..)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Meta(_) => term.clone(),
        })
    }

    /// `head` applied to `args`, both simplified: a lambda applied is
    /// beta-reduced, and a row eliminator applied to `Empty` inlined.
    fn reduce(&self, head: Term, mut args: Vec<Term>, fuel: &mut usize) -> Step<Term> {
        if args.is_empty() || *fuel == 0 {
            return Ok(rebuild(head, args));
        }
        let mut core = &head;
        while let Term::Loc(_, t) | Term::Ann(t, _) = core {
            core = t;
        }
        match core {
            Term::Lam(..) => {
                // The lambdas the arguments meet, and the body inside them.
                let mut body = core;
                let mut k = 0;
                while k < args.len()
                    && let Term::Lam(_, _, inner) = body
                {
                    body = inner.strip_loc();
                    k += 1;
                }
                if has_case(body) {
                    return Ok(rebuild(head, args));
                }
                *fuel -= 1;
                let rest = args.split_off(k);
                let reduced = self.beta(body, args)?;
                let reduced = self.simp(&reduced, fuel)?;
                if rest.is_empty() {
                    return Ok(reduced);
                }
                let (h, more) = reduced.spine();
                let h = h.clone();
                let mut all: Vec<Term> = more.into_iter().cloned().collect();
                all.extend(rest);
                self.reduce(h, all, fuel)
            }
            Term::Def(id) => {
                let Some(inline) = self.inline(*id) else {
                    return Ok(rebuild(head, args));
                };
                if args.len() < inline.arity || !self.is_empty_row(&args[inline.row]) {
                    return Ok(rebuild(head, args));
                }
                *fuel -= 1;
                // `(x1 … xn => branch) a1 … an`, reduced as any redex.
                let mut lam = (*inline.branch).clone();
                for _ in 0..inline.arity {
                    lam = Term::Lam("x".into(), stitchwort_core::Icit::Explicit, Rc::new(lam));
                }
                self.reduce(lam, args, fuel)
            }
            _ => Ok(rebuild(head, args)),
        }
    }

    /// `body`, under one binder per argument, with `args` for those
    /// variables (`args[0]` for the outermost): each argument is put in place
    /// if it's a value, or used once and not inside a lambda in `body`, and
    /// dropped if unused; the others are bound by `let`s around the result,
    /// in order.
    fn beta(&self, body: &Term, args: Vec<Term>) -> Step<Term> {
        let g = self.g;
        let k = args.len();
        // For each argument: `None` to put it in place, or its `let`'s
        // position among the `let`s.
        let mut lets = Vec::new();
        let mut placing = Vec::with_capacity(k);
        for (i, arg) in args.iter().enumerate() {
            let (uses, under_lambda) = occurrences(body, k - 1 - i);
            let in_place = uses == 0
                || is_value(arg) && (uses == 1 || !matches!(arg.strip_loc(), Term::Lam(..)))
                || uses == 1 && !under_lambda;
            if in_place {
                placing.push(None);
            } else {
                placing.push(Some(lets.len()));
                lets.push(i);
            }
        }
        let m = lets.len();
        // Variable `ix` under `depth` binders inside `body`: one of the
        // parameters, or a variable outside the redex, which is now under
        // the `let`s instead of the lambdas.
        let param = |ix: usize, depth: usize| -> Option<usize> {
            (ix >= depth && ix - depth < k).then(|| k - 1 - (ix - depth))
        };
        let core = self.subst(
            body,
            0,
            &|ix, depth| {
                Ok(match param(ix, depth) {
                    _ if ix < depth => Term::Var(ix),
                    None => Term::Var(ix - k + m),
                    Some(i) => match placing[i] {
                        None => args[i].shift(g, depth + m, 0)?,
                        Some(t) => Term::Var(depth + (m - 1 - t)),
                    },
                })
            },
            &|ix, depth| {
                Ok(match param(ix, depth) {
                    _ if ix < depth => Scrutinee::Var(ix),
                    None => Scrutinee::Var(ix - k + m),
                    Some(i) => match placing[i] {
                        Some(t) => Scrutinee::Var(depth + (m - 1 - t)),
                        None => match args[i].strip_loc() {
                            Term::Var(j) => Scrutinee::Var(j + depth + m),
                            a if let Some(c) = self.empty_ctor(a) => Scrutinee::Known(c),
                            _ => return Err(Fail::Unsupported),
                        },
                    },
                })
            },
        )?;
        let mut out = core;
        for (t, i) in lets.iter().enumerate().rev() {
            out = Term::Let(
                "x".into(),
                Rc::new(Term::Refl),
                Rc::new(args[*i].shift(g, t, 0)?),
                Rc::new(out),
                false,
            );
        }
        Ok(out)
    }

    // ----------------------------------------------------- substituting

    /// `term`, `depth` binders inside the starting point, with each variable
    /// replaced by `var(ix, depth)` and each `case`'s variable decided by
    /// `scrutinee`: a `case` on a known constructor (with no fields) is that
    /// branch.
    fn subst(
        &self,
        term: &Term,
        depth: usize,
        var: &dyn Fn(usize, usize) -> Step<Term>,
        scrutinee: &dyn Fn(usize, usize) -> Step<Scrutinee>,
    ) -> Step<Term> {
        self.g.budget.nesting(PASS)?;
        let go = |t: &Rc<Term>, depth: usize| -> Step<Rc<Term>> {
            Ok(Rc::new(self.subst(t, depth, var, scrutinee)?))
        };
        let all = |args: &[Rc<Term>]| -> Step<Vec<Rc<Term>>> {
            args.iter().map(|a| go(a, depth)).collect()
        };
        Ok(match term {
            Term::Var(ix) => var(*ix, depth)?,
            Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => term.clone(),
            Term::Data(d, args) => Term::Data(*d, all(args)?),
            Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args)?),
            Term::Quot(form, args, erased) => Term::Quot(*form, all(args)?, *erased),
            Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a, depth)?, go(b, depth + 1)?),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b, depth + 1)?),
            Term::App(f, a, i) => Term::App(go(f, depth)?, go(a, depth)?, *i),
            Term::Ann(e, t) => Term::Ann(go(e, depth)?, go(t, depth)?),
            Term::Let(x, a, v, b, erased) => Term::Let(
                x.clone(),
                go(a, depth)?,
                go(v, depth)?,
                go(b, depth + 1)?,
                *erased,
            ),
            Term::Eq(ty, a, b) => Term::Eq(
                ty.as_ref().map(|t| go(t, depth)).transpose()?,
                go(a, depth)?,
                go(b, depth)?,
            ),
            Term::J(m, b, p) => Term::J(go(m, depth)?, go(b, depth)?, go(p, depth)?),
            Term::Loc(span, t) => Term::Loc(*span, go(t, depth)?),
            Term::Case(ix, d, branches) => match scrutinee(*ix, depth)? {
                Scrutinee::Var(ix) => Term::Case(
                    ix,
                    *d,
                    branches
                        .iter()
                        .map(|b| {
                            Ok(Branch {
                                names: b.names.clone(),
                                body: b
                                    .body
                                    .as_ref()
                                    .map(|body| go(body, depth + b.names.len()))
                                    .transpose()?,
                            })
                        })
                        .collect::<Step<_>>()?,
                ),
                Scrutinee::Known(c) => {
                    let branch = branches.get(c).ok_or(Fail::Unsupported)?;
                    if !branch.names.is_empty() {
                        return Err(Fail::Unsupported);
                    }
                    let body = branch.body.as_ref().ok_or(Fail::Unsupported)?;
                    self.subst(body, depth, var, scrutinee)?
                }
            },
            Term::NumCase(ix, arms, default) => match scrutinee(*ix, depth)? {
                Scrutinee::Var(ix) => Term::NumCase(
                    ix,
                    arms.iter()
                        .map(|a| {
                            Ok(NumArm {
                                value: a.value.clone(),
                                body: go(&a.body, depth)?,
                            })
                        })
                        .collect::<Step<_>>()?,
                    go(default, depth)?,
                ),
                Scrutinee::Known(_) => return Err(Fail::Unsupported),
            },
        })
    }
}

/// What a `case`'s variable becomes in a substitution.
enum Scrutinee {
    Var(usize),
    /// A constructor with no fields, by index: the `case` is that branch.
    Known(usize),
}

/// `head` applied to `args`.
fn rebuild(head: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(head, Term::app)
}

/// How deeply `term` nests, found without recursing.
fn nesting(term: &Term) -> usize {
    let mut pending = vec![(term, 1)];
    let mut deepest = 0;
    while let Some((term, depth)) = pending.pop() {
        deepest = deepest.max(depth);
        term.for_each_child(|child, _| pending.push((child, depth + 1)));
    }
    deepest
}

/// Whether `term` contains a `case`.
fn has_case(term: &Term) -> bool {
    term.subterms()
        .any(|(t, _)| matches!(t, Term::Case(..) | Term::NumCase(..)))
}

/// A term computing nothing: putting it in place of a variable used several
/// times, or inside a lambda, does no work twice.
fn is_value(term: &Term) -> bool {
    match term.strip_loc() {
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Lam(..)
        | Term::Sort(_)
        | Term::Pi(..)
        | Term::Data(..)
        | Term::Eq(..)
        | Term::Refl => true,
        Term::Ctor(_, _, fields) => fields.iter().all(|f| is_value(f)),
        _ => false,
    }
}

/// How often variable `target` occurs in `body`, and whether any
/// occurrence is inside a lambda.
fn occurrences(body: &Term, target: usize) -> (usize, bool) {
    // (term, binders entered, inside a lambda)
    let mut pending = vec![(body, 0usize, false)];
    let (mut uses, mut under) = (0, false);
    while let Some((term, binders, in_lambda)) = pending.pop() {
        match term {
            Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..)
                if *ix == target + binders =>
            {
                uses += 1;
                under |= in_lambda;
            }
            _ => {}
        }
        let lambda = matches!(term, Term::Lam(..));
        term.for_each_child(|child, more| {
            pending.push((child, binders + more, in_lambda || lambda));
        });
    }
    (uses, under)
}

/// What a program uses, with empty-row variants: which definitions are used
/// as they are, and which through their variant.
pub struct Reach {
    pub used: Vec<bool>,
    pub empty: Vec<bool>,
}

/// The definitions the `roots` and the terms `entries` use, directly or
/// indirectly, as [`crate::erasure::reachable`] finds them, except that a
/// call at the empty row ([`Specialiser::empty_call`]) uses the callee's
/// variant, whose body is followed instead. What an `opaque` definition's
/// body uses doesn't count, and an opaque definition has no variant.
pub fn reachable(
    sp: &Specialiser,
    roots: impl IntoIterator<Item = DefId>,
    entries: &[&Term],
    opaque: impl Fn(DefId) -> bool,
) -> std::result::Result<Reach, Diagnostic> {
    let g = sp.g;
    let mut reach = Reach {
        used: vec![false; g.defs.len()],
        empty: vec![false; g.defs.len()],
    };
    // (definition, whether its variant)
    let mut todo: Vec<(DefId, bool)> = roots.into_iter().map(|id| (id, false)).collect();
    let mut found = Vec::new();
    for entry in entries {
        scan(sp, entry, &opaque, &mut found)?;
    }
    todo.append(&mut found);
    while let Some((id, variant)) = todo.pop() {
        let seen = if variant {
            &mut reach.empty[id.0]
        } else {
            &mut reach.used[id.0]
        };
        if std::mem::replace(seen, true) {
            continue;
        }
        let def = g.def(id);
        if !opaque(id) {
            let body = if variant {
                sp.empty_body(id)?
            } else {
                match sp.generic_body(id)? {
                    Some(body) => Some(body),
                    None => def.run_body().cloned(),
                }
            };
            if let Some(body) = body {
                scan(sp, &body, &opaque, &mut found)?;
            }
        }
        for validator in &def.validators {
            scan(sp, &validator.decision, &opaque, &mut found)?;
        }
        todo.append(&mut found);
    }
    Ok(reach)
}

/// The definitions `term` refers to, each with whether it's called at the
/// empty row (so through its variant).
fn scan(
    sp: &Specialiser,
    term: &Term,
    opaque: &impl Fn(DefId) -> bool,
    found: &mut Vec<(DefId, bool)>,
) -> std::result::Result<(), Diagnostic> {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if let Term::App(..) = term {
            let (head, args) = term.spine();
            if let Term::Def(id) = head.strip_loc() {
                let variant = !opaque(*id) && sp.empty_call(*id, &args)?;
                found.push((*id, variant));
                pending.extend(args);
                continue;
            }
        }
        if let Term::Def(id) = term {
            found.push((*id, false));
        }
        term.for_each_child(|child, _| pending.push(child));
    }
    Ok(())
}
