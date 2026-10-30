//! EXPERIMENTAL: a measuring prototype of lemma search by type (SW-915,
//! docs/proposals/search.md §4). Not a stable interface, and not used by
//! checking: only the hidden `stitchwort dev search` calls it.
//!
//! A pattern is elaborated as a closed expression whose `_`s are left as
//! unknowns. Each theorem's binders are opened with fresh unknowns, and the
//! pattern is unified, folded (glued, with calls compared by their
//! arguments), against its conclusion, or with `anywhere` against each of
//! its hypotheses and each call inside it with the pattern's head. Every
//! attempt runs under its own small budget and is undone afterwards.

use std::collections::BTreeSet;

use stitchwort_core::value::{Head, Value, eval, force};
use stitchwort_core::{DefId, Globals, Limits, Term};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, infer};

type Result<T> = std::result::Result<T, Diagnostic>;

/// The limits of one match attempt: a comparison that needs more is no match.
const ATTEMPT: Limits = Limits {
    work: 200_000,
    stack: 4 * 1024 * 1024,
    size: 100_000,
    frames: 10_000,
};

/// What a pattern's outermost layer is, for the head filter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HeadKey {
    Def(DefId),
    Data(stitchwort_core::DataId),
    Eq,
    Pi,
    Other,
}

/// An elaborated pattern.
pub struct Pattern {
    value: Value,
    /// The unknowns of each named hole's occurrences (`?x`), which must
    /// match the same thing.
    pub groups: Vec<Vec<usize>>,
    /// The definitions the pattern names: a theorem must mention each.
    pub constants: BTreeSet<DefId>,
    pub head: HeadKey,
    /// How many unknowns there were once it was elaborated.
    metas: usize,
}

/// Where a pattern matched a theorem.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Place {
    /// The whole type after its leading implicit parameters, for a pattern
    /// that is a function type (`List ?a → List ?a`).
    Whole,
    /// With [`Mode::Permute`] or [`Mode::Subset`]: the conclusions match
    /// and each of the pattern's explicit parameters matches a different one
    /// of the theorem's, in any order (draft 2 §5.2, measured there).
    Reordered,
    Conclusion,
    /// With [`Mode::Rewrite`]: the left side of an equation `l = r` that is
    /// the conclusion (`SearchRewrite`; draft 2 §5.3).
    Left,
    /// The right side, for rewriting from right to left.
    Right,
    Hypothesis,
    Inside,
}

/// What a search compares, besides the plain targets (EXPERIMENTAL, for
/// draft 2's measurements).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// Draft 1: the whole type (for a function pattern), the conclusion,
    /// and with `anywhere` the hypotheses and calls inside.
    Plain,
    /// Also, for a function pattern: the same conclusion and the same
    /// number of explicit parameters, matched in any order.
    Permute,
    /// Also, for a function pattern: the same conclusion, and each of the
    /// pattern's explicit parameters matched by a different one of the
    /// theorem's, which may have more (Loogle's `matchHyps`).
    Subset,
    /// Only the two sides of a conclusion that is an equation.
    Rewrite,
}

/// Which part of a theorem [`Elaborator::theorem_pattern`] makes into a
/// pattern.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Side {
    /// The conclusion, with every variable a hole.
    Conclusion,
    /// The left side of a conclusion `l = r`, with every variable a hole.
    Left,
}

/// A theorem the pattern matched.
#[derive(Clone, Debug)]
pub struct Hit {
    pub id: DefId,
    pub place: Place,
    /// The size of what the theorem's own variables took from the pattern:
    /// smaller is more specific (a lemma `x = x` takes a whole side).
    pub absorbed: usize,
    /// How many of the pattern's unknowns had to become more than one of
    /// the theorem's variables: fewer is a closer fit (`List.lengthAppend`
    /// before `List.lengthSnoc` for `List.length (_ ++ _) = _`).
    pub instantiated: usize,
    /// The size of the theorem's type, in nodes (Isabelle's, Rocq's and
    /// Loogle's first ranking key).
    pub size: usize,
    /// How many explicit parameters the rest of the type doesn't mention:
    /// the hypotheses, as against the variables (Isabelle's second key).
    pub hyps: usize,
}

/// The size of `id`'s type and the number of its hypotheses (see [`Hit`]).
pub fn shape(g: &Globals, id: DefId) -> (usize, usize) {
    let ty = &g.def(id).ty;
    let mut hyps = 0;
    let mut t = ty.strip_loc();
    while let Term::Pi(_, icit, _, cod) = t {
        if *icit == stitchwort_core::Icit::Explicit && !cod.mentions(0) {
            hyps += 1;
        }
        t = cod.strip_loc();
    }
    (size(ty), hyps)
}

/// Counts of what a search did, for measuring.
#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub candidates: usize,
    pub filtered_out: usize,
    pub unifications: usize,
    pub resource_outs: usize,
}

/// What an unknown is after a match.
enum Now {
    Meta(usize),
    Size(usize),
}

/// The definitions a term names.
pub fn constants(term: &Term) -> BTreeSet<DefId> {
    term.subterms()
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        })
        .collect()
}

fn head_key(term: &Term) -> HeadKey {
    match term.spine().0.strip_loc() {
        Term::Def(id) => HeadKey::Def(*id),
        Term::Data(d, _) => HeadKey::Data(*d),
        Term::Eq(..) => HeadKey::Eq,
        Term::Pi(..) => HeadKey::Pi,
        _ => HeadKey::Other,
    }
}

/// The size of a term, in nodes.
fn size(term: &Term) -> usize {
    term.subterms()
        .filter(|(t, _)| !matches!(t, Term::Loc(..)))
        .count()
}

impl Elaborator {
    /// Elaborates a search pattern. `named` lists, per named hole, the spans
    /// of its occurrences, each written as `_` in `expr`.
    pub fn search_pattern(&mut self, expr: &Expr, named: &[Vec<Span>]) -> Result<Pattern> {
        self.clear_metas();
        let was = self.globals.glue.replace(self.glue);
        let saved = self.globals.budget.start(self.limits);
        let result = (|| -> Result<Pattern> {
            let mut cx = Ctx::new(self, expr.span());
            let (term, _) = infer(&mut cx, expr)?;
            let value = cx.eval(&term)?;
            let g = &self.globals;
            let zonked =
                stitchwort_core::value::quote_folded(g, 0, &value).unwrap_or_else(|_| term.clone());
            // The unknown of a hole is the last one made at its span (an
            // inferred `_` makes its type's first).
            let metas = g.metas.borrow();
            let at = |span: &Span| {
                (0..metas.len())
                    .rev()
                    .find(|m| metas[*m].span == *span && metas[*m].solution.is_none())
            };
            let groups = named
                .iter()
                .map(|spans| spans.iter().filter_map(at).collect())
                .collect();
            Ok(Pattern {
                head: head_key(&zonked),
                constants: constants(&zonked),
                value,
                groups,
                metas: metas.len(),
            })
        })();
        self.globals.budget.restore(saved);
        self.globals.glue.set(was);
        result
    }

    /// A pattern made from theorem `id` itself: its conclusion (or the left
    /// side of it, an equation), with each of its variables a hole. For the
    /// self-retrieval measurements of draft 2 (§6): searching with it must
    /// find `id`, and where `id` ranks measures the ranking. `None` for a
    /// conclusion that is one of the theorem's variables, or (with
    /// [`Side::Left`]) one that isn't an equation.
    pub fn theorem_pattern(&mut self, id: DefId, side: Side) -> Option<Pattern> {
        self.clear_metas();
        let g = &self.globals;
        let was = g.glue.replace(self.glue);
        let made = (|| -> std::result::Result<Option<Pattern>, stitchwort_core::ResourceError> {
            let _op = g.budget.operation(ATTEMPT);
            let def = g.def(id);
            let mut env: Vec<Value> = Vec::new();
            let mut t = def.ty.strip_loc();
            while let Term::Pi(_, _, _, cod) = t {
                let m = g.new_meta(def.span);
                env.push(eval(g, &[], &Term::Meta(m))?);
                t = cod.strip_loc();
            }
            let value = match (side, t) {
                (Side::Conclusion, _) => eval(g, &env, t)?,
                (Side::Left, Term::Eq(_, left, _)) => eval(g, &env, left)?,
                _ => return Ok(None),
            };
            if let Value::Neutral(Head::Meta(_), s) = force(g, value.clone())?
                && s.is_empty()
            {
                return Ok(None);
            }
            let quoted = stitchwort_core::value::quote_folded(g, 0, &value)?;
            Ok(Some(Pattern {
                head: head_key(&quoted),
                constants: constants(&quoted),
                value,
                groups: Vec::new(),
                metas: g.metas.borrow().len(),
            }))
        })();
        g.glue.set(was);
        made.ok().flatten()
    }

    /// The definitions `id`'s type names, read back folded as a pattern is
    /// (so a field such as `Ord.compare` is named the same way in both).
    pub fn type_constants(&self, id: DefId) -> BTreeSet<DefId> {
        let g = &self.globals;
        let was = g.glue.replace(self.glue);
        let found = (|| {
            let _op = g.budget.operation(ATTEMPT);
            let v = eval(g, &[], &g.def(id).ty)?;
            stitchwort_core::value::quote_folded(g, 0, &v)
        })();
        g.glue.set(was);
        let mut all = constants(&g.def(id).ty);
        if let Ok(t) = found {
            all.extend(constants(&t));
        }
        all
    }

    /// Matches `pattern` against theorem (or definition) `id`'s type. With
    /// `filter` (the theorem's [`Elaborator::type_constants`]), a theorem
    /// that doesn't mention each of the pattern's constants is skipped
    /// without unifying.
    pub fn search_one(
        &self,
        pattern: &Pattern,
        id: DefId,
        anywhere: bool,
        mode: Mode,
        filter: Option<&BTreeSet<DefId>>,
        stats: &mut Stats,
    ) -> Option<Hit> {
        let g = &self.globals;
        let def = g.def(id);
        stats.candidates += 1;
        if let Some(theirs) = filter
            && !pattern.constants.is_subset(theirs)
        {
            stats.filtered_out += 1;
            return None;
        }
        let was = g.glue.replace(self.glue);
        let metas = g.metas.borrow().len();
        let trail = g.meta_trail.borrow().len();
        let found = (|| -> std::result::Result<Option<Hit>, stitchwort_core::ResourceError> {
            let _op = g.budget.operation(ATTEMPT);
            // Open the binders with fresh unknowns.
            let mut env: Vec<Value> = Vec::new();
            let mut opened: Vec<usize> = Vec::new();
            let mut hypotheses: Vec<(Term, usize)> = Vec::new();
            let mut t = def.ty.strip_loc();
            let mut whole: Option<(Term, usize)> = None;
            while let Term::Pi(_, icit, dom, cod) = t {
                if *icit == stitchwort_core::Icit::Explicit {
                    if whole.is_none() {
                        whole = Some((t.clone(), env.len()));
                    }
                    hypotheses.push(((**dom).clone(), env.len()));
                }
                let m = g.new_meta(def.span);
                opened.push(m);
                env.push(eval(g, &[], &Term::Meta(m))?);
                t = cod.strip_loc();
            }
            let conclusion = t.clone();
            let (type_size, hyps) = shape(g, id);
            // The targets, in order of preference.
            let mut targets: Vec<(Place, Term, usize)> =
                vec![(Place::Conclusion, conclusion.clone(), env.len())];
            if pattern.head == HeadKey::Pi
                && let Some((t, at)) = whole
            {
                targets.insert(0, (Place::Whole, t, at));
            }
            if mode == Mode::Rewrite {
                targets.clear();
                // An equation as stated, not one a definition (`≤` on `Nat`)
                // unfolds to: `rewrite` takes the statement.
                if let Term::Eq(_, left, right) = conclusion.strip_loc() {
                    targets.push((Place::Left, (**left).clone(), env.len()));
                    targets.push((Place::Right, (**right).clone(), env.len()));
                }
            }
            if anywhere && mode != Mode::Rewrite {
                for (h, at) in &hypotheses {
                    targets.push((Place::Hypothesis, h.clone(), *at));
                }
                let mut inside = Vec::new();
                for (whole, at) in std::iter::once((&conclusion, env.len()))
                    .chain(hypotheses.iter().map(|(h, at)| (h, *at)))
                {
                    for (sub, binders) in whole.subterms() {
                        if binders == 0
                            && !matches!(sub, Term::Loc(..))
                            && !std::ptr::eq(sub, whole)
                            && head_key(sub) == pattern.head
                            && pattern.head != HeadKey::Other
                        {
                            inside.push((Place::Inside, sub.clone(), at));
                        }
                    }
                }
                targets.extend(inside);
            }
            // Last, the parameters in another order: an exact-order match
            // above is better.
            if matches!(mode, Mode::Permute | Mode::Subset) && pattern.head == HeadKey::Pi {
                targets.push((Place::Reordered, conclusion.clone(), env.len()));
            }
            for (place, target, at) in targets {
                stats.unifications += 1;
                let inner = g.meta_trail.borrow().len();
                let mut same = if place == Place::Reordered {
                    let theirs: Vec<Value> = (hypotheses.iter())
                        .map(|(h, at)| eval(g, &env[..*at], h))
                        .collect::<std::result::Result<_, _>>()?;
                    let concl = eval(g, &env, &conclusion)?;
                    reordered(g, &pattern.value, &theirs, &concl, mode)?
                } else {
                    let target_value = eval(g, &env[..at], &target)?;
                    // A target that is one of the theorem's own variables
                    // (`(p: Prop) (h: p): p`) matches anything: no match.
                    if let Value::Neutral(Head::Meta(m), _) = force(g, target_value.clone())?
                        && opened.contains(&m)
                    {
                        stats.unifications -= 1;
                        continue;
                    }
                    crate::unify::unify_solving_arguments(g, 0, &pattern.value, &target_value)?
                };
                for group in &pattern.groups {
                    for pair in group.windows(2) {
                        if same {
                            let a = eval(g, &[], &Term::Meta(pair[0]))?;
                            let b = eval(g, &[], &Term::Meta(pair[1]))?;
                            same = crate::unify::unify_solving_arguments(g, 0, &a, &b)?;
                        }
                    }
                }
                // What an unknown now is: another unknown, or a term of
                // some size.
                let rep = |m: usize| -> std::result::Result<Now, stitchwort_core::ResourceError> {
                    let v = force(g, eval(g, &[], &Term::Meta(m))?)?;
                    Ok(match v {
                        Value::Neutral(Head::Meta(r), s) if s.is_empty() => Now::Meta(r),
                        v => Now::Size(size(&stitchwort_core::value::quote_folded(g, 0, &v)?)),
                    })
                };
                // Different named holes must stay different: `Nat.min ?a ?b
                // ≤ ?a` isn't `Nat.minLeRight` with its `m` and `n` made one.
                if same {
                    let mut seen = Vec::new();
                    for group in &pattern.groups {
                        if let Some(first) = group.first()
                            && let Now::Meta(r) = rep(*first)?
                        {
                            if seen.contains(&r) {
                                same = false;
                            }
                            seen.push(r);
                        }
                    }
                }
                if same {
                    // What the theorem's variables took: the size of each
                    // that became a term, and one for each that was made
                    // the same as another (`Ord.compare c a` for
                    // `Ord.compare ?x ?x`).
                    let mut absorbed = 0;
                    let mut classes: Vec<usize> = Vec::new();
                    for m in &opened {
                        match rep(*m)? {
                            Now::Size(n) => absorbed += n,
                            Now::Meta(r) => {
                                if classes.contains(&r) {
                                    absorbed += 1;
                                }
                                classes.push(r);
                            }
                        }
                    }
                    // The pattern's unknowns that had to become more than
                    // a variable of the theorem's.
                    let mut instantiated = 0;
                    for m in 0..pattern.metas {
                        if let Some(solution) = g.meta_solution(m)
                            && !matches!(force(g, solution)?, Value::Neutral(Head::Meta(_), s) if s.is_empty())
                        {
                            instantiated += 1;
                        }
                    }
                    return Ok(Some(Hit {
                        id,
                        place,
                        absorbed,
                        instantiated,
                        size: type_size,
                        hyps,
                    }));
                }
                crate::unify::undo_since(g, inner);
            }
            Ok(None)
        })();
        crate::unify::undo_since(g, trail);
        g.metas.borrow_mut().truncate(metas.max(pattern.metas));
        g.glue.set(was);
        match found {
            Ok(hit) => hit,
            Err(_) => {
                stats.resource_outs += 1;
                None
            }
        }
    }
}

/// Whether a function-type pattern matches a theorem whose explicit
/// parameters' types are `theirs` and whose conclusion is `concl`, with the
/// parameters in any order: the conclusions unify, and each of the
/// pattern's explicit parameters unifies with a different one of the
/// theorem's, chosen greedily left to right as Loogle's `matchHyps` does.
/// With [`Mode::Permute`] the counts must be equal; with [`Mode::Subset`]
/// the theorem may have more. The pattern's own binders are opened with
/// rigid variables.
fn reordered(
    g: &Globals,
    pattern: &Value,
    theirs: &[Value],
    concl: &Value,
    mode: Mode,
) -> std::result::Result<bool, stitchwort_core::ResourceError> {
    let mut ours: Vec<Value> = Vec::new();
    let mut v = force(g, pattern.clone())?;
    // Rigid variables, not unknowns: a hole under the arrows is an unknown
    // applied to them (`?m x y`), which unification can solve only when
    // they are variables.
    let mut level = 0;
    while let Value::Pi(_, icit, dom, closure) = v {
        if icit == stitchwort_core::Icit::Explicit {
            ours.push((*dom).clone());
        }
        v = force(g, closure.apply(g, Value::var(level))?)?;
        level += 1;
    }
    let counts_fit = match mode {
        Mode::Subset => ours.len() <= theirs.len(),
        _ => ours.len() == theirs.len(),
    };
    if ours.len() < 2 || !counts_fit || !crate::unify::unify_solving_arguments(g, level, &v, concl)?
    {
        return Ok(false);
    }
    let mut used = vec![false; theirs.len()];
    for want in &ours {
        let mut found = false;
        for (i, have) in theirs.iter().enumerate() {
            if used[i] {
                continue;
            }
            let inner = g.meta_trail.borrow().len();
            if crate::unify::unify_solving_arguments(g, level, want, have)? {
                used[i] = true;
                found = true;
                break;
            }
            crate::unify::undo_since(g, inner);
        }
        if !found {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The ranking: where it matched; then specificity (what the theorem's own
/// variables took, then what the pattern's holes had to become); then the
/// shorter name, then the name.
pub fn rank(g: &Globals, hits: &mut [Hit]) {
    hits.sort_by(|a, b| {
        let (na, nb) = (g.def(a.id).path.to_string(), g.def(b.id).path.to_string());
        (a.place, a.absorbed, a.instantiated, na.len(), &na).cmp(&(
            b.place,
            b.absorbed,
            b.instantiated,
            nb.len(),
            &nb,
        ))
    });
}
