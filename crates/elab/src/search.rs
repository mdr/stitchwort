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
use stitchwort_core::{DataId, DefId, Globals, Limits, Term};
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
    Data(DataId),
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
    /// The data types it names (draft 2 §5.6's widened filter).
    pub data: BTreeSet<usize>,
    pub head: HeadKey,
    /// How many unknowns there were once it was elaborated.
    metas: usize,
    /// The unknowns elaboration left unsolved: the pattern's holes (and
    /// their types), which a match may bind.
    free: Vec<usize>,
    /// Every hole stands for a different variable, as in a pattern made
    /// from a theorem or a goal: two made the same is an instantiation. In a
    /// written pattern, two `_`s may bind the same variable.
    distinct: bool,
}

impl Pattern {
    /// The pattern, read back folded, for messages.
    pub fn show(&self, g: &Globals) -> String {
        match stitchwort_core::value::quote_folded(g, 0, &self.value) {
            Ok(t) => stitchwort_core::pretty::term(g, &[], &t),
            Err(_) => "?".into(),
        }
    }
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
    /// With [`Mode::Rewrite`]: the left side of an equation `l = r` (or,
    /// with [`Opts::iff`], of `Iff l r`) that is the conclusion
    /// (`SearchRewrite`; draft 2 §5.3).
    Left,
    /// The right side, for rewriting from right to left.
    Right,
    Hypothesis,
    /// A call inside the type (draft 3 names it `subterm`).
    Inside,
}

/// How a pattern and a theorem matched (draft 3 §5.1, D2062), best first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Relation {
    /// The theorem instantiates to the pattern: only the theorem's
    /// variables took structure; the pattern's holes stayed distinct
    /// variables (bound to the theorem's, or left alone).
    Instance,
    /// The pattern generalises the theorem: its holes took structure from
    /// the theorem, whose variables stayed distinct variables.
    Generalisation,
    /// Both sides took structure: the two only have a common instance.
    Common,
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

/// Which theorems the constants filter lets through.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Filter {
    Off,
    /// Draft 2: the theorem's type names every definition the pattern
    /// names (and, with [`Opts::data`], every data type).
    Pattern,
    /// That, or the theorem's conclusion names something and the pattern
    /// names everything it does: a theorem that instantiates to a pasted
    /// goal brings its own constants, not the goal's (draft 3 §5.6).
    Either,
}

/// How a search matches (EXPERIMENTAL; draft 3's measurements).
#[derive(Clone, Copy, Debug)]
pub struct Opts {
    pub mode: Mode,
    /// Also hypotheses and calls inside.
    pub anywhere: bool,
    /// Draft 3's relations (D2062): try every target for the best relation,
    /// and try a match that two-way unification found crossed again one
    /// way, the pattern's holes frozen (then the theorem's variables).
    pub tiers: bool,
    /// Also targets headed by one of the theorem's variables (`p x`), which
    /// draft 2 skipped; unification solves them as higher-order patterns or
    /// by its first-order approximation.
    pub ho: bool,
    /// With [`Mode::Rewrite`], `Iff l r` conclusions too (this data type).
    pub iff: Option<DataId>,
    pub filter: Filter,
    /// The filter checks data types too.
    pub data: bool,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            mode: Mode::Plain,
            anywhere: true,
            tiers: false,
            ho: false,
            iff: None,
            filter: Filter::Pattern,
            data: false,
        }
    }
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
    pub relation: Relation,
    /// Matched a side of an `Iff`, not of an equation.
    pub iff: bool,
    /// The size of what the theorem's own variables took from the pattern:
    /// smaller is more specific (a lemma `x = x` takes a whole side).
    pub absorbed: usize,
    /// How many of the pattern's holes had to become more than one of the
    /// theorem's variables (or, in a pattern from a theorem or goal, the
    /// same as another hole): fewer is a closer
    /// fit (`List.lengthAppend` before `List.lengthSnoc` for
    /// `List.length (_ ++ _) = _`).
    pub instantiated: usize,
    /// The size of the theorem's type, in nodes (Isabelle's, Rocq's and
    /// Loogle's first ranking key).
    pub size: usize,
    /// How many explicit parameters the rest of the type doesn't mention:
    /// the premises, as against the variables (Isabelle's second key).
    pub hyps: usize,
}

/// The size of `id`'s type and the number of its premises (see [`Hit`]).
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
    /// Matches two-way unification found crossed that a one-way retry
    /// found better ([`Opts::tiers`]).
    pub upgraded: usize,
}

/// What a theorem's type names, for the filter.
#[derive(Default, Debug, Clone)]
pub struct Index {
    /// The definitions its type names (read back folded, and as written).
    pub ty: BTreeSet<DefId>,
    /// The data types its type names.
    pub data: BTreeSet<usize>,
    /// The definitions its conclusion names, as written.
    pub conclusion: BTreeSet<DefId>,
}

/// What an unknown is after a match.
enum Now {
    Meta(usize),
    /// One of the pattern's binders.
    Var,
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

/// The data types a term names.
pub fn data_types(term: &Term) -> BTreeSet<usize> {
    term.subterms()
        .filter_map(|(t, _)| match t {
            Term::Data(d, _) => Some(d.0),
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

/// The conclusion of a type: what is left under its `Pi`s.
fn conclusion_of(ty: &Term) -> &Term {
    let mut t = ty.strip_loc();
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
    }
    t
}

type Res<T> = std::result::Result<T, stitchwort_core::ResourceError>;

/// What unknown `m` is now: another unknown, one of the pattern's binders,
/// or a term of some size. A solution under the pattern's binders (`x y =>
/// ?a`) is read under them.
fn rep(g: &Globals, m: usize) -> Res<Now> {
    let mut v = force(g, eval(g, &[], &Term::Meta(m))?)?;
    let mut level = 0;
    while let Value::Lam(_, _, body) = &v {
        let next = force(g, body.apply(g, Value::var(level))?)?;
        v = next;
        level += 1;
    }
    Ok(match v {
        Value::Neutral(Head::Meta(r), s) if s.is_empty() => Now::Meta(r),
        Value::Neutral(Head::Var(..), s) if s.is_empty() && level > 0 => Now::Var,
        v => Now::Size(size(&stitchwort_core::value::quote_folded(g, level, &v)?)),
    })
}

/// After a successful unification: `None` if two different named holes
/// were made the same; otherwise what the theorem's variables (`opened`)
/// absorbed and how many of the pattern's holes (`free`) were
/// instantiated (see [`Hit`]).
fn measure(
    g: &Globals,
    pattern: &Pattern,
    opened: &[usize],
    free: &[usize],
) -> Res<Option<(usize, usize, usize)>> {
    let distinct = pattern.distinct;
    let named = |m: &usize| distinct || pattern.groups.iter().any(|group| group.contains(m));
    // Different named holes must stay different: `Nat.min ?a ?b ≤ ?a`
    // isn't `Nat.minLeRight` with its `m` and `n` made one.
    let mut seen = Vec::new();
    for group in &pattern.groups {
        if let Some(first) = group.first()
            && let Now::Meta(r) = rep(g, *first)?
        {
            if seen.contains(&r) {
                return Ok(None);
            }
            seen.push(r);
        }
    }
    // What the theorem's variables took: the size of each that became a
    // term, and one for each that was made the same as another
    // (`Ord.compare c a` for `Ord.compare ?x ?x`).
    let mut absorbed = 0;
    let mut classes: Vec<usize> = Vec::new();
    for m in opened {
        match rep(g, *m)? {
            Now::Size(n) => absorbed += n,
            Now::Var => {}
            Now::Meta(r) => {
                if classes.contains(&r) {
                    absorbed += 1;
                }
                classes.push(r);
            }
        }
    }
    // The pattern's holes that had to become more than a variable, or the
    // same as another hole.
    // Only named holes (in a pattern from a theorem or goal, every hole)
    // decide the relation: a written `_` may take any structure, as it
    // asks to (draft 3 §5.1).
    let mut instantiated = 0;
    let mut decisive = 0;
    let mut classes: Vec<usize> = Vec::new();
    for m in free {
        match rep(g, *m)? {
            Now::Size(_) => {
                instantiated += 1;
                if named(m) {
                    decisive += 1;
                }
            }
            Now::Var => {}
            Now::Meta(r) => {
                if distinct && classes.contains(&r) {
                    instantiated += 1;
                    decisive += 1;
                }
                classes.push(r);
            }
        }
    }
    Ok(Some((absorbed, instantiated, decisive)))
}

/// After the pattern is unified with a target: makes each named hole's
/// occurrences one unknown (they can be under different binders, so this
/// waits until the target has solved them).
fn same_groups(g: &Globals, pattern: &Pattern) -> Res<bool> {
    for group in &pattern.groups {
        for pair in group.windows(2) {
            let a = eval(g, &[], &Term::Meta(pair[0]))?;
            let b = eval(g, &[], &Term::Meta(pair[1]))?;
            if !crate::unify::unify_solving_arguments(g, 0, &a, &b)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

fn relation_of(absorbed: usize, instantiated: usize) -> Relation {
    if instantiated == 0 {
        Relation::Instance
    } else if absorbed == 0 {
        Relation::Generalisation
    } else {
        Relation::Common
    }
}

/// Whether the filter lets theorem `index` through for `pattern`.
pub fn passes(pattern: &Pattern, index: &Index, opts: &Opts) -> bool {
    let named = pattern.constants.is_subset(&index.ty)
        && (!opts.data || pattern.data.is_subset(&index.data));
    match opts.filter {
        Filter::Off => true,
        Filter::Pattern => named,
        Filter::Either => {
            named
                || (!index.conclusion.is_empty() && index.conclusion.is_subset(&pattern.constants))
        }
    }
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
            let free = (0..metas.len())
                .filter(|m| metas[*m].solution.is_none())
                .collect();
            Ok(Pattern {
                head: head_key(&zonked),
                constants: constants(&zonked),
                data: data_types(&zonked),
                value,
                groups,
                metas: metas.len(),
                free,
                distinct: false,
            })
        })();
        self.globals.budget.restore(saved);
        self.globals.glue.set(was);
        result
    }

    /// A pattern made from theorem `id` itself: its conclusion (or the left
    /// side of it, an equation, or with `iff` an `Iff`), with each of its
    /// variables a hole. For the self-retrieval measurements (draft 2 §6):
    /// searching with it must find `id`, and where `id` ranks measures the
    /// ranking. `None` for a conclusion that is one of the theorem's
    /// variables, or (with [`Side::Left`]) one that isn't an equation.
    pub fn theorem_pattern(
        &mut self,
        id: DefId,
        side: Side,
        iff: Option<DataId>,
    ) -> Option<Pattern> {
        self.clear_metas();
        let g = &self.globals;
        let was = g.glue.replace(self.glue);
        let made = (|| -> Res<Option<Pattern>> {
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
                (Side::Left, Term::Data(d, args)) if Some(*d) == iff && args.len() == 2 => {
                    eval(g, &env, &args[0])?
                }
                _ => return Ok(None),
            };
            self.finish_pattern(value)
        })();
        g.glue.set(was);
        made.ok().flatten()
    }

    /// A pattern from a use of theorem `lemma` in a proof: its type applied
    /// to `args` (terms under `depth` binders, each of which becomes a
    /// hole). That is the goal the use proved, with the proof's variables
    /// as holes (draft 3's proof-use benchmark). `None` if it isn't applied
    /// to all its parameters, or its conclusion is a variable.
    pub fn use_pattern(&mut self, lemma: DefId, args: &[&Term], depth: usize) -> Option<Pattern> {
        self.clear_metas();
        let g = &self.globals;
        let was = g.glue.replace(self.glue);
        let made = (|| -> Res<Option<Pattern>> {
            let _op = g.budget.operation(ATTEMPT);
            let def = g.def(lemma);
            let mut env: Vec<Value> = Vec::new();
            for _ in 0..depth {
                let m = g.new_meta(def.span);
                env.push(eval(g, &[], &Term::Meta(m))?);
            }
            let mut ty = eval(g, &[], &def.ty)?;
            for arg in args {
                let Value::Pi(_, _, _, closure) = force(g, ty)? else {
                    return Ok(None);
                };
                ty = closure.apply(g, eval(g, &env, arg)?)?;
            }
            let ty = force(g, ty)?;
            if matches!(ty, Value::Pi(..)) {
                return Ok(None);
            }
            self.finish_pattern(ty)
        })();
        g.glue.set(was);
        made.ok().flatten()
    }

    /// A pattern of `value`, whose unknowns are all holes; `None` if it is
    /// one.
    fn finish_pattern(&self, value: Value) -> Res<Option<Pattern>> {
        let g = &self.globals;
        if let Value::Neutral(Head::Meta(_), s) = force(g, value.clone())?
            && s.is_empty()
        {
            return Ok(None);
        }
        let quoted = stitchwort_core::value::quote_folded(g, 0, &value)?;
        let metas = g.metas.borrow().len();
        Ok(Some(Pattern {
            head: head_key(&quoted),
            constants: constants(&quoted),
            data: data_types(&quoted),
            value,
            groups: Vec::new(),
            metas,
            free: (0..metas)
                .filter(|m| g.meta_solution(*m).is_none())
                .collect(),
            distinct: true,
        }))
    }

    /// What `id`'s type names, read back folded as a pattern is (so a
    /// field such as `Ord.compare` is named the same way in both), and as
    /// written.
    pub fn type_index(&self, id: DefId) -> Index {
        let g = &self.globals;
        let was = g.glue.replace(self.glue);
        let found = (|| {
            let _op = g.budget.operation(ATTEMPT);
            let v = eval(g, &[], &g.def(id).ty)?;
            stitchwort_core::value::quote_folded(g, 0, &v)
        })();
        g.glue.set(was);
        let ty = &g.def(id).ty;
        let mut index = Index {
            ty: constants(ty),
            data: data_types(ty),
            conclusion: constants(conclusion_of(ty)),
        };
        if let Ok(t) = found {
            index.ty.extend(constants(&t));
            index.data.extend(data_types(&t));
        }
        index
    }

    /// Matches `pattern` against theorem (or definition) `id`'s type. With
    /// `filter` (the theorem's [`Elaborator::type_index`]), a theorem the
    /// filter ([`passes`]) doesn't let through is skipped without unifying.
    pub fn search_one(
        &self,
        pattern: &Pattern,
        id: DefId,
        opts: &Opts,
        filter: Option<&Index>,
        stats: &mut Stats,
    ) -> Option<Hit> {
        let g = &self.globals;
        let def = g.def(id);
        stats.candidates += 1;
        if let Some(theirs) = filter
            && !passes(pattern, theirs, opts)
        {
            stats.filtered_out += 1;
            return None;
        }
        let was = g.glue.replace(self.glue);
        let metas = g.metas.borrow().len();
        let trail = g.meta_trail.borrow().len();
        let frozen = g.frozen_metas.borrow().len();
        let mode = opts.mode;
        let found = (|| -> Res<Option<Hit>> {
            let _op = g.budget.operation(ATTEMPT);
            let free = &pattern.free;
            // Frozen for a one-way match the pattern's way: its holes, but
            // only the first occurrence of each named hole, so that the
            // others can still be made the same as it.
            let later: Vec<usize> = (pattern.groups.iter())
                .flat_map(|group| group.iter().skip(1).copied())
                .collect();
            let rigid: Vec<usize> = (free.iter().copied())
                .filter(|m| {
                    !later.contains(m)
                        && (pattern.distinct || pattern.groups.iter().any(|gr| gr.contains(m)))
                })
                .collect();
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
            // The targets, in order of preference, and whether each is a
            // side of an `Iff`.
            let mut targets: Vec<(Place, Term, usize, bool)> =
                vec![(Place::Conclusion, conclusion.clone(), env.len(), false)];
            if pattern.head == HeadKey::Pi
                && let Some((t, at)) = whole
            {
                targets.insert(0, (Place::Whole, t, at, false));
            }
            if mode == Mode::Rewrite {
                targets.clear();
                // An equation as stated, not one a definition (`≤` on `Nat`)
                // unfolds to: `rewrite` takes the statement.
                match conclusion.strip_loc() {
                    Term::Eq(_, left, right) => {
                        targets.push((Place::Left, (**left).clone(), env.len(), false));
                        targets.push((Place::Right, (**right).clone(), env.len(), false));
                    }
                    Term::Data(d, args) if Some(*d) == opts.iff && args.len() == 2 => {
                        targets.push((Place::Left, (*args[0]).clone(), env.len(), true));
                        targets.push((Place::Right, (*args[1]).clone(), env.len(), true));
                    }
                    _ => {}
                }
            }
            if opts.anywhere && mode != Mode::Rewrite {
                for (h, at) in &hypotheses {
                    targets.push((Place::Hypothesis, h.clone(), *at, false));
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
                            inside.push((Place::Inside, sub.clone(), at, false));
                        }
                    }
                }
                targets.extend(inside);
            }
            // Last, the parameters in another order: an exact-order match
            // above is better.
            if matches!(mode, Mode::Permute | Mode::Subset) && pattern.head == HeadKey::Pi {
                targets.push((Place::Reordered, conclusion.clone(), env.len(), false));
            }
            // Unifies the pattern with one target, leaving what it solved;
            // `None` for a target that can't be a match.
            let try_target = |place: Place, target: &Term, at: usize| -> Res<Option<bool>> {
                if place == Place::Reordered {
                    let theirs: Vec<Value> = (hypotheses.iter())
                        .map(|(h, at)| eval(g, &env[..*at], h))
                        .collect::<Res<_>>()?;
                    let concl = eval(g, &env, &conclusion)?;
                    let same = reordered(g, &pattern.value, &theirs, &concl, mode)?;
                    return Ok(Some(same && same_groups(g, pattern)?));
                }
                let target_value = eval(g, &env[..at], target)?;
                // A target that is one of the theorem's own variables
                // (`(p: Prop) (h: p): p`) matches anything: no match. Draft
                // 2 skipped one applied to arguments too (`p x`).
                if let Value::Neutral(Head::Meta(m), s) = force(g, target_value.clone())?
                    && opened.contains(&m)
                    && (s.is_empty() || !opts.ho)
                {
                    return Ok(None);
                }
                let same =
                    crate::unify::unify_solving_arguments(g, 0, &pattern.value, &target_value)?;
                Ok(Some(same && same_groups(g, pattern)?))
            };
            let mut best: Option<Hit> = None;
            for (place, target, at, iff) in targets {
                if let Some(b) = &best
                    && (!opts.tiers || b.relation == Relation::Instance)
                {
                    break;
                }
                let inner = g.meta_trail.borrow().len();
                stats.unifications += 1;
                let Some(same) = try_target(place, &target, at)? else {
                    stats.unifications -= 1;
                    continue;
                };
                let measured = if same {
                    measure(g, pattern, &opened, free)?
                } else {
                    None
                };
                crate::unify::undo_since(g, inner);
                let Some((mut absorbed, mut instantiated, decisive)) = measured else {
                    continue;
                };
                let mut relation = relation_of(absorbed, decisive);
                // Two-way unification may have found a crossed solution
                // where a one-way one exists (its first-order approximation
                // isn't most general): try again with one side frozen.
                if opts.tiers {
                    for (want, side) in [
                        (Relation::Instance, &rigid),
                        (Relation::Generalisation, &opened),
                    ] {
                        if want >= relation {
                            break;
                        }
                        g.frozen_metas.borrow_mut().extend(side.iter().copied());
                        stats.unifications += 1;
                        let tried = try_target(place, &target, at);
                        g.frozen_metas.borrow_mut().truncate(frozen);
                        let m = match tried? {
                            Some(true) => measure(g, pattern, &opened, free)?,
                            _ => None,
                        };
                        crate::unify::undo_since(g, inner);
                        if let Some((a, i, d)) = m {
                            stats.upgraded += 1;
                            relation = want.max(relation_of(a, d));
                            absorbed = a;
                            instantiated = i;
                            break;
                        }
                    }
                }
                let better = match &best {
                    None => true,
                    Some(b) => (relation, place) < (b.relation, b.place),
                };
                if better {
                    best = Some(Hit {
                        id,
                        place,
                        relation,
                        iff,
                        absorbed,
                        instantiated,
                        size: type_size,
                        hyps,
                    });
                }
            }
            Ok(best)
        })();
        g.frozen_metas.borrow_mut().truncate(frozen);
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

/// Draft 3's ranking (§5.1): the relation, where it matched, specificity
/// (what the theorem's own variables took, then what the pattern's holes
/// had to become), premises, size, then the name.
pub fn rank(g: &Globals, hits: &mut [Hit]) {
    hits.sort_by_cached_key(|h| {
        let place = match h.place {
            Place::Right => Place::Left,
            p => p,
        };
        (
            h.relation,
            place,
            h.absorbed,
            h.instantiated,
            h.hyps,
            h.size,
            g.def(h.id).path.to_string(),
        )
    });
}
