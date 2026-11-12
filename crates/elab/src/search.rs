//! Lemma search by type, stage 1 (SW-915, docs/proposals/search.md draft 3
//! §4, §8 S1a): the matching behind `stitchwort search`. Checking never uses
//! it.
//!
//! A pattern is elaborated as a closed expression whose `_`s are left as
//! unknowns, and whose named holes (`?x`, and lowercase names nothing else
//! means) are unknowns made once, outside any binder of the pattern. Each
//! candidate's binders (a theorem's, a definition's or a constructor's) are
//! opened with fresh unknowns, and the pattern is unified, folded (glued,
//! with calls compared by their arguments), with each of its targets: the
//! whole type, the conclusion, each premise, each call inside, or with
//! `--rewrite` each side of a conclusion that is an equation or an `Iff`.
//! Every attempt runs under its own step budget and is undone afterwards.
//!
//! A match is labelled with how the two sides met (D2062, D2064): an
//! `instance` (only the candidate's variables took structure), a
//! `generalisation` (the pattern's named holes took structure, the
//! candidate's variables stayed variables) or a `commonInstance` (both). A
//! match two-way unification found crossed is tried again one way, with one
//! side frozen, since that unification's solution need not be the most
//! general one (draft 3 §5.1).

use std::collections::BTreeSet;
use std::rc::Rc;

use stitchwort_core::value::{Elim, Head, Value, eval, force};
use stitchwort_core::{DataId, DefId, Ev, Icit, Limits, Term};
use stitchwort_syntax::ast::Expr;
use stitchwort_syntax::{Diagnostic, Span};

use crate::Elaborator;
use crate::check::{Ctx, infer};

type Result<T> = std::result::Result<T, Diagnostic>;
type Res<T> = std::result::Result<T, stitchwort_core::ResourceError>;

/// The limits of one match attempt: a comparison that needs more is no match
/// (and is counted, as `outOfBudget`). Run as an attempt
/// ([`stitchwort_core::budget::Budget::attempt`]): inside an operation, it
/// may go as deep as that may, and `stack` only applies outside one.
pub(crate) const ATTEMPT: Limits = Limits {
    work: 200_000,
    stack: 4 * 1024 * 1024,
    size: 100_000,
    frames: 10_000,
    native_frames: 10_000,
};

/// What a pattern's outermost layer is: the calls inside a candidate that
/// are tried as `subterm` targets have the same.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HeadKey {
    Def(DefId),
    Data(DataId),
    Eq,
    Pi,
    Other,
}

/// Which of the instance double search a pattern is (draft 3 §5.6): with
/// the interface dictionaries elaboration resolved, or with each of them a
/// hole, so that a generic lemma (`Ord.compareSelf`) is found for a pattern
/// at a concrete type (`Ord.compare (?x: Nat) ?x`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Via {
    Resolved,
    Generic,
}

impl Via {
    pub fn name(self) -> &'static str {
        match self {
            Via::Resolved => "resolved",
            Via::Generic => "generic",
        }
    }
}

/// An elaborated pattern.
pub struct Pattern {
    pub(crate) value: Value,
    /// The definitions the pattern names: in the filtered pass, a candidate
    /// must name each.
    pub constants: BTreeSet<DefId>,
    /// The data types it names (D2054): likewise.
    pub data: BTreeSet<usize>,
    pub head: HeadKey,
    /// How many unknowns there were once it was elaborated.
    pub(crate) metas: usize,
    /// Its size, in nodes: a candidate variable that took a term this
    /// large absorbed the whole pattern.
    pub(crate) size: usize,
    /// The unknowns elaboration left unsolved: the pattern's holes (and
    /// their types), which a match may bind.
    pub(crate) free: Vec<usize>,
    /// The holes that decide the relation (D2064): the named holes of a
    /// written pattern, every hole of a pattern made from a theorem or a
    /// goal. A written `_` may take any structure.
    pub(crate) decisive: Vec<usize>,
    /// Every hole stands for a different variable, as in a pattern made from
    /// a theorem or a goal: two made the same is an instantiation. In a
    /// written pattern, two `_`s may bind the same variable.
    pub(crate) distinct: bool,
    /// What the pattern is: a type, or a term of this type. A target of
    /// another type is no match, and isn't unified (unification doesn't
    /// look at types, and an unknown solved by a term of another type can
    /// make computing it take a `case` of one type to a constructor of
    /// another: SW-924).
    pub(crate) ty: Option<Ty>,
    /// Which half of the instance double search this is; `None` when the
    /// pattern resolved no dictionary.
    pub via: Option<Via>,
}

impl Pattern {
    /// The pattern, read back folded, for messages and the JSON's `query`.
    pub fn show(&self, g: &Ev) -> String {
        match stitchwort_core::value::quote_folded(g, 0, &self.value) {
            Ok(t) => stitchwort_core::pretty::term(g, &[], &t),
            Err(_) => "?".into(),
        }
    }

    /// [`Pattern::show`] with calls written as calls, so that
    /// `List.append` and `Text.append` differ (both print as `++`).
    pub fn show_calls(&self, g: &Ev) -> String {
        match stitchwort_core::value::quote_folded(g, 0, &self.value) {
            Ok(t) => stitchwort_core::pretty::term_calls(g, &[], &t),
            Err(_) => "?".into(),
        }
    }
}

/// The type of a pattern or a target, as far as search compares them.
#[derive(Clone)]
pub(crate) enum Ty {
    /// A type (its type is a sort).
    Type,
    /// A term of this type.
    Of(Value),
}

impl Ty {
    pub(crate) fn of(g: &Ev, ty: Value) -> Res<Ty> {
        Ok(match force(g, ty)? {
            Value::Sort(_) => Ty::Type,
            other => Ty::Of(other),
        })
    }
}

/// The type of `term`, a type or a call in a candidate's type whose binders
/// `env` opened with unknowns, when its head tells: a type former is a
/// type; a definition or one of the candidate's variables, applied to
/// arguments, has the type its own type gives them. `None` when it can't
/// tell.
pub(crate) fn type_of_target(
    g: &crate::unify::Unifier<'_>,
    env: &[Value],
    term: &Term,
) -> Res<Option<Ty>> {
    let (head, args) = term.spine();
    let mut ty = match head {
        Term::Pi(..) | Term::Data(..) | Term::Eq(..) | Term::Sort(..) if args.is_empty() => {
            return Ok(Some(Ty::Type));
        }
        Term::Nat(_) if args.is_empty() => match g.env.builtins().nat {
            Some(nat) => return Ok(Some(Ty::Of(Value::Data(nat, Vec::new().into())))),
            None => return Ok(None),
        },
        Term::Def(id) => g.def(*id).ty_value().clone(),
        Term::Var(_) => match force(g, eval(g, env, head)?)? {
            Value::Neutral(Head::Meta(m), s) if s.is_empty() => match g.store.meta_type(m) {
                Some((ty, 0)) => ty,
                _ => return Ok(None),
            },
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };
    for arg in args {
        let Value::Pi(_, _, _, closure) = force(g, ty)? else {
            return Ok(None);
        };
        ty = closure.apply(g, eval(g, env, arg)?)?;
    }
    Ty::of(g, ty).map(Some)
}

/// Whether a pattern of type `ours` may match a target of type `theirs`:
/// the two types unify (solving what they leave open), or both are types.
/// An unknown type, on either side, doesn't rule a match out.
fn types_agree(g: &crate::unify::Unifier<'_>, ours: Option<&Ty>, theirs: Option<&Ty>) -> Res<bool> {
    let is_type = |v: &Value| -> Res<bool> {
        Ok(matches!(
            force(g, v.clone())?,
            Value::Sort(_) | Value::Neutral(Head::Meta(_), _)
        ))
    };
    match (ours, theirs) {
        (Some(Ty::Of(a)), Some(Ty::Of(b))) => crate::unify::unify(g, 0, a, b),
        (Some(Ty::Type), Some(Ty::Of(v))) | (Some(Ty::Of(v)), Some(Ty::Type)) => is_type(v),
        _ => Ok(true),
    }
}

/// Where a pattern matched a candidate, best first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Place {
    /// The whole type after its leading implicit parameters, for a pattern
    /// that is a function type (`List ?a → List ?a`).
    Whole,
    /// The conclusions match, and each of the pattern's explicit
    /// parameters matches a different one of the candidate's, in any order,
    /// the candidate having perhaps more (Loogle's `matchHyps`, greedy;
    /// draft 2 §5.2).
    Reordered,
    Conclusion,
    /// With `--rewrite`: the left side of an equation `l = r`, or of
    /// `Iff l r`, that is the conclusion.
    Left,
    /// The right side, for rewriting from right to left.
    Right,
    /// A premise: an explicit parameter's type.
    Premise,
    /// A call inside the type, with the pattern's head.
    Subterm,
}

impl Place {
    /// The name the JSON contract (version 1) gives it.
    pub fn name(self) -> &'static str {
        match self {
            Place::Whole => "whole",
            Place::Reordered => "reordered",
            Place::Conclusion => "conclusion",
            Place::Left => "left",
            Place::Right => "right",
            Place::Premise => "premise",
            Place::Subterm => "subterm",
        }
    }
}

/// How a pattern and a candidate matched (draft 3 §5.1, D2062), best first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Relation {
    /// The candidate instantiates to the pattern: only the candidate's
    /// variables took structure; the pattern's deciding holes stayed
    /// distinct variables (bound to the candidate's, or left alone).
    Instance,
    /// The pattern generalises the candidate: its holes took structure from
    /// the candidate, whose variables stayed distinct variables.
    Generalisation,
    /// Both sides took structure: the two only have a common instance.
    Common,
}

impl Relation {
    /// The name the JSON contract (version 1) gives it.
    pub fn name(self) -> &'static str {
        match self {
            Relation::Instance => "instance",
            Relation::Generalisation => "generalisation",
            Relation::Common => "commonInstance",
        }
    }
}

/// What a search compares.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode {
    /// The whole type (for a function pattern), the conclusion, and, unless
    /// [`Opts::anywhere`] is off, the premises and the calls inside.
    Plain,
    /// [`Mode::Plain`], and for a function pattern, its parameters matched
    /// in any order by a candidate's, which may have more (the default).
    Subset,
    /// Only the two sides of a conclusion that is an equation (or, with
    /// [`Opts::iff`], an `Iff`).
    Rewrite,
}

/// How a search matches.
#[derive(Clone, Copy, Debug)]
pub struct Opts {
    pub mode: Mode,
    /// Also premises and calls inside (off for a `⊢` pattern).
    pub anywhere: bool,
    /// With [`Mode::Rewrite`], `Iff l r` conclusions too (this data type).
    pub iff: Option<DataId>,
    /// The first pass is filtered: a candidate's type must name every
    /// definition and data type the pattern names (D2054). If it finds
    /// nothing, a second pass runs without the filter (D2063).
    pub filter: bool,
    /// Past this, no more candidates are compared (`Stats::stopped`):
    /// `search --at`'s time limit covers its search too.
    pub deadline: Option<stitchwort_core::budget::Instant>,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            mode: Mode::Subset,
            anywhere: true,
            iff: None,
            filter: true,
            deadline: None,
        }
    }
}

/// Which part of a theorem [`Elaborator::theorem_pattern`] makes into a
/// pattern.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Side {
    /// The conclusion, with every variable a hole.
    Conclusion,
    /// The left side of a conclusion `l = r` (or `Iff l r`), with every
    /// variable a hole.
    Left,
}

/// A declaration search can find.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Item {
    Def(DefId),
    /// A data type's constructor.
    Ctor(DataId, usize),
    /// A conjunct of a theorem whose conclusion is a conjunction, written
    /// (`A ∧ B`) or a definition that unfolds to one (`Graph.Shortest`,
    /// SW-993): `And.left (T …)`, with `T`'s parameters.
    Part(DefId, Part),
}

/// Which conjunct (SW-993): the sides taken, outermost first.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Part {
    /// Bit `i` set: the `i`-th side taken is the right one.
    bits: u8,
    len: u8,
}

/// How deep conjunctions are taken apart: `A ∧ (B ∧ (C ∧ D))` gives every
/// conjunct.
const MAX_PART_DEPTH: u8 = 3;

impl Part {
    fn then(self, right: bool) -> Part {
        Part {
            bits: self.bits | (u8::from(right) << self.len),
            len: self.len + 1,
        }
    }

    /// The sides, outermost first: `true` for the right one.
    pub fn sides(self) -> impl Iterator<Item = bool> {
        (0..self.len).map(move |i| self.bits & (1 << i) != 0)
    }

    /// `left`, `right.left`, …: the fields taken, outermost first.
    pub fn name(self) -> String {
        let sides: Vec<&str> = self
            .sides()
            .map(|r| if r { "right" } else { "left" })
            .collect();
        sides.join(".")
    }
}

/// The conjuncts of the conclusion of `ty` (a theorem's type), each as a
/// type of its own: `ty`'s parameters, then the conjunct. The conclusion
/// is a conjunction as written, or a call (of a definition) that unfolds
/// to one; each side is taken apart in turn, to [`MAX_PART_DEPTH`], where
/// it is a conjunction as written (in the theorem, or in the definition's
/// body), not where it is a call that unfolds to one: AoC 2021 day 11's
/// `Part2Answer levels answer` is `AllFlashIn levels answer ∧ …`, and
/// `AllFlashIn`'s own first conjunct, `1 ≤ answer`, fits any `1 ≤ x` (and
/// its theorem's premise, closed by `rfl`, then computed for minutes).
pub fn conjuncts(g: &Ev, ty: &Term, and: DataId) -> Vec<(Part, Term)> {
    let mut binders: Vec<(&stitchwort_core::Name, Icit, &Term)> = Vec::new();
    let mut t = ty.strip_loc();
    while let Term::Pi(name, icit, dom, cod) = t {
        binders.push((name, *icit, dom));
        t = cod.strip_loc();
    }
    // Only a conjunction, or a call, can be one.
    let head = {
        let mut h = t;
        while let Term::App(f, _, _) = h {
            h = f.strip_loc();
        }
        h
    };
    match head {
        Term::Data(d, _) if *d == and => {}
        Term::Def(_) => {}
        _ => return Vec::new(),
    }
    let level = binders.len();
    let was = g.machine.glue.replace(true);
    let mut out = Vec::new();
    let found = (|| -> Res<()> {
        let _op = g.machine.budget.attempt(ATTEMPT);
        let env: Vec<Value> = (0..level).map(Value::var).collect();
        let concl = eval(g, &env, t)?;
        split_conjunction(g, concl, level, and, Part { bits: 0, len: 0 }, &mut out)
    })();
    g.machine.glue.set(was);
    if found.is_err() {
        return Vec::new();
    }
    (out.into_iter())
        .map(|(part, conjunct)| {
            let mut ty = conjunct;
            for (name, icit, dom) in binders.iter().rev() {
                ty = Term::Pi((*name).clone(), *icit, Rc::new((*dom).clone()), Rc::new(ty));
            }
            (part, ty)
        })
        .collect()
}

fn split_conjunction(
    g: &Ev,
    v: Value,
    level: usize,
    and: DataId,
    part: Part,
    out: &mut Vec<(Part, Term)>,
) -> Res<()> {
    if part.len >= MAX_PART_DEPTH {
        return Ok(());
    }
    // The conclusion itself is unfolded; a side only as written.
    let v = if part.len == 0 { force(g, v)? } else { v };
    let Value::Data(d, args) = v else {
        return Ok(());
    };
    if d != and || args.len() != 2 {
        return Ok(());
    }
    for (right, side) in [(false, &args[0]), (true, &args[1])] {
        let here = part.then(right);
        out.push((here, stitchwort_core::value::quote_folded(g, level, side)?));
        split_conjunction(g, side.clone(), level, and, here, out)?;
    }
    Ok(())
}

/// What kind of declaration an [`Item`] is (D2089).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    Theorem,
    Definition,
    Constructor,
}

impl Kind {
    pub fn name(self) -> &'static str {
        match self {
            Kind::Theorem => "theorem",
            Kind::Definition => "definition",
            Kind::Constructor => "constructor",
        }
    }
}

impl Item {
    /// A theorem, or a definition whose type concludes in a proposition (an
    /// interface's law, such as `Ord.flip`); a definition; a constructor.
    pub fn kind(self, g: &Ev) -> Kind {
        match self {
            Item::Def(id) if g.def(id).theorem() || concludes_in_prop(g, g.def(id).ty()) => {
                Kind::Theorem
            }
            Item::Def(_) => Kind::Definition,
            Item::Ctor(..) => Kind::Constructor,
            Item::Part(..) => Kind::Theorem,
        }
    }

    /// Whether it is a generated equation (`f.eqK`, `f.eqK.orN`), or a
    /// conjunct of one.
    pub fn generated_equation(self, g: &stitchwort_core::Ev) -> bool {
        match self {
            Item::Def(id) | Item::Part(id, _) => {
                g.def(id).theorem() && crate::equations::is_generated_name(g, g.def(id).name())
            }
            Item::Ctor(..) => false,
        }
    }

    /// The conjunct it is, for a part of a theorem.
    pub fn part(self) -> Option<Part> {
        match self {
            Item::Part(_, part) => Some(part),
            _ => None,
        }
    }

    /// Its full name: `Std.List.lengthAppend`, `Std.List.Cons`.
    /// A conjunct's is its theorem's.
    pub fn path(self, g: &stitchwort_core::Ev) -> String {
        match self {
            Item::Def(id) | Item::Part(id, _) => g.def(id).path().to_string(),
            Item::Ctor(d, c) => format!("{}.{}", g.data(d).path(), g.data(d).ctors()[c].name),
        }
    }

    /// Its name from the root of its module (`List.lengthAppend`, without
    /// the module's namespace).
    pub fn name(self, g: &Ev) -> String {
        match self {
            Item::Def(id) | Item::Part(id, _) => g.def(id).name().to_string(),
            Item::Ctor(d, c) => format!("{}.{}", g.data(d).name(), g.data(d).ctors()[c].name),
        }
    }

    /// Where it is declared (a constructor: its type's declaration).
    pub fn span(self, g: &stitchwort_core::Ev) -> Span {
        match self {
            Item::Def(id) | Item::Part(id, _) => g.def(id).span(),
            Item::Ctor(d, _) => g.data(d).span(),
        }
    }

    /// Its type: a constructor's is its type's parameters (implicit), its
    /// fields, then the type applied to the parameters and its indices.
    pub fn ty(self, g: &Ev) -> Term {
        match self {
            Item::Def(id) => g.def(id).ty().clone(),
            Item::Part(id, part) => {
                let ty = g.def(id).ty();
                let and = (0..g.env.datas().len())
                    .map(DataId)
                    .find(|d| &**g.data(*d).path() == "Std.And");
                (and.map(|and| conjuncts(g, ty, and)).unwrap_or_default())
                    .into_iter()
                    .find(|(p, _)| *p == part)
                    .map_or_else(|| ty.clone(), |(_, t)| t)
            }
            Item::Ctor(d, c) => {
                let data = g.data(d);
                let ctor = &data.ctors()[c];
                let (p, f) = (data.params().len(), ctor.fields.len());
                let mut args: Vec<Term> = (0..p).map(|i| Term::Var(p + f - 1 - i)).collect();
                args.extend(ctor.result.iter().cloned());
                let mut ty = Term::data(d, args);
                for (i, (name, field)) in ctor.fields.iter().enumerate().rev() {
                    let icit = if ctor.implicit.get(i) == Some(&true) {
                        Icit::Implicit
                    } else {
                        Icit::Explicit
                    };
                    ty = Term::Pi(name.clone(), icit, Rc::new(field.clone()), Rc::new(ty));
                }
                for (i, (name, param)) in data.params().iter().enumerate().rev() {
                    let icit = if data.auto_params().get(i) == Some(&true) {
                        Icit::Auto
                    } else {
                        Icit::Implicit
                    };
                    ty = Term::Pi(name.clone(), icit, Rc::new(param.clone()), Rc::new(ty));
                }
                ty
            }
        }
    }
}

/// Whether type `ty`, after its parameters, is an equation or a data type
/// in `Prop`.
fn concludes_in_prop(g: &Ev, ty: &Term) -> bool {
    let mut t = ty.strip_loc();
    while let Term::Pi(_, _, _, cod) = t {
        t = cod.strip_loc();
    }
    match t {
        Term::Eq(..) => true,
        Term::Data(d, _) => g.data(*d).sort() == stitchwort_core::term::Sort::Prop,
        _ => false,
    }
}

/// What a candidate's type names, for the filter.
#[derive(Default, Debug, Clone)]
pub struct Index {
    /// The definitions its type names (read back folded, and as written).
    pub ty: BTreeSet<DefId>,
    /// The data types its type names.
    pub data: BTreeSet<usize>,
}

/// A declaration to search, with its type and what the type names.
pub struct Candidate {
    pub item: Item,
    pub ty: Term,
    pub index: Index,
    /// The size of its type, in nodes (Isabelle's, Rocq's and Loogle's
    /// first ranking key).
    pub size: usize,
    /// How many explicit parameters the rest of the type doesn't mention:
    /// the premises, as against the variables (Isabelle's second key).
    pub premises: usize,
    /// A theorem whose proof is, or has, an open goal (`?`): usable as an
    /// assumption (SW-2805), but not finished.
    pub open: bool,
}

/// A candidate the pattern matched.
#[derive(Clone, Debug)]
pub struct Hit {
    pub item: Item,
    pub place: Place,
    pub relation: Relation,
    /// The target is headed by one of the candidate's own variables
    /// (`p x`): unification lets such a candidate absorb nearly any
    /// pattern, so it ranks after its relation's other matches (draft 3
    /// §6.3, as `exact?` treats its `*` key).
    pub absorbs: bool,
    /// Matched a side of an `Iff`, not of an equation.
    pub iff: bool,
    /// The size of what the candidate's own variables took from the
    /// pattern: smaller is more specific (a lemma `x = x` takes a whole
    /// side).
    pub absorbed: usize,
    /// How many of the pattern's holes had to become more than one of the
    /// candidate's variables (or, in a pattern from a theorem or goal, the
    /// same as another hole): fewer is a closer fit (`List.lengthAppend`
    /// before `List.lengthSnoc` for `List.length (_ ++ _) = _`).
    pub instantiated: usize,
    pub size: usize,
    pub premises: usize,
    /// Its candidate was [`Candidate::open`].
    pub open: bool,
    /// Which halves of the instance double search found it.
    pub via: Vec<Via>,
}

/// A hit's sort key: see [`Hit::key`].
pub type Key = (
    Relation,
    bool,
    Place,
    bool,
    bool,
    usize,
    usize,
    usize,
    usize,
    bool,
    String,
);

impl Hit {
    /// The ranking (draft 3 §5.1, S1a): the relation, then whether the
    /// candidate absorbed the pattern whole, where it matched (a left and a
    /// right side alike), a declaration before a conjunct of one (SW-993),
    /// a written theorem before a generated equation (`f.eqK`,
    /// docs/proposals/function-equations.md §3.4: a hand-written lemma is
    /// the one meant, and the equations stay found after it), specificity,
    /// premises, size, a finished theorem before an open one (so an open
    /// theorem follows the finished matches of equal fit), then the name.
    pub fn key(&self, g: &stitchwort_core::Ev) -> Key {
        let place = match self.place {
            Place::Right => Place::Left,
            p => p,
        };
        (
            self.relation,
            self.absorbs,
            place,
            self.item.part().is_some(),
            self.item.generated_equation(g),
            self.absorbed,
            self.instantiated,
            self.premises,
            self.size,
            self.open,
            match self.item.part() {
                Some(part) => format!("{} {}", self.item.path(g), part.name()),
                None => self.item.path(g),
            },
        )
    }
}

/// Orders `hits` by [`Hit::key`].
pub fn rank(g: &stitchwort_core::Ev, hits: &mut [Hit]) {
    hits.sort_by_cached_key(|h| h.key(g));
}

/// Counts of what a search did.
#[derive(Default, Debug, Clone)]
pub struct Stats {
    /// Candidates searched (after the caller's own selection).
    pub candidates: usize,
    /// Comparisons of a pattern with a candidate the filter let through.
    pub compared: usize,
    pub unifications: usize,
    /// Comparisons that ran out of their step budget: possible missed
    /// matches.
    pub out_of_budget: usize,
    /// The candidates of those comparisons, in the order compared.
    pub out_of_budget_items: Vec<Item>,
    /// [`Opts::deadline`] passed before every candidate was compared.
    pub stopped: bool,
    /// Matches two-way unification found crossed that a one-way retry
    /// found better.
    pub upgraded: usize,
    /// Comparisons that failed with an internal error (a panic), each
    /// counted as no match. Search must have none (SW-919, SW-924).
    pub internal_errors: usize,
}

/// Which pass found a search's results (D2063).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SearchTier {
    /// The constants filter was on.
    Filtered,
    /// The filtered pass found nothing, so the search ran again without it.
    Relaxed,
    /// The pattern names nothing to filter by (or the filter was off).
    Unfiltered,
}

impl SearchTier {
    pub fn name(self) -> &'static str {
        match self {
            SearchTier::Filtered => "filtered",
            SearchTier::Relaxed => "relaxed",
            SearchTier::Unfiltered => "unfiltered",
        }
    }
}

/// What [`Elaborator::search`] found.
pub struct Found {
    /// Ranked, one per candidate.
    pub hits: Vec<Hit>,
    pub tier: SearchTier,
    pub stats: Stats,
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

pub(crate) fn head_key(term: &Term) -> HeadKey {
    match term.spine().0.strip_loc() {
        Term::Def(id) => HeadKey::Def(*id),
        Term::Data(d, _) => HeadKey::Data(*d),
        Term::Eq(..) => HeadKey::Eq,
        Term::Pi(..) => HeadKey::Pi,
        _ => HeadKey::Other,
    }
}

/// The size of a term, in nodes.
pub(crate) fn size(term: &Term) -> usize {
    term.subterms()
        .filter(|(t, _)| !matches!(t, Term::Loc(..)))
        .count()
}

/// The size of type `ty` and the number of its premises (see
/// [`Candidate`]).
fn shape(ty: &Term) -> (usize, usize) {
    let mut premises = 0;
    let mut t = ty.strip_loc();
    while let Term::Pi(_, icit, _, cod) = t {
        if *icit == Icit::Explicit && !cod.mentions(0) {
            premises += 1;
        }
        t = cod.strip_loc();
    }
    (size(ty), premises)
}

/// What unknown `m` is now: another unknown, one of the pattern's binders,
/// or a term of some size. A solution under the pattern's binders (`x y =>
/// ?a`) is read under them.
fn rep(g: &Ev, m: usize) -> Res<Now> {
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
/// were made the same variable; otherwise what the candidate's variables
/// (`opened`) absorbed, how many of the pattern's holes were instantiated,
/// how many of those decide the relation, and whether one of the
/// candidate's variables took the whole pattern (see [`Hit`]).
fn measure(
    g: &Ev,
    pattern: &Pattern,
    opened: &[usize],
) -> Res<Option<(usize, usize, usize, bool)>> {
    let deciding = |m: &usize| pattern.distinct || pattern.decisive.contains(m);
    // Different named holes must stay different: `Nat.min ?a ?b ≤ ?a`
    // isn't `Nat.minLeRight` with its `m` and `n` made one.
    if !pattern.distinct {
        let mut seen = Vec::new();
        for m in &pattern.decisive {
            if let Now::Meta(r) = rep(g, *m)? {
                if seen.contains(&r) {
                    return Ok(None);
                }
                seen.push(r);
            }
        }
    }
    // What the candidate's variables took: the size of each that became a
    // term, and one for each that was made the same as another
    // (`Ord.compare c a` for `Ord.compare ?x ?x`).
    let mut absorbed = 0;
    let mut whole = false;
    let mut classes: Vec<usize> = Vec::new();
    for m in opened {
        match rep(g, *m)? {
            Now::Size(n) => {
                absorbed += n;
                whole |= n >= pattern.size;
            }
            Now::Var => {}
            Now::Meta(r) => {
                if classes.contains(&r) {
                    absorbed += 1;
                }
                classes.push(r);
            }
        }
    }
    // The pattern's holes that had to become more than a variable, or (in
    // a pattern from a theorem or goal) the same as another hole. Only the
    // deciding ones decide the relation: a written `_` may take any
    // structure, as it asks to (D2064).
    let mut instantiated = 0;
    let mut decisive = 0;
    let mut classes: Vec<usize> = Vec::new();
    for m in &pattern.free {
        match rep(g, *m)? {
            Now::Size(_) => {
                instantiated += 1;
                if deciding(m) {
                    decisive += 1;
                }
            }
            Now::Var => {}
            Now::Meta(r) => {
                if pattern.distinct && classes.contains(&r) {
                    instantiated += 1;
                    decisive += 1;
                }
                classes.push(r);
            }
        }
    }
    Ok(Some((absorbed, instantiated, decisive, whole)))
}

fn relation_of(absorbed: usize, decisive: usize) -> Relation {
    if decisive == 0 {
        Relation::Instance
    } else if absorbed == 0 {
        Relation::Generalisation
    } else {
        Relation::Common
    }
}

/// Whether the filter lets a candidate whose type names `index` through for
/// `pattern`: it names every definition and data type the pattern names.
pub fn passes(pattern: &Pattern, index: &Index) -> bool {
    pattern.constants.is_subset(&index.ty) && pattern.data.is_subset(&index.data)
}

/// Whether a candidate whose type names `index` names a definition
/// `pattern` names; for a pattern that names none, a data type it names
/// (always, for a pattern that names neither).
pub fn overlaps(pattern: &Pattern, index: &Index) -> bool {
    if !pattern.constants.is_empty() {
        // A data type in common (`List`, `Nat`) says little.
        return !pattern.constants.is_disjoint(&index.ty);
    }
    pattern.data.is_empty() || !pattern.data.is_disjoint(&index.data)
}

/// Puts things back as they were before a comparison, also when it panics
/// (so a caller that catches the panic can go on).
pub(crate) struct Restore<'g> {
    pub(crate) g: crate::unify::Unifier<'g>,
    pub(crate) metas: usize,
    pub(crate) trail: usize,
    pub(crate) frozen: usize,
    pub(crate) glue: bool,
}

impl Drop for Restore<'_> {
    fn drop(&mut self) {
        let g = &self.g;
        g.store.frozen_metas.borrow_mut().truncate(self.frozen);
        crate::unify::undo_since(g, self.trail);
        g.store.metas.borrow_mut().truncate(self.metas);
        g.machine.glue.set(self.glue);
    }
}

impl Elaborator {
    /// Elaborates a search pattern. Each name in `holes` is a named hole:
    /// one unknown, made outside the pattern's binders, so that it means
    /// the same at every binder depth (`(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤
    /// ?c`). Returns the pattern as written, and, when elaboration resolved
    /// interface dictionaries in it, the same with each of them a hole (the
    /// instance double search). An error for a pattern that doesn't
    /// elaborate, or that is a hole on its own (it would match everything).
    pub fn search_pattern(&mut self, expr: &Expr, holes: &[String]) -> Result<Vec<Pattern>> {
        self.clear_metas();
        let was = self.kernel.machine.glue.replace(self.gluing());
        let saved = self.kernel.machine.budget.start(self.options.limits);
        let result = (|| -> Result<Vec<Pattern>> {
            let span = expr.span();
            let mut cx = Ctx::new(self, span);
            let g = &self.ev();
            let mut decisive = Vec::new();
            for name in holes {
                let ty = self.metas().new_meta(span);
                let hole = self.metas().new_meta(span);
                let ty_value = eval(g, &[], &Term::Meta(ty))?;
                self.metas().set_meta_type(hole, ty_value.clone(), 0);
                cx.define(
                    Some(name),
                    name.as_str().into(),
                    ty_value,
                    Term::Meta(ty),
                    Term::Meta(hole),
                )?;
                decisive.push(hole);
            }
            let (term, mut ty) = infer(&mut cx, expr)?;
            // A pattern is a closed pattern, as a `rewrite` rule is
            // (invariant 7, D2087): its own waiting checks are settled,
            // defaults included, before it is searched for, so `_ + 0 = _`
            // is on `Nat` (its `0` waited, K4) and not on an unknown type.
            let term = if crate::Elaborator::settle_pattern(&cx)? {
                ty = cx.eval(&cx.quote_folded(&ty)?)?;
                self.zonk_keeping(&term, 0, &|_| true)?
            } else {
                term
            };
            // What still waits after settling is a choice the pattern
            // doesn't make: this reading doesn't elaborate.
            if let Some(stuck) = self.pattern_stuck()? {
                return Err(stuck);
            }
            let value = cx.eval(&term)?;
            let ty = Ty::of(g, ty).ok();
            if let Value::Neutral(Head::Meta(_), s) = force(g, value.clone())?
                && s.is_empty()
            {
                // Written as more than a hole, it computed to one (SW-942):
                // `List.drop _ 0` is its list argument.
                if !matches!(term.strip_loc(), Term::Meta(_) | Term::Var(_)) {
                    return Err(Diagnostic::error(
                        "E-SEARCH-PATTERN",
                        "this pattern computes to a hole on its own, which would match everything",
                    )
                    .with_label(span, "this is what one of its holes is, once computed")
                    .with_note(
                        "the library's definitions compute on what the pattern gives them: \
                         `List.drop _ 0` is the list `_`, so it is a hole. Search for what \
                         it is about instead (`List.drop _ _ = _`), or give the hole \
                         some structure",
                    ));
                }
                return Err(Diagnostic::error(
                    "E-SEARCH-PATTERN",
                    "this pattern is a hole on its own, which would match everything",
                )
                .with_label(span, "a hole, with nothing around it")
                .with_note(
                    "give it some structure: a name it mentions (`List.length _ = _`), or a \
                     type (`List _ → Nat`)",
                ));
            }
            let make = |value: Value, via: Option<Via>| -> Pattern {
                let zonked = stitchwort_core::value::quote_folded(g, 0, &value)
                    .unwrap_or_else(|_| term.clone());
                let metas = self.metas().metas.borrow().len();
                Pattern {
                    head: head_key(&zonked),
                    constants: constants(&zonked),
                    data: data_types(&zonked),
                    size: size(&zonked),
                    value,
                    metas,
                    free: (0..metas)
                        .filter(|m| g.meta_solution(*m).is_none())
                        .collect(),
                    decisive: decisive.clone(),
                    distinct: false,
                    ty: ty.clone(),
                    via,
                }
            };
            // The instance double search: each dictionary elaboration
            // resolved, made a hole.
            let made = std::cell::Cell::new(false);
            let level = cx.level();
            let generic = self
                .zonk_keeping(&term, level, &|_| true)
                .ok()
                .and_then(|zonked| {
                    crate::lift::replace_with(
                        g,
                        &zonked,
                        level,
                        &|l| Ok(Term::Var(level - 1 - l)),
                        &|t, _| match t {
                            Term::App(f, arg, Icit::Auto) if is_dictionary(g, arg) => {
                                made.set(true);
                                let hole = Term::Meta(self.metas().new_meta(span));
                                Some(Term::App(f.clone(), Rc::new(hole), Icit::Auto))
                            }
                            // A concrete instance the elaborator unfolded
                            // to its field (`Nat.decEq` for `Nat.instDecEq`):
                            // the generic reading names the interface's
                            // method with the dictionary a hole, so a lemma
                            // that takes its dictionary as an argument
                            // (`DecEq.refl`) can match too.
                            Term::Def(id) => {
                                let (method, dict_ty) = self.instance_method_for(*id)?;
                                let Term::Data(_, args) = dict_ty.strip_loc() else {
                                    return None;
                                };
                                let [ty_arg] = args.as_slice() else {
                                    return None;
                                };
                                let hole = self.metas().new_meta(span);
                                self.metas()
                                    .set_meta_type(hole, eval(g, &[], &dict_ty).ok()?, 0);
                                made.set(true);
                                let call = Term::app_icit(
                                    Term::Def(method),
                                    (**ty_arg).clone(),
                                    Icit::Implicit,
                                );
                                Some(Term::app_icit(call, Term::Meta(hole), Icit::Auto))
                            }
                            _ => None,
                        },
                    )
                    .ok()
                });
            match generic {
                Some(generic_term) if made.get() => {
                    let generic = cx.eval(&generic_term)?;
                    let resolved = make(value, Some(Via::Resolved));
                    let mut generic = make(generic, Some(Via::Generic));
                    // A generic lemma names the interface, not the type it
                    // was resolved at (`Ord.compareSelf` doesn't name
                    // `Nat`): the filter asks only for the data types the
                    // pattern names outside implicit arguments and
                    // ascriptions.
                    generic.data = explicit_data(&generic_term);
                    Ok(vec![resolved, generic])
                }
                _ => Ok(vec![make(value, None)]),
            }
        })();
        self.kernel.machine.budget.restore(saved);
        self.kernel.machine.glue.set(was);
        result
    }

    /// If `field` is the implementation a parameterless global instance
    /// supplies (`Nat.decEq` is `Nat.instDecEq`'s `decide`), the interface
    /// method that projects it (`DecEq.decide`) and the dictionary's type
    /// (`DecEq Nat`). A pattern that names such a function can be searched
    /// again with the dictionary a hole, as one that names the method is.
    fn instance_method_for(&self, field: DefId) -> Option<(DefId, Term)> {
        let g = &self.ev();
        for (key, info) in self.tables.instances.iter() {
            if !info.valid || !info.params.is_empty() {
                continue;
            }
            let interface = key.0;
            let Some(known) = self.tables.interfaces.get(&interface) else {
                continue;
            };
            let Ok(value) = eval(g, &[], &Term::Def(info.def)) else {
                continue;
            };
            let Ok(value) = force(g, value) else {
                continue;
            };
            let value = stitchwort_core::value::unfold_folded(g, &value)
                .ok()
                .flatten()
                .unwrap_or(value);
            let Value::Ctor(_, _, fields) = value else {
                continue;
            };
            for (i, value) in fields.iter().enumerate() {
                if let Value::Neutral(Head::Def(id), _) = force(g, value.clone()).ok()?
                    && id == field
                {
                    let method = *known.methods.get(i)?;
                    let mut ty = g.def(info.def).ty().strip_loc();
                    while let Term::Pi(_, _, _, cod) = ty {
                        ty = cod.strip_loc();
                    }
                    return Some((method, ty.clone()));
                }
            }
        }
        None
    }

    /// A pattern made from theorem `id` itself: its conclusion (or the left
    /// side of it, an equation, or with `iff` an `Iff`), with each of its
    /// variables a hole. For the self-retrieval benchmark (draft 2 §6):
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
        let g = &self.unifier();
        let was = g.machine.glue.replace(self.gluing());
        let made = (|| -> Res<Option<Pattern>> {
            let _op = g.machine.budget.attempt(ATTEMPT);
            let def = g.def(id);
            let mut env: Vec<Value> = Vec::new();
            let mut t = def.ty().strip_loc();
            while let Term::Pi(_, _, dom, cod) = t {
                let m = self.metas().new_meta(def.span());
                self.metas().set_meta_type(m, eval(g, &env, dom)?, 0);
                env.push(eval(g, &[], &Term::Meta(m))?);
                t = cod.strip_loc();
            }
            let (value, ty) = match (side, t) {
                (Side::Conclusion, _) => (eval(g, &env, t)?, Some(Ty::Type)),
                (Side::Left, Term::Eq(ty, left, _)) => {
                    let ty = match ty {
                        Some(ty) => Some(Ty::of(g, eval(g, &env, ty)?)?),
                        None => type_of_target(g, &env, left)?,
                    };
                    (eval(g, &env, left)?, ty)
                }
                (Side::Left, Term::Data(d, args)) if Some(*d) == iff && args.len() == 2 => {
                    (eval(g, &env, &args[0])?, Some(Ty::Type))
                }
                _ => return Ok(None),
            };
            self.finish_pattern(value, ty)
        })();
        g.machine.glue.set(was);
        made.ok().flatten()
    }

    /// A pattern from a use of theorem `lemma` in a proof: its type applied
    /// to `args` (terms under `depth` binders, each of which becomes a
    /// hole). That is the goal the use proved, with the proof's variables
    /// as holes (draft 3's proof-use benchmark). `None` if it isn't applied
    /// to all its parameters, or its conclusion is a variable.
    pub fn use_pattern(&mut self, lemma: DefId, args: &[&Term], depth: usize) -> Option<Pattern> {
        self.clear_metas();
        let g = &self.unifier();
        let was = g.machine.glue.replace(self.gluing());
        let made = (|| -> Res<Option<Pattern>> {
            let _op = g.machine.budget.attempt(ATTEMPT);
            let def = g.def(lemma);
            let mut env: Vec<Value> = Vec::new();
            for _ in 0..depth {
                let m = self.metas().new_meta(def.span());
                env.push(eval(g, &[], &Term::Meta(m))?);
            }
            // The proof's variables have no recorded type, so unification
            // can't tell an ill-typed pairing from a good one (SW-919's
            // guard needs the types), and an unknown solved with a term of
            // another type can make computing it panic. Each variable given
            // as an argument, to the lemma or to a call in its arguments,
            // gets the type that parameter has.
            let holes: Vec<usize> = (env.iter())
                .filter_map(|v| match v {
                    Value::Neutral(Head::Meta(m), _) => Some(*m),
                    _ => None,
                })
                .collect();
            type_holes(g, &env, &holes, def.span(), def.ty_value().clone(), args)?;
            for arg in args {
                for (sub, binders) in arg.subterms() {
                    if binders == 0
                        && let (Term::Def(id), sub_args) = sub.spine()
                        && !sub_args.is_empty()
                    {
                        type_holes(
                            g,
                            &env,
                            &holes,
                            def.span(),
                            g.def(*id).ty_value().clone(),
                            &sub_args,
                        )?;
                    }
                }
            }
            let mut ty = eval(g, &[], def.ty())?;
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
            self.finish_pattern(ty, Some(Ty::Type))
        })();
        g.machine.glue.set(was);
        made.ok().flatten()
    }

    /// A pattern of `value`, whose unknowns are all holes, each a different
    /// variable; `None` if it is one.
    fn finish_pattern(&self, value: Value, ty: Option<Ty>) -> Res<Option<Pattern>> {
        let g = &self.ev();
        if let Value::Neutral(Head::Meta(_), s) = force(g, value.clone())?
            && s.is_empty()
        {
            return Ok(None);
        }
        let quoted = stitchwort_core::value::quote_folded(g, 0, &value)?;
        let metas = self.metas().metas.borrow().len();
        Ok(Some(Pattern {
            head: head_key(&quoted),
            constants: constants(&quoted),
            data: data_types(&quoted),
            size: size(&quoted),
            value,
            metas,
            free: (0..metas)
                .filter(|m| g.meta_solution(*m).is_none())
                .collect(),
            decisive: Vec::new(),
            distinct: true,
            ty,
            via: None,
        }))
    }

    /// The candidates: every declaration `keep` keeps (given its full
    /// name), definitions, theorems and constructors, but those not checked
    /// in full (unfinished, or failed). A theorem with an open goal of its
    /// own is kept, marked [`Candidate::open`]: its statement is as good as
    /// any, and what uses it is checked as if it were an assumption.
    pub fn search_candidates(&self, keep: &dyn Fn(Item, &str) -> bool) -> Vec<Candidate> {
        let g = &self.ev();
        let open_owners: BTreeSet<String> = (g.env.defs().iter())
            .filter_map(|d| d.assumption())
            // A declaration with an error isn't offered: its proof (or body)
            // is wrong, unlike an open goal's, which is only missing.
            .filter(|a| !a.is_error())
            .map(|a| a.owner.to_string())
            .collect();
        let is_open = |id: DefId| {
            !open_owners.is_empty()
                && g.def(id).assumption().is_none()
                && g.def(id).theorem()
                && open_owners.contains(&**g.def(id).path())
        };
        let defs = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| !self.is_unfinished(*id) || is_open(*id))
            .map(Item::Def);
        let ctors = (0..g.env.datas().len()).flat_map(|d| {
            (0..g.data(DataId(d)).ctors().len()).map(move |c| Item::Ctor(DataId(d), c))
        });
        let and = (0..g.env.datas().len())
            .map(DataId)
            .find(|d| &**g.data(*d).path() == "Std.And");
        let candidate = |item: Item, ty: Term, open: bool| {
            let (size, premises) = shape(&ty);
            Candidate {
                open,
                item,
                index: self.type_index(&ty),
                ty,
                size,
                premises,
            }
        };
        let mut out = Vec::new();
        for item in defs.chain(ctors) {
            if !keep(item, &item.path(g)) {
                continue;
            }
            let ty = item.ty(g);
            // A theorem's conjuncts (SW-993), after it.
            let parts = match (item, and) {
                (Item::Def(id), Some(and)) if item.kind(g) == Kind::Theorem => {
                    conjuncts(g, &ty, and)
                        .into_iter()
                        .map(|(part, t)| (Item::Part(id, part), t))
                        .collect()
                }
                _ => Vec::new(),
            };
            let open = matches!(item, Item::Def(id) if is_open(id));
            out.push(candidate(item, ty, open));
            for (part, t) in parts {
                out.push(candidate(part, t, open));
            }
        }
        out
    }

    /// What type `ty` names, read back folded as a pattern is (so a field
    /// such as `Ord.compare` is named the same way in both), and as
    /// written.
    pub fn type_index(&self, ty: &Term) -> Index {
        let g = &self.ev();
        let was = g.machine.glue.replace(self.gluing());
        let found = (|| {
            let _op = g.machine.budget.attempt(ATTEMPT);
            let v = eval(g, &[], ty)?;
            stitchwort_core::value::quote_folded(g, 0, &v)
        })();
        g.machine.glue.set(was);
        let mut index = Index {
            ty: constants(ty),
            data: data_types(ty),
        };
        if let Ok(t) = found {
            index.ty.extend(constants(&t));
            index.data.extend(data_types(&t));
        }
        index
    }

    /// Searches `candidates` (those `keep` keeps) for `patterns`, the halves
    /// of one query: a candidate found by both appears once, at its better
    /// rank, with both in `via`. The first pass is filtered (unless
    /// [`Opts::filter`] is off, or the patterns name nothing); if it finds
    /// nothing, a second runs unfiltered (D2063). An internal error in one
    /// comparison is counted and taken as no match.
    pub fn search(
        &self,
        patterns: &[Pattern],
        candidates: &[Candidate],
        opts: &Opts,
        keep: &dyn Fn(&Candidate) -> bool,
    ) -> Found {
        let g = &self.ev();
        let names_something = patterns
            .iter()
            .any(|p| !p.constants.is_empty() || !p.data.is_empty());
        let mut tier = if opts.filter && names_something {
            SearchTier::Filtered
        } else {
            SearchTier::Unfiltered
        };
        let mut stats = Stats::default();
        loop {
            let mut best: Vec<Option<Hit>> = vec![None; candidates.len()];
            stats.candidates = 0;
            for (i, candidate) in candidates.iter().enumerate() {
                if !keep(candidate) {
                    continue;
                }
                if opts
                    .deadline
                    .is_some_and(|d| stitchwort_core::budget::Instant::now() >= d)
                {
                    stats.stopped = true;
                    break;
                }
                stats.candidates += 1;
                for pattern in patterns {
                    let filtered = tier == SearchTier::Filtered;
                    // In the relaxed pass, a pattern with premises (a
                    // function type) still asks for a definition or data
                    // type in common: matched through their higher-order
                    // variables, `Exists.map` and `Quot.funext` fit nearly
                    // any (SW-935). A conclusion pattern, as a goal's is,
                    // keeps the whole pass: the lemma used in a proof often
                    // names nothing the goal does (the proof-use benchmark
                    // loses 7 points of recall@10 with the rule).
                    if tier == SearchTier::Relaxed
                        && pattern.head == HeadKey::Pi
                        && !overlaps(pattern, &candidate.index)
                    {
                        continue;
                    }
                    let attempt = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        self.search_one(pattern, candidate, opts, filtered, &mut stats)
                    }));
                    let hit = attempt.unwrap_or_else(|_| {
                        stats.internal_errors += 1;
                        None
                    });
                    let Some(mut hit) = hit else { continue };
                    // Nor, for such a pattern, one whose own variable took
                    // the whole pattern (`List.foldLeft`'s result `b`).
                    if tier == SearchTier::Relaxed && pattern.head == HeadKey::Pi && hit.absorbs {
                        continue;
                    }
                    hit.via = pattern.via.into_iter().collect();
                    best[i] = Some(match best[i].take() {
                        None => hit,
                        Some(mut other) => {
                            let mut via: Vec<Via> =
                                other.via.iter().chain(&hit.via).copied().collect();
                            via.sort();
                            via.dedup();
                            if hit.key(g) < other.key(g) {
                                other = hit;
                            }
                            other.via = via;
                            other
                        }
                    });
                }
            }
            let mut hits: Vec<Hit> = best.into_iter().flatten().collect();
            if hits.is_empty() && tier == SearchTier::Filtered {
                tier = SearchTier::Relaxed;
                continue;
            }
            rank(g, &mut hits);
            return Found { hits, tier, stats };
        }
    }

    /// Matches `pattern` against `candidate`'s type: its best target (best
    /// relation, then best place). With `filtered`, a candidate the filter
    /// ([`passes`]) doesn't let through is skipped without unifying.
    pub fn search_one(
        &self,
        pattern: &Pattern,
        candidate: &Candidate,
        opts: &Opts,
        filtered: bool,
        stats: &mut Stats,
    ) -> Option<Hit> {
        if filtered && !passes(pattern, &candidate.index) {
            return None;
        }
        stats.compared += 1;
        let g = &self.unifier();
        let frozen = g.store.frozen_metas.borrow().len();
        let _restore = Restore {
            g: *g,
            metas: g.store.metas.borrow().len().max(pattern.metas),
            trail: g.store.meta_trail.borrow().len(),
            frozen,
            glue: g.machine.glue.replace(self.gluing()),
        };
        let span = candidate.item.span(g);
        let mode = opts.mode;
        let found = (|| -> Res<Option<Hit>> {
            let _op = g.machine.budget.attempt(ATTEMPT);
            // Frozen for a one-way match the pattern's way.
            let rigid: &[usize] = if pattern.distinct {
                &pattern.free
            } else {
                &pattern.decisive
            };
            // Open the binders with fresh unknowns.
            let mut env: Vec<Value> = Vec::new();
            let mut opened: Vec<usize> = Vec::new();
            let mut premises: Vec<(Term, usize)> = Vec::new();
            let mut t = candidate.ty.strip_loc();
            let mut whole: Option<(Term, usize)> = None;
            // A pattern that starts with an `auto` or implicit binder
            // (`[auto eq: DecEq ?a] → …`) is matched from each such binder
            // of the candidate, skipping the ones before it.
            let opens_hidden = matches!(
                force(g, pattern.value.clone())?,
                Value::Pi(_, icit, ..) if icit != Icit::Explicit
            );
            let mut hidden: Vec<(Term, usize)> = Vec::new();
            while let Term::Pi(_, icit, dom, cod) = t {
                if opens_hidden && *icit != Icit::Explicit {
                    hidden.push((t.clone(), env.len()));
                }
                if *icit == Icit::Explicit {
                    if whole.is_none() {
                        whole = Some((t.clone(), env.len()));
                    }
                    premises.push(((**dom).clone(), env.len()));
                }
                let m = g.store.new_meta(span);
                g.store.set_meta_type(m, eval(g, &env, dom)?, 0);
                opened.push(m);
                env.push(eval(g, &[], &Term::Meta(m))?);
                t = cod.strip_loc();
            }
            let conclusion = t.clone();
            // The targets, in order of preference, and whether each is a
            // side of an `Iff`.
            let mut targets: Vec<(Place, Term, usize, bool)> =
                vec![(Place::Conclusion, conclusion.clone(), env.len(), false)];
            if pattern.head == HeadKey::Pi
                && let Some((t, at)) = whole
            {
                targets.insert(0, (Place::Whole, t, at, false));
            }
            if pattern.head == HeadKey::Pi {
                for (i, (t, at)) in hidden.into_iter().enumerate() {
                    targets.insert(i, (Place::Whole, t, at, false));
                }
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
                for (h, at) in &premises {
                    targets.push((Place::Premise, h.clone(), *at, false));
                }
                let mut inside = Vec::new();
                for (whole, at) in std::iter::once((&conclusion, env.len()))
                    .chain(premises.iter().map(|(h, at)| (h, *at)))
                {
                    for (sub, binders) in whole.subterms() {
                        if binders == 0
                            && !matches!(sub, Term::Loc(..))
                            && !std::ptr::eq(sub, whole)
                            && head_key(sub) == pattern.head
                            && pattern.head != HeadKey::Other
                        {
                            inside.push((Place::Subterm, sub.clone(), at, false));
                        }
                    }
                }
                targets.extend(inside);
            }
            // Last, the parameters in another order: an exact-order match
            // above is better.
            if mode == Mode::Subset && pattern.head == HeadKey::Pi {
                targets.push((Place::Reordered, conclusion.clone(), env.len(), false));
            }
            // Unifies the pattern with one target, leaving what it solved;
            // `None` for a target that can't be a match, else whether it
            // matched and whether the target is headed by one of the
            // candidate's variables.
            let try_target =
                |place: Place, target: &Term, at: usize| -> Res<Option<(bool, bool)>> {
                    if place == Place::Reordered {
                        let theirs: Vec<Value> = (premises.iter())
                            .map(|(h, at)| eval(g, &env[..*at], h))
                            .collect::<Res<_>>()?;
                        let concl = eval(g, &env, &conclusion)?;
                        let same = reordered(g, &pattern.value, &theirs, &concl)?;
                        return Ok(Some((same, false)));
                    }
                    // Of another type, it isn't a match, and unifying could
                    // solve an unknown with a term of the wrong type
                    // (SW-924).
                    let theirs = match place {
                        Place::Left | Place::Right => match conclusion.strip_loc() {
                            Term::Eq(Some(ty), ..) => Some(Ty::of(&g.ev, eval(g, &env, ty)?)?),
                            Term::Eq(None, ..) => type_of_target(g, &env[..at], target)?,
                            _ => Some(Ty::Type),
                        },
                        Place::Whole | Place::Conclusion | Place::Premise => Some(Ty::Type),
                        _ => type_of_target(g, &env[..at], target)?,
                    };
                    if !types_agree(g, pattern.ty.as_ref(), theirs.as_ref())? {
                        return Ok(Some((false, false)));
                    }
                    let target_value = eval(g, &env[..at], target)?;
                    // A target that is one of the candidate's own variables
                    // (`(p: Prop) (h: p): p`) matches anything: no match.
                    // One applied to arguments (`p x`) is tried (D2067), and
                    // ranks after its relation's other matches.
                    let absorbs = match force(g, target_value.clone())? {
                        Value::Neutral(Head::Meta(m), s) if opened.contains(&m) => {
                            if s.is_empty() {
                                return Ok(None);
                            }
                            true
                        }
                        _ => false,
                    };
                    let same =
                        crate::unify::unify_solving_arguments(g, 0, &pattern.value, &target_value)?;
                    Ok(Some((same, absorbs)))
                };
            let mut best: Option<Hit> = None;
            for (place, target, at, iff) in targets {
                if let Some(b) = &best
                    && b.relation == Relation::Instance
                    && !b.absorbs
                {
                    break;
                }
                let inner = g.store.meta_trail.borrow().len();
                stats.unifications += 1;
                let Some((same, mut absorbs)) = try_target(place, &target, at)? else {
                    stats.unifications -= 1;
                    continue;
                };
                let measured = if same {
                    measure(&g.ev, pattern, &opened)?
                } else {
                    None
                };
                crate::unify::undo_since(g, inner);
                let Some((mut absorbed, mut instantiated, decisive, whole)) = measured else {
                    continue;
                };
                // A variable of the candidate took the whole pattern (`a`
                // in a conclusion `{row} a`): as good as no match, so it
                // ranks after the relation's other matches.
                absorbs |= whole;
                let mut relation = relation_of(absorbed, decisive);
                // Two-way unification may have found a crossed solution
                // where a one-way one exists (its first-order approximation
                // isn't most general): try again with one side frozen.
                for (want, side) in [
                    (Relation::Instance, rigid),
                    (Relation::Generalisation, &opened[..]),
                ] {
                    if want >= relation {
                        break;
                    }
                    g.store
                        .frozen_metas
                        .borrow_mut()
                        .extend(side.iter().copied());
                    stats.unifications += 1;
                    let tried = try_target(place, &target, at);
                    g.store.frozen_metas.borrow_mut().truncate(frozen);
                    let m = match tried? {
                        Some((true, _)) => measure(&g.ev, pattern, &opened)?,
                        _ => None,
                    };
                    crate::unify::undo_since(g, inner);
                    if let Some((a, i, d, _)) = m {
                        stats.upgraded += 1;
                        relation = want.max(relation_of(a, d));
                        absorbed = a;
                        instantiated = i;
                        break;
                    }
                }
                let better = match &best {
                    None => true,
                    Some(b) => (relation, absorbs, place) < (b.relation, b.absorbs, b.place),
                };
                if better {
                    best = Some(Hit {
                        item: candidate.item,
                        place,
                        relation,
                        absorbs,
                        iff,
                        absorbed,
                        instantiated,
                        size: candidate.size,
                        premises: candidate.premises,
                        open: candidate.open,
                        via: Vec::new(),
                    });
                }
            }
            Ok(best)
        })();
        match found {
            Ok(hit) => hit,
            Err(why) => {
                if std::env::var_os("STITCHWORT_SEARCH_DEBUG").is_some() {
                    eprintln!("search: {} ran out ({why:?})", candidate.item.path(g));
                }
                stats.out_of_budget += 1;
                stats.out_of_budget_items.push(candidate.item);
                None
            }
        }
    }
}

/// For a call of something of type `ty` to `args` (terms in `env`): each
/// argument that is one of `holes` with no type yet gets its parameter's.
/// An argument that is a hole applied to terms (`p x`, a proof's predicate)
/// makes the hole a function of that many arguments, of unknown domains,
/// into the parameter's type: a candidate's term of another form (`Some y`)
/// is then no solution for it, which computing the call would otherwise
/// find out by applying a constructor.
fn type_holes(
    g: &crate::unify::Unifier<'_>,
    env: &[Value],
    holes: &[usize],
    span: Span,
    ty: Value,
    args: &[&Term],
) -> Res<()> {
    let mut ty = ty;
    for arg in args {
        let Value::Pi(_, _, dom, closure) = force(g, ty)? else {
            return Ok(());
        };
        let value = eval(g, env, arg)?;
        if let Value::Neutral(Head::Meta(m), s) = force(g, value.clone())?
            && holes.contains(&m)
            && g.store.meta_type(m).is_none()
        {
            if s.is_empty() {
                g.store.set_meta_type(m, (*dom).clone(), 0);
            } else if s.iter().all(|e| matches!(e, Elim::App(_, Icit::Explicit))) {
                let mut function = stitchwort_core::value::quote_folded(g, 0, &dom)?;
                for _ in 0..s.len() {
                    let domain = g.store.new_meta(span);
                    function = Term::Pi(
                        "_".into(),
                        Icit::Explicit,
                        Rc::new(Term::Meta(domain)),
                        Rc::new(function),
                    );
                }
                g.store.set_meta_type(m, eval(g, &[], &function)?, 0);
            }
        }
        ty = closure.apply(g, value)?;
    }
    Ok(())
}

/// The data types `term` names outside implicit and `auto` arguments and
/// ascriptions' types.
fn explicit_data(term: &Term) -> BTreeSet<usize> {
    let mut found = BTreeSet::new();
    let mut work = vec![term];
    while let Some(t) = work.pop() {
        match t {
            Term::App(f, arg, icit) => {
                work.push(f);
                if *icit == Icit::Explicit {
                    work.push(arg);
                }
            }
            Term::Data(d, args) => {
                found.insert(d.0);
                work.extend(args.iter().map(|a| &**a));
            }
            Term::Loc(_, t) => work.push(t),
            Term::Pi(_, _, a, b) => {
                work.push(a);
                work.push(b);
            }
            // An ascription's type says what a hole is, as an implicit
            // argument would.
            Term::Ann(a, _) => work.push(a),
            Term::Eq(ty, a, b) => {
                work.extend(ty.iter().map(|t| &**t));
                work.push(a);
                work.push(b);
            }
            Term::Lam(_, _, b) => work.push(b),
            Term::Ctor(_, _, args) => work.extend(args.iter().map(|a| &**a)),
            _ => {}
        }
    }
    found
}

/// Whether `arg`, an `auto` argument, is an interface dictionary that
/// elaboration resolved: an instance (or a dictionary definition) applied
/// to arguments.
fn is_dictionary(g: &Ev, arg: &Term) -> bool {
    match arg.spine().0.strip_loc() {
        Term::Def(id) => {
            let def = g.def(*id);
            def.instance() || def.fold()
        }
        _ => false,
    }
}

/// Whether a function-type pattern matches a candidate whose explicit
/// parameters' types are `theirs` and whose conclusion is `concl`, with the
/// parameters in any order: the conclusions unify, and each of the
/// pattern's explicit parameters unifies with a different one of the
/// candidate's, chosen greedily left to right as Loogle's `matchHyps` does;
/// the candidate may have more. The pattern's own binders are opened with
/// rigid variables.
///
/// One parameter is enough (SW-993): `Ord.compare ?x ?y = Equal → ?x = ?y`
/// is `Ord.equal`'s statement after its explicit `x` and `y`, which the
/// whole-type match, starting at the first explicit parameter, doesn't
/// skip.
fn reordered(
    g: &crate::unify::Unifier<'_>,
    pattern: &Value,
    theirs: &[Value],
    concl: &Value,
) -> Res<bool> {
    let mut ours: Vec<Value> = Vec::new();
    let mut v = force(g, pattern.clone())?;
    // Rigid variables, not unknowns: a hole under the arrows is an unknown
    // applied to them (`?m x y`), which unification can solve only when
    // they are variables.
    let mut level = 0;
    while let Value::Pi(_, icit, dom, closure) = v {
        if icit == Icit::Explicit {
            ours.push((*dom).clone());
        }
        v = force(g, closure.apply(g, Value::var(level))?)?;
        level += 1;
    }
    if ours.is_empty()
        || ours.len() > theirs.len()
        || !crate::unify::unify_solving_arguments(g, level, &v, concl)?
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
            let inner = g.store.meta_trail.borrow().len();
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
