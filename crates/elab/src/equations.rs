//! Generated equations for each arm (docs/proposals/function-equations.md,
//! stage 1a; D2173–D2180, D2183–D2187): for a definition with arms,
//!
//! ```text
//! ex.eq3 (depth: Nat) (left: Num) (right: Num)
//!     (notArm2: (a: Nat) → (b: Nat) → left = Reg a → right = Reg b → Void):
//!     ex depth (Pr left right) = ex (depth + 1) left + ex (depth + 1) right
//! ```
//!
//! one theorem `f.eqK` per arm `K` (`f.eqK.orN` per alternative of an arm
//! with an or-pattern), whose left side is the arm's patterns and whose
//! right side is the arm's body as elaborated, `let`s substituted. Each
//! earlier arm that overlaps it becomes a hypothesis (§3.2): `notArmJ:
//! (vars) → x = p → … → Void` in Lean's form, `n ≠ k` for a number, and the
//! earlier arms' characters on one variable merged into `notListed: c ∉
//! ['k', 'j']`. A `:=` body that is a `match` on the header's parameters
//! counts as arms (D2187); local definitions get theirs (`f.go.eq1`), except
//! in a `decreasing` definition; an effect-polymorphic definition's are at
//! the empty row (its implicit rows `Empty`, divergences `Total`).
//!
//! **How a statement is found.** The arm's left side and the variables it
//! binds come from compiling the arm on its own, as the definition's own
//! `match` would, with a probe for its body ([`PROBE`]): the context there
//! is the arm's. Its right side is the body of one of the definition's
//! leaves for the arm (the leaves `check_tree` records in [`LeafLog`], by
//! their place in the case tree), read in the arm's variables. An arm the
//! tree splits further, because an earlier arm overlaps it, has several
//! leaves; their bodies are the same term with the arm's variables refined,
//! unless the body captured a refined variable (a lifted `match` does), and
//! then no leaf says the arm's right side in its own variables: the arm is
//! skipped.
//!
//! **How it's proved.** As a kernel term, never trusted: a case tree on the
//! equation's variables that splits wherever the definition's tree does
//! (walking that tree with the arm's left side), `rfl` at the arm's own
//! leaves and `Void.exfalso` of the hypothesis at an earlier arm's. A
//! `decreasing` definition is walked through its `f.%step`, each leaf
//! proved by `f.unfold`; an `opaque` one's equations are checked with
//! `unfolding f`, as `f.unfold` is (§4).
//!
//! **When.** A program's definitions get theirs when they're checked. The
//! core's and the library's are made on demand (D2178's fallback: eager,
//! they cost every start), when first named (a module's needs) or listed
//! (`search`), from their source in the library index
//! ([`Elaborator::ensure_equations`]).
//!
//! What isn't generated (§3.2, "Not generated") is recorded with the reason,
//! and naming it is `E-NO-EQUATION` ([`no_equation`]).

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{Elim, Head, eval, force};
use stitchwort_core::{DataId, DefId, Globals, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Decl, Expr, MatchKind, Pattern, Scrutinee};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Saved};
use crate::decreasing::{Binder, apps, lams, pis, split_pis};
use crate::{Elaborator, Global, Result, kernel};

/// The variable the probe's body is: [`probe`] records the context it's
/// checked in.
pub(crate) const PROBE: &str = "%equation-probe";

/// What making one equation may take: steps, the size of a term, frames.
/// The equations of std take far less (the largest a few thousand steps).
const ATTEMPT: stitchwort_core::budget::Limits = stitchwort_core::budget::Limits {
    work: 5_000_000,
    stack: 0,
    size: 1_000_000,
    frames: 100_000,
};

/// A right side larger than this many times its arm's elaborated body
/// (`let`s substituted can make it so) isn't generated (§10; the factor is
/// the note's guess).
const SIZE_FACTOR: usize = 10;

/// An equation that would take more than this many hypotheses `x ≠ k` for
/// earlier number arms isn't generated (D2189): its proof splits on the
/// number with every one of them in context, which the kernel refines at
/// each number, so checking it costs their count squared.
const LITERAL_CAP: usize = 64;

// ------------------------------------------------------------ the leaf log

/// Where each case tree's leaves are: recorded by `check_tree` while a
/// declaration's bodies are checked, by the tree's root (the name of the
/// definition, top-level or local, whose body it is) and the path of choices
/// to the leaf, which the kernel term has too.
#[derive(Default)]
pub(crate) struct LeafLog {
    /// The choices from the current root to here: a constructor's index, or
    /// a number case's arm (its default after them).
    pub(crate) path: Vec<u32>,
    root: Option<Span>,
    leaves: Vec<Leaf>,
}

#[derive(Clone)]
struct Leaf {
    root: Span,
    path: Vec<u32>,
    /// The row's span: the arm's, or the or-pattern alternative's.
    span: Span,
    /// The or-pattern alternatives that chose the row.
    alternatives: Vec<Span>,
}

impl LeafLog {
    /// A leaf of the tree being checked, if it's a definition's.
    pub(crate) fn record(&mut self, span: Span, alternatives: &[Span]) {
        if let Some(root) = self.root {
            self.leaves.push(Leaf {
                root,
                path: self.path.clone(),
                span,
                alternatives: alternatives.to_vec(),
            });
        }
    }

    /// The body of the definition named at `root` is checked from here.
    pub(crate) fn enter_root(&mut self, root: Span) -> (Option<Span>, Vec<u32>) {
        (self.root.replace(root), std::mem::take(&mut self.path))
    }

    /// Back to the tree [`Self::enter_root`] left.
    pub(crate) fn leave_root(&mut self, saved: (Option<Span>, Vec<u32>)) {
        self.root = saved.0;
        self.path = saved.1;
    }

    /// Forgets what was recorded, before a new top-level declaration.
    pub(crate) fn clear(&mut self) {
        self.leaves.clear();
        self.path.clear();
        self.root = None;
    }
}

// --------------------------------------------------------------- the probe

/// What the probe saw: the context at the arm's leaf and its goal.
pub(crate) struct Probed {
    saved: Saved,
    goal: Value,
}

/// The probe's state: which probe to record, and what it saw.
#[derive(Default)]
pub(crate) struct ProbeState {
    wanted: Option<Span>,
    found: Option<Probed>,
}

/// The probe [`PROBE`], checked at `span` against `expected`: records the
/// context if it's the one wanted. Its term is never used.
pub(crate) fn probe(cx: &mut Ctx, expected: &Value, span: Span) -> Term {
    let mut state = cx.e.arm_probe.borrow_mut();
    if state.wanted == Some(span) && state.found.is_none() {
        state.found = Some(Probed {
            saved: cx.save(),
            goal: expected.clone(),
        });
    }
    Term::Refl
}

// ---------------------------------------------------------------- the arms

/// How a definition's arms are written.
enum Form {
    /// Arms, each with the header's parameters first.
    Arms,
    /// A `:=` body that is, as a whole, a `match` on header parameters
    /// (D2187): its alternatives are the arms, matching those parameters.
    WholeMatch,
}

/// One row: an arm, or one alternative of an arm with or-patterns.
struct Row {
    /// The arm's number, from 1.
    arm: usize,
    /// The alternative's number among the arm's, from 1; `None` for an arm
    /// without or-patterns.
    or: Option<usize>,
    /// Its patterns, without or-patterns, one per column.
    patterns: Vec<Pattern>,
    /// The spans of the alternatives chosen, sorted.
    alternatives: Vec<Span>,
    /// The arm's span: a leaf's row span is it or inside it.
    span: Span,
    /// Whether it has a right side (an arm with `()` has none).
    has_rhs: bool,
}

impl Row {
    fn suffix(&self) -> String {
        match self.or {
            Some(m) => format!("eq{}.or{m}", self.arm),
            None => format!("eq{}", self.arm),
        }
    }
}

/// Every way of choosing one alternative of each or-pattern in `patterns`:
/// the patterns chosen, and the spans of the alternatives, sorted.
fn expand_or(patterns: &[Pattern]) -> Vec<(Vec<Pattern>, Vec<Span>)> {
    let mut out: Vec<(Vec<Pattern>, Vec<Span>)> = vec![(Vec::new(), Vec::new())];
    for p in patterns {
        let mut next = Vec::new();
        for (done, spans) in &out {
            for (q, more) in expand_one(p) {
                let mut d = done.clone();
                d.push(q);
                let mut s = spans.clone();
                s.extend(more);
                next.push((d, s));
            }
        }
        out = next;
    }
    for (_, spans) in &mut out {
        spans.sort_by_key(|s| (s.start, s.end));
    }
    out
}

fn expand_one(p: &Pattern) -> Vec<(Pattern, Vec<Span>)> {
    let many = |ps: &[Pattern], rebuild: &dyn Fn(Vec<Pattern>) -> Pattern| {
        expand_or(ps)
            .into_iter()
            .map(|(qs, spans)| (rebuild(qs), spans))
            .collect::<Vec<_>>()
    };
    match p {
        Pattern::Or(alternatives, _) => alternatives
            .iter()
            .flat_map(|a| {
                expand_one(a).into_iter().map(move |(q, mut spans)| {
                    spans.push(a.span());
                    (q, spans)
                })
            })
            .collect(),
        Pattern::Ctor(n, args, span) => many(args, &|qs| Pattern::Ctor(n.clone(), qs, *span)),
        Pattern::Tuple(a, b, span) => many(&[(**a).clone(), (**b).clone()], &|mut qs| {
            let b = qs.pop().expect("two");
            let a = qs.pop().expect("two");
            Pattern::Tuple(Box::new(a), Box::new(b), *span)
        }),
        Pattern::Cons(a, b, span) => many(&[(**a).clone(), (**b).clone()], &|mut qs| {
            let b = qs.pop().expect("two");
            let a = qs.pop().expect("two");
            Pattern::Cons(Box::new(a), Box::new(b), *span)
        }),
        Pattern::Named(n, q, span) => many(std::slice::from_ref(&**q), &|mut qs| {
            Pattern::Named(n.clone(), Box::new(qs.pop().expect("one")), *span)
        }),
        Pattern::Record { fields, rest, span } => {
            let ps: Vec<Pattern> = fields.iter().map(|(_, p)| p.clone()).collect();
            many(&ps, &|qs| Pattern::Record {
                fields: fields.iter().map(|(n, _)| n.clone()).zip(qs).collect(),
                rest: *rest,
                span: *span,
            })
        }
        Pattern::CtorFields {
            ctor,
            fields,
            rest,
            span,
        } => {
            let ps: Vec<Pattern> = fields.iter().map(|(_, p)| p.clone()).collect();
            many(&ps, &|qs| Pattern::CtorFields {
                ctor: ctor.clone(),
                fields: fields.iter().map(|(n, _)| n.clone()).zip(qs).collect(),
                rest: *rest,
                span: *span,
            })
        }
        Pattern::Var(_)
        | Pattern::Wildcard(_)
        | Pattern::Absurd(_)
        | Pattern::Num(..)
        | Pattern::NegNum(..)
        | Pattern::Char(..)
        | Pattern::Nil(_) => vec![(p.clone(), Vec::new())],
    }
}

fn has_or(p: &Pattern) -> bool {
    expand_one(p).len() > 1 || matches!(p, Pattern::Or(..))
}

/// The arms of a definition, as the source writes them: the form, the
/// columns' parameter names (for a whole-body `match`, its scrutinees), and
/// each arm's patterns, right side and span.
/// A definition's arms as the source writes them (`source_arms`): the form,
/// the columns' parameter names, and each arm's patterns, whether it has a
/// right side, and its span.
type SourceArms = (Form, Vec<String>, Vec<(Vec<Pattern>, bool, Span)>);

fn source_arms(equations: &[Decl]) -> Option<SourceArms> {
    let first = equations.first()?;
    let Decl::Equation {
        patterns, rhs, arm, ..
    } = first
    else {
        return None;
    };
    if arm.is_some() {
        let arms = equations
            .iter()
            .filter_map(|e| match e {
                Decl::Equation {
                    patterns,
                    rhs,
                    span,
                    ..
                } => Some((patterns.clone(), rhs.is_some(), *span)),
                _ => None,
            })
            .collect();
        return Some((Form::Arms, Vec::new(), arms));
    }
    if equations.len() != 1 {
        return None;
    }
    let Some(Expr::Match {
        scrutinees,
        alts,
        kind: MatchKind::Match,
        ..
    }) = rhs
    else {
        return None;
    };
    let header: Vec<&str> = patterns
        .iter()
        .filter_map(|p| match p {
            Pattern::Var(x) => Some(x.text.as_str()),
            _ => None,
        })
        .collect();
    let mut columns = Vec::new();
    for s in scrutinees {
        match (&s.name, &s.expr) {
            (None, Expr::Var(x)) if header.contains(&x.text.as_str()) => {
                columns.push(x.text.to_string())
            }
            _ => return None,
        }
    }
    let arms = alts
        .iter()
        .map(|a: &Alt| (a.patterns.clone(), true, a.span))
        .collect();
    Some((Form::WholeMatch, columns, arms))
}

/// The equation names the source implies for a definition with these
/// equations (§3.3): `eq1`, `eq2`, `eq3.or1`, …, under the definition's
/// key. The library index lists them before the file is elaborated.
pub(crate) fn source_suffixes(equations: &[Decl]) -> Vec<String> {
    let Some((_, _, arms)) = source_arms(equations) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for (k, (patterns, _, _)) in arms.iter().enumerate() {
        let combos = if patterns.iter().any(has_or) {
            expand_or(patterns).len()
        } else {
            0
        };
        if combos == 0 {
            out.push(format!("eq{}", k + 1));
        } else {
            for m in 1..=combos {
                out.push(format!("eq{}.or{m}", k + 1));
            }
        }
    }
    out
}

/// Whether a declared key's last part is an equation name reserved for the
/// definition `prefix` names: `f.eq`, `f.eq3`, `f.eq3.or1`, … (D2176).
pub(crate) fn reserved_suffix(key: &str) -> Option<(&str, &str)> {
    // `f.eqK.orN` and `f.eqK.ifTrue…`: the `eq` part is the first one that
    // looks like it, after at least one segment of the owner.
    let mut owner_len = 0;
    for (i, part) in key.split('.').enumerate() {
        let digits = part.strip_prefix("eq");
        if i > 0 && digits.is_some_and(|d| d.chars().all(|c| c.is_ascii_digit())) {
            return Some((&key[..owner_len - 1], &key[owner_len..]));
        }
        owner_len += part.len() + 1;
    }
    None
}

/// Whether a local definition can't be called `name`: `eq`, `eqK` and
/// `induct` would be its owner's generated names (D2176).
pub(crate) fn reserved_local(name: &str) -> bool {
    name == "induct"
        || name
            .strip_prefix("eq")
            .is_some_and(|d| d.chars().all(|c| c.is_ascii_digit()))
}

// ------------------------------------------------------- what an arm says

/// An arm's statement, as the probe found it: a context of `depth`
/// variables (the probe's predicate at level 0, then the definition's
/// parameters, then the patterns' fields), the definition's arguments in
/// it, and the variables the equation takes, in order.
struct Shape {
    depth: usize,
    lhs: Vec<Term>,
    /// The levels the equation takes, in order, with their names, how
    /// they're passed, and their types (terms at `depth`).
    tele: Vec<usize>,
    names: Vec<Name>,
    icits: Vec<Icit>,
    types: Vec<Term>,
}

/// A hypothesis: an earlier row the arm overlaps, as the arm's variables
/// can't be.
enum Hyp {
    /// `notArmJ: (vars) → x = p → … → Void`, or `x ≠ p` with no vars and
    /// one equation. `vars` are levels of the earlier row's shape, with its
    /// types; each equation is a level of this arm's shape and a term in
    /// the earlier row's.
    Overlap {
        row: usize,
        vars: Vec<usize>,
        eqs: Vec<(usize, Term)>,
        bound: HashMap<usize, Term>,
    },
    /// `notListed: c ∉ [chars]`: the earlier rows (by index), each a
    /// character `c` can't be.
    Listed {
        level: usize,
        rows: Vec<(usize, char)>,
    },
}

/// Why an equation isn't made: a shape this stage doesn't cover, or an
/// error (which stops the definition's equations).
enum Stop {
    Skip(String),
    Error(Diagnostic),
}

impl From<Diagnostic> for Stop {
    fn from(d: Diagnostic) -> Stop {
        Stop::Error(d)
    }
}

impl From<stitchwort_core::budget::ResourceError> for Stop {
    fn from(e: stitchwort_core::budget::ResourceError) -> Stop {
        Stop::Error(e.into())
    }
}

type R<T> = std::result::Result<T, Stop>;

fn skip<T>(why: impl Into<String>) -> R<T> {
    Err(Stop::Skip(why.into()))
}

/// What kind of definition the equations are for.
#[derive(Clone, Copy)]
pub(crate) enum Kind {
    Plain,
    Opaque,
    /// `decreasing`: its tree is `step`'s, whose parameter `header` is
    /// `%rec`; each leaf is proved by `unfold`.
    Decreasing {
        step: DefId,
        unfold: DefId,
        header: usize,
    },
}

/// The definition, as the generator reads it.
struct Def<'a> {
    f: DefId,
    kind: Kind,
    /// Its key and display name.
    key: &'a str,
    display: String,
    /// Its parameters, as many as its body takes.
    binders: Vec<Binder>,
    /// The names the probe binds them by.
    names: Vec<String>,
    /// What each is in the equations if not a variable: an implicit row of
    /// abilities is `Empty`, a divergence `Total`.
    special: Vec<Option<Term>>,
    /// Its case tree, under its parameters (`%step`'s for `decreasing`).
    tree: Rc<Term>,
    /// The leaves recorded for it.
    leaves: Vec<Leaf>,
    rows: Vec<Row>,
    /// The parameters matched (indices into `binders`).
    columns: Vec<usize>,
}

impl Def<'_> {
    /// The number of parameters of the tree (one more than `binders` for
    /// `decreasing`: `%rec`).
    fn tree_params(&self) -> usize {
        match self.kind {
            Kind::Decreasing { .. } => self.binders.len() + 1,
            _ => self.binders.len(),
        }
    }

    /// The tree's parameter at `level`, as the definition's parameter it
    /// stands for (`None` for `%rec`).
    fn param_of_tree_level(&self, level: usize) -> Option<usize> {
        match self.kind {
            Kind::Decreasing { header, .. } => match level.cmp(&header) {
                std::cmp::Ordering::Less => Some(level),
                std::cmp::Ordering::Equal => None,
                std::cmp::Ordering::Greater => Some(level - 1),
            },
            _ => Some(level),
        }
    }

    /// The row a leaf of the tree at `path` belongs to, if it's an arm's.
    fn row_at(&self, path: &[u32]) -> Option<usize> {
        let leaf = self
            .leaves
            .iter()
            .filter(|l| l.path == path)
            .find(|l| self.rows.iter().any(|r| contains(r.span, l.span)))?;
        let mut alts = leaf.alternatives.clone();
        alts.sort_by_key(|s| (s.start, s.end));
        alts.dedup();
        self.rows
            .iter()
            .position(|r| contains(r.span, leaf.span) && r.alternatives == alts)
    }
}

fn contains(outer: Span, inner: Span) -> bool {
    outer.file == inner.file && outer.start <= inner.start && inner.end <= outer.end
}

// ----------------------------------------------------------- the generator

impl Elaborator {
    /// The equations of a `decreasing` definition `f`, just admitted: its
    /// tree is its `f.%step`'s, and each leaf is proved by `f.unfold`.
    pub(crate) fn decreasing_equations(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        key: Option<&str>,
    ) -> Result<()> {
        let Decl::Signature { name, theorem, .. } = signature else {
            return Ok(());
        };
        if *theorem {
            return self.generate_equations_keyed(f, signature, equations, Kind::Plain, key);
        }
        let key = match key {
            Some(k) => k.to_string(),
            None => self.declaration_key(name)?,
        };
        let Some(unfold) = self.lookup_def(&format!("{key}.unfold")) else {
            return Ok(());
        };
        let step_name = format!("{}.%step", crate::scope::display(&key));
        let g = &self.globals;
        let Some(step) = (0..g.defs.len())
            .rev()
            .map(DefId)
            .find(|id| &*g.def(*id).name == step_name.as_str())
        else {
            return Ok(());
        };
        let (tel, _) = split_pis(&g.def(step).ty, None);
        let Some(header) = tel.iter().position(|b| &*b.name == crate::decreasing::REC) else {
            return Ok(());
        };
        self.generate_equations_keyed(
            f,
            signature,
            equations,
            Kind::Decreasing {
                step,
                unfold,
                header,
            },
            Some(&key),
        )
    }

    /// The equations of definition `f` (final), whose signature and
    /// equations are given: each generated, or recorded as skipped with the
    /// reason. Errors only for running out of resources.
    pub(crate) fn generate_equations(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        kind: Kind,
    ) -> Result<()> {
        self.generate_equations_keyed(f, signature, equations, kind, None)
    }

    /// [`Self::generate_equations`], for a definition by its key (a local
    /// one, or one made on demand outside its own module).
    fn generate_equations_keyed(
        &mut self,
        f: DefId,
        signature: &Decl,
        equations: &[Decl],
        kind: Kind,
        local_key: Option<&str>,
    ) -> Result<()> {
        let Decl::Signature {
            name: def_name,
            theorem,
            instance,
            unfolding,
            ..
        } = signature
        else {
            return Ok(());
        };
        let Some((form, scrutinees, arms)) = source_arms(equations) else {
            return Ok(());
        };
        let key = match local_key {
            Some(k) => k.to_string(),
            None => self.declaration_key(def_name)?,
        };
        let suffixes = source_suffixes(equations);
        let why_none = if *theorem {
            Some("a theorem's arms have no equations: nothing unfolds a proof")
        } else if *instance {
            Some(
                "an instance's arms have no equations: write the method as a named `def` the \
                 instance points to, which gets them",
            )
        } else if !unfolding.is_empty() || !self.globals.def(f).unfolding.is_empty() {
            Some(
                "an `opaque` definition with an `unfolding` clause has no equations, as it has no `unfold`",
            )
        } else {
            None
        };
        if let Some(why) = why_none {
            // A theorem's and an instance's are said by `no_equation` from
            // the definition itself.
            if !*theorem && !*instance {
                for s in &suffixes {
                    self.equation_skips.push((f, s.clone(), why.to_string()));
                }
            }
            return Ok(());
        }
        let def = self.globals.def(f);
        if def.state() != stitchwort_core::globals::State::Final {
            return Ok(());
        }
        let (arity, def_ty) = (def.arity, def.ty.clone());
        let mut rows = Vec::new();
        for (k, (patterns, has_rhs, span)) in arms.iter().enumerate() {
            let combos = expand_or(patterns);
            let or = patterns.iter().any(has_or);
            for (m, (patterns, alternatives)) in combos.into_iter().enumerate() {
                rows.push(Row {
                    arm: k + 1,
                    or: or.then_some(m + 1),
                    patterns,
                    alternatives,
                    span: *span,
                    has_rhs: *has_rhs,
                });
            }
        }
        let display = crate::scope::display(&key).to_string();
        let skip_all = |e: &mut Elaborator, why: &str| {
            for r in &rows {
                e.equation_skips.push((f, r.suffix(), why.to_string()));
            }
        };
        let (tree_def, tree_lams) = match kind {
            Kind::Decreasing { step, header, .. } => (step, Some(header)),
            _ => (f, None),
        };
        let (binders, _) = split_pis(&def_ty, Some(arity));
        if binders.len() != arity {
            skip_all(
                self,
                "its type doesn't show all the parameters its body takes",
            );
            return Ok(());
        }
        let Some(body) = self.globals.def(tree_def).body().cloned() else {
            skip_all(self, "its body isn't available");
            return Ok(());
        };
        let tree_params = arity + usize::from(tree_lams.is_some());
        if self.globals.def(tree_def).arity != tree_params {
            skip_all(
                self,
                "its body returns a function, so its arms aren't a case tree",
            );
            return Ok(());
        }
        let special = special_params(&self.globals, &binders);
        if performs_abilities(&self.globals, &def_ty, &special)? {
            skip_all(
                self,
                "it performs abilities (or is polymorphic in them): its arms are computations, \
                 not stated by equations in stage 1a",
            );
            return Ok(());
        }
        let tree = Term::peel_lams_rc(&body, tree_params);
        // The names the probe binds the parameters by: their own where
        // they're plain and distinct, else `%eN`.
        let mut names: Vec<String> = Vec::new();
        for (i, b) in binders.iter().enumerate() {
            let n = b.name.to_string();
            let plain = !n.is_empty()
                && n != "_"
                && !n.starts_with('%')
                && n.chars().next().is_some_and(|c| c.is_alphabetic())
                && !names.contains(&n);
            names.push(if plain { n } else { format!("%e{i}") });
        }
        let columns: Vec<usize> = match form {
            // The last explicit parameters: a local definition's captures
            // come before its own.
            Form::Arms => {
                let explicit: Vec<usize> = (0..arity)
                    .filter(|&i| binders[i].icit == Icit::Explicit)
                    .collect();
                let p = rows.first().map_or(0, |r| r.patterns.len());
                if p > explicit.len() {
                    skip_all(self, "its arms' patterns don't line up with its parameters");
                    return Ok(());
                }
                explicit[explicit.len() - p..].to_vec()
            }
            Form::WholeMatch => {
                let mut cols = Vec::new();
                for s in &scrutinees {
                    match names.iter().rposition(|n| n == s) {
                        Some(i) => cols.push(i),
                        None => {
                            return Ok(());
                        }
                    }
                }
                cols
            }
        };
        if let Some(first) = rows.first()
            && first.patterns.len() != columns.len()
        {
            skip_all(self, "its arms' patterns don't line up with its parameters");
            return Ok(());
        }
        let leaves: Vec<Leaf> = self
            .leaf_log
            .borrow()
            .leaves
            .iter()
            .filter(|l| l.root == def_name.span)
            .cloned()
            .collect();
        let d = Def {
            f,
            kind,
            key: &key,
            display,
            binders,
            names,
            special,
            tree,
            leaves,
            rows,
            columns,
        };
        let mut d = d;
        // Made on demand, after the definition: its leaves weren't
        // recorded, so its arms are compiled again.
        if d.leaves.is_empty() {
            let why = match self.recompute_leaves(&d, &arms, def_name.span) {
                Ok(Some(leaves)) => {
                    d.leaves = leaves;
                    None
                }
                Ok(None) => Some(
                    "an arm with `()` keeps a definition's equations from being made on demand"
                        .to_string(),
                ),
                Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                Err(Stop::Error(e)) => Some(format!(
                    "its arms couldn't be compiled again: {}",
                    e.message
                )),
                Err(Stop::Skip(why)) => Some(why),
            };
            if let Some(why) = why {
                for r in &d.rows {
                    self.equation_skips.push((f, r.suffix(), why.clone()));
                }
                return Ok(());
            }
        }
        self.equations_of(&d, def_name.span)
    }

    fn equations_of(&mut self, d: &Def, span: Span) -> Result<()> {
        // Each row's shape, from the probe.
        let mut shapes: Vec<std::result::Result<Shape, String>> = Vec::new();
        for row in &d.rows {
            let shape = if !row.has_rhs {
                Err("an arm with `()` has no right side".to_string())
            } else {
                match self.attempt(|e| e.probe_row(d, row, span)) {
                    Ok(s) => Ok(s),
                    Err(Stop::Skip(why)) => Err(why),
                    Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                    Err(Stop::Error(e)) => {
                        Err(format!("its patterns couldn't be read: {}", e.message))
                    }
                }
            };
            shapes.push(shape);
        }
        for (k, row) in d.rows.iter().enumerate() {
            let name = (d.f, row.suffix());
            if self
                .scope
                .get(&format!("{}.{}", d.key, row.suffix()))
                .is_some()
            {
                // Reserved names are refused where they're declared; a
                // clash here is one declared before the definition.
                self.equation_skips.push((
                    name.0,
                    name.1,
                    "the name is already declared".to_string(),
                ));
                continue;
            }
            let shape = match &shapes[k] {
                Ok(s) => s,
                Err(why) => {
                    self.equation_skips.push((name.0, name.1, why.clone()));
                    continue;
                }
            };
            let mark = self.globals.mark();
            match self.attempt(|e| e.equation(d, k, shape, &shapes)) {
                Ok(()) => {}
                Err(Stop::Skip(why)) => {
                    self.globals.rewind(&mark);
                    self.equation_skips.push((name.0, name.1, why));
                }
                Err(Stop::Error(e)) if crate::undo::fatal(&e) => return Err(e),
                Err(Stop::Error(e)) => {
                    self.globals.rewind(&mark);
                    self.equation_skips.push((
                        name.0,
                        name.1,
                        format!(
                            "the kernel refused the generated proof ({}: {})",
                            e.code, e.message
                        ),
                    ));
                }
            }
        }
        Ok(())
    }

    /// `f`, with a step, size and frame budget of its own ([`ATTEMPT`]):
    /// running out of it skips the equation, with the reason, instead of
    /// failing the definition. An equation whose `rfl` the kernel can only
    /// check by computing far (a body that calls a definition on a known
    /// number, `digits 40 (k + n) 0`, compared without sharing) would
    /// otherwise take the time and memory of that computation.
    fn attempt<T>(&mut self, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        let limits = stitchwort_core::budget::Limits {
            work: ATTEMPT.work,
            size: ATTEMPT.size,
            frames: ATTEMPT.frames,
            ..self.limits
        };
        let saved = self.globals.budget.start_attempt(limits);
        let result = f(self);
        self.globals.budget.restore(saved);
        match result {
            Err(Stop::Error(e))
                if e.code == "E-RESOURCE" && self.globals.budget.exhausted().is_none() =>
            {
                Err(Stop::Skip(
                    "checking it takes more than the generator allows for one equation (its \
                     proof computes too far)"
                        .to_string(),
                ))
            }
            other => other,
        }
    }

    /// The shape of `row`: compiles its patterns alone, as a `match` on the
    /// definition's parameters, and probes its body.
    fn probe_row(&mut self, d: &Def, row: &Row, span: Span) -> R<Shape> {
        let g = &self.globals;
        let n = d.binders.len();
        // The predicate `%P: (params) → Prop` the goal applies to the
        // parameters, so the goal at the leaf shows what they are there.
        let pred_ty = pis(&d.binders, Term::Sort(Sort::Prop));
        let pred_ty = eval(g, &[], &pred_ty)?;
        let probe_span = Span {
            file: span.file,
            start: span.start,
            end: span.start,
        };
        let other_span = Span {
            file: span.file,
            start: span.end,
            end: span.end,
        };
        let nav = self.nav.take();
        let lambda_warnings = self.lambda_warnings.borrow().len();
        let branch_errors = self.branch_errors.borrow().len();
        *self.arm_probe.borrow_mut() = ProbeState {
            wanted: Some(probe_span),
            found: None,
        };
        let result = (|| -> Result<Option<()>> {
            let mut cx = Ctx::new(self, span);
            cx.bind_hidden("%P".into(), pred_ty.clone());
            for (i, b) in d.binders.iter().enumerate() {
                let ty = eval(g, &cx.env[1..], &b.ty)?;
                if let Some(value) = &d.special[i] {
                    let ty_term = cx.quote(&ty)?;
                    cx.define(
                        Some(&d.names[i]),
                        b.name.clone(),
                        ty,
                        ty_term,
                        value.clone(),
                    )?;
                } else {
                    cx.bind(&d.names[i], ty);
                }
                cx.set_kind(b.icit);
            }
            let goal_term = apps(
                Term::Var(n),
                (0..n).map(|i| (Term::Var(n - 1 - i), d.binders[i].icit)),
            );
            let goal = cx.eval(&goal_term)?;
            let var = |text: &str, span: Span| {
                Expr::Var(ast::Name {
                    text: text.into(),
                    span,
                })
            };
            let expr = Expr::Match {
                scrutinees: d
                    .columns
                    .iter()
                    .map(|&i| Scrutinee {
                        name: None,
                        expr: var(&d.names[i], span),
                    })
                    .collect(),
                alts: vec![
                    Alt {
                        patterns: row.patterns.clone(),
                        body: var(PROBE, probe_span),
                        span: probe_span,
                    },
                    Alt {
                        patterns: d
                            .columns
                            .iter()
                            .map(|_| Pattern::Wildcard(other_span))
                            .collect(),
                        body: var(PROBE, other_span),
                        span: other_span,
                    },
                ],
                span,
                kind: MatchKind::Match,
            };
            match crate::matching::in_tree(&mut cx, &expr, &goal) {
                None => Ok(None),
                Some(r) => r.map(|_| Some(())),
            }
        })();
        self.nav = nav;
        self.lambda_warnings.borrow_mut().truncate(lambda_warnings);
        self.branch_errors.borrow_mut().truncate(branch_errors);
        let found = std::mem::take(&mut *self.arm_probe.borrow_mut()).found;
        self.clear_metas();
        match result {
            Ok(Some(())) => {}
            Ok(None) => return skip("its patterns aren't a match on its parameters"),
            Err(e) => return Err(Stop::Error(e)),
        }
        let Some(Probed { saved, goal }) = found else {
            return skip("its arm is never reached");
        };
        let cx = saved.ctx(self);
        let g = &self.globals;
        let depth = cx.level();
        let Value::Neutral(Head::Var(0, _), spine) = force(g, goal)? else {
            return skip("its arm's goal wasn't the probe's");
        };
        let mut lhs = Vec::new();
        for elim in spine.iter() {
            match elim {
                Elim::App(v, _) => lhs.push(stitchwort_core::value::quote(g, depth, v)?),
                _ => return skip("its arm's goal wasn't the probe's"),
            }
        }
        if lhs.len() != n {
            return skip("its arm's goal wasn't the probe's");
        }
        let own = |l: usize| {
            cx.lets[l].is_none()
                && matches!(&cx.env[l], Value::Neutral(Head::Var(x, _), s) if *x == l && s.is_empty())
        };
        let mut types: HashMap<usize, Term> = HashMap::default();
        for l in 1..depth {
            if own(l) {
                types.insert(l, stitchwort_core::value::quote(g, depth, &cx.types[l])?);
            }
        }
        // The variables the equation takes: those its arguments mention,
        // and those their types do.
        let mut wanted: Vec<usize> = Vec::new();
        let mut pending: Vec<usize> = lhs.iter().flat_map(|t| levels_in(t, depth)).collect();
        while let Some(l) = pending.pop() {
            if wanted.contains(&l) {
                continue;
            }
            if l == 0 || !own(l) {
                return skip("its left side mentions something other than its variables");
            }
            wanted.push(l);
            pending.extend(levels_in(&types[&l], depth));
        }
        // In order: the parameters, then the arm's variables as written,
        // then the rest by level; each after those its type mentions.
        // The parameters the arms don't match (implicit ones, the
        // header's), then the arm's variables as written, then the rest
        // (`_`s) by level.
        let written: Vec<usize> = crate::written_names(&row.patterns)
            .into_iter()
            .filter_map(|x| cx.lookup(x))
            .collect();
        let rank = |l: usize| -> (usize, usize) {
            if l <= n && !d.columns.contains(&(l - 1)) {
                (0, l)
            } else if let Some(i) = written.iter().position(|&w| w == l) {
                (1, i)
            } else {
                (2, l)
            }
        };
        wanted.sort_by_key(|&l| rank(l));
        let mut tele: Vec<usize> = Vec::new();
        while tele.len() < wanted.len() {
            let next = wanted
                .iter()
                .copied()
                .find(|l| {
                    !tele.contains(l)
                        && levels_in(&types[l], depth)
                            .iter()
                            .all(|m| m == l || tele.contains(m))
                })
                .ok_or_else(|| {
                    Stop::Skip("its variables' types depend on each other in a cycle".into())
                })?;
            tele.push(next);
        }
        let mut names: Vec<Name> = Vec::new();
        let mut icits = Vec::new();
        // `x1`, `x2`, … for those with no name to take (§3.1).
        let mut unnamed = 0;
        for &l in &tele {
            let base = if (1..=n).contains(&l) {
                let given = d.binders[l - 1].name.to_string();
                match cx.name_of_level(l) {
                    Some(x) if !x.starts_with('%') => x.to_string(),
                    _ => given,
                }
            } else {
                cx.name_of_level(l)
                    .map(str::to_string)
                    .unwrap_or_else(|| cx.names[l].trim_end_matches('✝').to_string())
            };
            let base = if base.is_empty() || base == "_" || base.starts_with('%') {
                unnamed += 1;
                format!("x{unnamed}")
            } else {
                base
            };
            names.push(fresh(&names, &base).into());
            icits.push(if (1..=n).contains(&l) {
                d.binders[l - 1].icit
            } else {
                Icit::Explicit
            });
        }
        let pure = d.special.iter().any(Option::is_some);
        let types = tele
            .iter()
            .map(|l| {
                if pure {
                    pure_at_empty(g, &types[l], depth)
                } else {
                    Ok(types[l].clone())
                }
            })
            .collect::<stitchwort_core::budget::Result<_>>()?;
        Ok(Shape {
            depth,
            lhs,
            tele,
            names,
            icits,
            types,
        })
    }

    /// Generates row `k`'s equation (or says why it can't).
    fn equation(
        &mut self,
        d: &Def,
        k: usize,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
    ) -> R<()> {
        let g = &self.globals;
        // The hypotheses: each earlier row it overlaps.
        let mut hyps: Vec<Hyp> = Vec::new();
        for (j, shape_j) in shapes.iter().enumerate().take(k) {
            let other = match shape_j {
                Ok(s) => s,
                // An earlier arm without a right side (`()`): what it covers
                // has no values, so it needs no hypothesis.
                Err(_) if !d.rows[j].has_rhs => continue,
                Err(_) => {
                    return skip(format!(
                        "the overlap with arm {} can't be stated: that arm's patterns couldn't be read",
                        d.rows[j].arm
                    ));
                }
            };
            match overlap(g, other, shape)? {
                Overlap::Disjoint => {}
                Overlap::Unknown => {
                    return skip(format!(
                        "the overlap with arm {} can't be stated as equations of this arm's \
                         variables",
                        d.rows[j].arm
                    ));
                }
                Overlap::Indexed => {
                    return skip(format!(
                        "it overlaps arm {} on an indexed family, where the hypothesis would \
                         compare values of different types (D2185; a heterogeneous equation \
                         isn't in std)",
                        d.rows[j].arm
                    ));
                }
                Overlap::Covers => {
                    return skip(format!(
                        "arm {} matches everything it does, so it's never reached",
                        d.rows[j].arm
                    ));
                }
                Overlap::Meets { vars, eqs, bound } => hyps.push(Hyp::Overlap {
                    row: j,
                    vars,
                    eqs,
                    bound,
                }),
            }
        }
        let hyps = merge_chars(g, hyps, shapes);
        // D2189: past the cap, decided before any kernel work.
        let literals = hyps.iter().filter(|h| number_overlap(h)).count();
        if literals > LITERAL_CAP {
            return skip(format!(
                "it would take {literals} hypotheses `x ≠ k`, one for each earlier number arm, \
                 more than the {LITERAL_CAP} an equation is made with (its proof's cost grows \
                 with their square)"
            ));
        }
        // The right side: a leaf of this row, read in the arm's variables.
        let (rhs, arm_size) = self.right_side(d, k, shape)?;
        // The statement.
        let tk = shape.tele.len();
        let at = |t: &Term, to: usize| -> R<Term> { remap_shape(g, t, shape, to) };
        let mut binders: Vec<(Name, Icit, Term)> = Vec::new();
        for (j, ty) in shape.types.iter().enumerate() {
            binders.push((shape.names[j].clone(), shape.icits[j], at(ty, j)?));
        }
        let mut hyp_names: Vec<Name> = Vec::new();
        let mut used: Vec<Name> = shape.names.clone();
        for (i, h) in hyps.iter().enumerate() {
            let base = match h {
                Hyp::Overlap { row, .. } => {
                    let r = &d.rows[*row];
                    if r.arm == d.rows[k].arm {
                        format!("notOr{}", r.or.unwrap_or(1))
                    } else {
                        let same_arm = hyps.iter().filter(|h| matches!(h, Hyp::Overlap { row: o, .. } if d.rows[*o].arm == r.arm)).count();
                        match (same_arm > 1, r.or) {
                            (true, Some(m)) => format!("notArm{}or{m}", r.arm),
                            _ => format!("notArm{}", r.arm),
                        }
                    }
                }
                Hyp::Listed { .. } => "notListed".to_string(),
            };
            let name: Name = fresh(&used, &base).into();
            used.push(name.clone());
            hyp_names.push(name.clone());
            let ty = self.hyp_type(h, shape, shapes, tk + i)?;
            binders.push((name, Icit::Explicit, ty));
        }
        let depth = tk + hyps.len();
        let f_args: Vec<(Term, Icit)> = shape
            .lhs
            .iter()
            .zip(&d.binders)
            .map(|(t, b)| Ok((at(t, depth)?, b.icit)))
            .collect::<R<_>>()?;
        let lhs = apps(Term::Def(d.f), f_args);
        let rhs_term = at(&rhs, depth)?;
        let body = Term::Eq(None, Rc::new(lhs), Rc::new(rhs_term));
        let ty = binders
            .iter()
            .rev()
            .fold(body.clone(), |acc, (x, icit, ty)| {
                Term::Pi(x.clone(), *icit, Rc::new(ty.clone()), Rc::new(acc))
            });
        // §10: a right side much larger than the arm's body (a `let` used
        // many times, substituted) isn't generated.
        let size = rhs.subterms().count();
        if size > 256 && size > SIZE_FACTOR * arm_size {
            return skip(format!(
                "its right side would be {size} nodes, more than ten times its arm's {arm_size}"
            ));
        }
        // The proof.
        let mut walk = Walk::new(self, d, k, shape, shapes, &hyps, depth, &body)?;
        let mut fvals = Vec::new();
        for level in 0..d.tree_params() {
            fvals.push(match d.param_of_tree_level(level) {
                Some(i) => walk.pv_of(&shape.lhs[i], shape)?,
                None => PV::Rec,
            });
        }
        let tree = walk.go(&d.tree, &mut fvals, &mut Vec::new())?;
        let lam_names: Vec<(Name, Icit)> =
            binders.iter().map(|(x, i, _)| (x.clone(), *i)).collect();
        let proof = lams(&lam_names, tree);
        // Declared and checked by the kernel like any theorem.
        let name: Name = format!("{}.{}", d.display, d.rows[k].suffix()).into();
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, d.rows[k].span)?;
        if matches!(d.kind, Kind::Opaque) {
            stitchwort_core::check::mark_opaque(&mut self.globals, id);
            stitchwort_core::check::set_unfolding(&mut self.globals, id, &[d.f]);
        }
        kernel::define_group(&mut self.globals, &[(id, proof)])?;
        if let Some(item) = self.module.item {
            self.module.def_items.insert(id, item);
        }
        let key = format!("{}.{}", d.key, d.rows[k].suffix());
        self.scope
            .insert(&key, Global::Def(id), d.rows[k].span, false);
        // A name under `f.eqK`, as an update lemma is under its accessor:
        // dot notation looks these up as local definitions.
        if d.rows[k].or.is_some() {
            self.helper_keys
                .insert(format!("{}.eq{}", d.key, d.rows[k].arm));
        }
        self.helper_keys.insert(key);
        Ok(())
    }

    /// Row `k`'s right side, in its shape's context: the body of the first
    /// of its leaves that mentions only what the arm's patterns bind.
    fn right_side(&self, d: &Def, k: usize, shape: &Shape) -> R<(Term, usize)> {
        let g = &self.globals;
        let mut fmap: Vec<Option<Term>> = Vec::new();
        for level in 0..d.tree_params() {
            fmap.push(match d.param_of_tree_level(level) {
                Some(i) => Some(shape.lhs[i].clone()),
                None => Some(rec_term(d, shape.depth)),
            });
        }
        let mut found = Found::None;
        find_rhs(
            g,
            d,
            k,
            shape,
            &d.tree,
            &mut fmap,
            &mut Vec::new(),
            &mut found,
        )?;
        match found {
            Found::Rhs(t, size) => Ok((t, size)),
            Found::Match => skip(
                "its right side is a `match` on its variables, compiled into the case tree: its \
                 branches get equations in stage 1b",
            ),
            Found::Refined => skip(
                "an earlier arm overlaps it, so its body was elaborated once for each case of \
                 that arm's patterns, each with the variables refined (a lifted `match` or local \
                 definition captures them): no one right side states it",
            ),
            Found::None => skip("its arm is never reached in the definition's case tree"),
        }
    }

    /// Hypothesis `h`'s type, at `depth` (the shape's variables, then the
    /// hypotheses before it).
    fn hyp_type(
        &self,
        h: &Hyp,
        shape: &Shape,
        shapes: &[std::result::Result<Shape, String>],
        depth: usize,
    ) -> R<Term> {
        let g = &self.globals;
        let lib =
            Lib::new(g).ok_or_else(|| Stop::Skip("the core's logic isn't loaded yet".into()))?;
        match h {
            Hyp::Listed { level, rows } => {
                let x = remap_shape(g, &Term::Var(shape.depth - 1 - level), shape, depth)?;
                let chars: Rc<[char]> = rows.iter().map(|(_, c)| *c).collect();
                let list = lib.char_list(g, &chars)?;
                let mem = apps(
                    Term::Def(lib.mem),
                    [
                        (Term::Data(lib.char, Vec::new()), Icit::Implicit),
                        (x, Icit::Explicit),
                        (list, Icit::Explicit),
                    ],
                );
                Ok(Term::app(Term::Def(lib.not), mem))
            }
            Hyp::Overlap {
                row,
                vars,
                eqs,
                bound,
            } => {
                let other = shapes[*row].as_ref().map_err(|e| Stop::Skip(e.clone()))?;
                // This arm's terms the earlier row's solved variables stand
                // for, at `depth`.
                let mut solved: HashMap<usize, Term> = HashMap::default();
                for (l, t) in bound {
                    if let Ok(t) = remap_shape(g, t, shape, depth) {
                        solved.insert(*l, t);
                    }
                }
                // The earlier row's levels: its vars bound here in order,
                // the solved ones as this arm's terms.
                let jmap = |t: &Term, to: usize, taken: usize| -> R<Term> {
                    remap(g, t, other.depth, to, &|l| match vars
                        .iter()
                        .take(taken)
                        .position(|&v| v == l)
                    {
                        Some(i) => Some(Term::Var(to - 1 - (depth + i))),
                        None => solved.get(&l).map(|t| t.shift(g, to - depth, 0).ok())?,
                    })?
                    .ok_or_else(|| {
                        Stop::Skip("an overlap mentions a variable it doesn't bind".into())
                    })
                };
                let mut binders: Vec<(Name, Term)> = Vec::new();
                for (i, &v) in vars.iter().enumerate() {
                    let pos = other.tele.iter().position(|&l| l == v).ok_or_else(|| {
                        Stop::Skip("an overlap's variable isn't one of the earlier arm's".into())
                    })?;
                    let ty = jmap(&other.types[pos], depth + i, i)?;
                    binders.push((other.names[pos].clone(), ty));
                }
                let inner = depth + vars.len();
                let mut eq_terms = Vec::new();
                for (e, (lk, s)) in eqs.iter().enumerate() {
                    let x = remap_shape(g, &Term::Var(shape.depth - 1 - lk), shape, inner + e)?;
                    let p = jmap(s, inner + e, vars.len())?;
                    eq_terms.push(Term::Eq(None, Rc::new(x), Rc::new(p)));
                }
                let void = Term::Data(lib.void, Vec::new());
                if vars.is_empty() && eq_terms.len() == 1 {
                    return Ok(Term::app(Term::Def(lib.not), eq_terms.pop().expect("one")));
                }
                let mut ty = void;
                for eq in eq_terms.into_iter().rev() {
                    ty = Term::Pi("_".into(), Icit::Explicit, Rc::new(eq), Rc::new(ty));
                }
                for (x, t) in binders.into_iter().rev() {
                    ty = Term::Pi(x, Icit::Explicit, Rc::new(t), Rc::new(ty));
                }
                Ok(ty)
            }
        }
    }
}

/// A fresh name: `base`, or with a digit added if it's taken.
fn fresh(taken: &[Name], base: &str) -> String {
    if !taken.iter().any(|t| &**t == base) {
        return base.to_string();
    }
    (2..)
        .map(|i| format!("{base}{i}"))
        .find(|c| !taken.iter().any(|t| &**t == c.as_str()))
        .expect("some number is free")
}

/// Whether `t` mentions a computation type: `Comp`, `CompIn`, `CompD` or
/// `Delay`.
fn mentions_computation(g: &Globals, t: &Term) -> bool {
    let r = &g.registry;
    let comp = r.data(Builtin::Comp);
    let defs = [
        r.def(Builtin::CompIn),
        r.def(Builtin::CompD),
        r.def(Builtin::Delay),
    ];
    t.subterms().any(|(t, _)| match t {
        Term::Data(d, _) => Some(*d) == comp,
        Term::Def(id) => defs.contains(&Some(*id)),
        _ => false,
    })
}

/// Whether a definition of type `ty` (taking `binders`) performs abilities:
/// with its implicit rows `Empty` and its divergences `Total` (`special`),
/// a parameter's type or its result is still a computation.
fn performs_abilities(
    g: &Globals,
    ty: &Term,
    special: &[Option<Term>],
) -> stitchwort_core::budget::Result<bool> {
    let mut v = eval(g, &[], ty)?;
    let mut depth = 0;
    for s in special {
        let Value::Pi(_, _, dom, cod) = force(g, v)? else {
            return Ok(true);
        };
        if let Some(t) = s {
            v = cod.apply(g, eval(g, &[], t)?)?;
            continue;
        }
        if mentions_computation(g, &stitchwort_core::value::quote(g, depth, &dom)?) {
            return Ok(true);
        }
        v = cod.apply(g, Value::var(depth))?;
        depth += 1;
    }
    Ok(mentions_computation(
        g,
        &stitchwort_core::value::quote(g, depth, &v)?,
    ))
}

/// What each parameter is in the equations, if not a variable: an
/// effect-polymorphic definition's are stated at the empty row (§3.2), so
/// an implicit row of abilities is `Empty` and an implicit divergence
/// `Total`.
fn special_params(g: &Globals, binders: &[Binder]) -> Vec<Option<Term>> {
    let r = &g.registry;
    let row = r.data(Builtin::Row);
    let div = r.data(Builtin::Divergence);
    let empty = r.ctor(Builtin::RowEmpty);
    let total = r.ctor(Builtin::DivTotal);
    binders
        .iter()
        .map(|b| {
            if b.icit == Icit::Explicit {
                return None;
            }
            match b.ty.strip_loc() {
                Term::Data(d, args) if args.is_empty() && Some(*d) == row => {
                    empty.map(|(d, c)| Term::Ctor(d, c, Vec::new()))
                }
                Term::Data(d, args) if args.is_empty() && Some(*d) == div => {
                    total.map(|(d, c)| Term::Ctor(d, c, Vec::new()))
                }
                _ => None,
            }
        })
        .collect()
}

/// What [`rebuild`] does to each immediate sub-term, given the binders it's
/// under.
type Sub<'a> = &'a mut dyn FnMut(&Rc<Term>, usize) -> stitchwort_core::budget::Result<Rc<Term>>;

/// Rebuilds `t` with each immediate sub-term replaced by `f(sub, binders
/// it's under)`.
fn rebuild(t: &Term, f: Sub<'_>) -> stitchwort_core::budget::Result<Term> {
    let all = |ts: &[Rc<Term>], f: Sub<'_>| {
        ts.iter()
            .map(|t| f(t, 0))
            .collect::<stitchwort_core::budget::Result<Vec<_>>>()
    };
    Ok(match t {
        Term::App(a, b, i) => Term::App(f(a, 0)?, f(b, 0)?, *i),
        Term::Loc(s, inner) => Term::Loc(*s, f(inner, 0)?),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args, f)?),
        Term::Data(d, args) => Term::Data(*d, all(args, f)?),
        Term::Quot(q, args, e) => Term::Quot(*q, all(args, f)?, *e),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, f(a, 0)?, f(b, 1)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, f(b, 1)?),
        Term::Ann(a, b) => Term::Ann(f(a, 0)?, f(b, 0)?),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), f(a, 0)?, f(v, 0)?, f(b, 1)?, *e),
        Term::Eq(ty, a, b) => {
            let ty = match ty {
                Some(ty) => Some(f(ty, 0)?),
                None => None,
            };
            Term::Eq(ty, f(a, 0)?, f(b, 0)?)
        }
        Term::J(m, b, p) => Term::J(f(m, 0)?, f(b, 0)?, f(p, 0)?),
        Term::Case(i, d, branches) => Term::Case(
            *i,
            *d,
            branches
                .iter()
                .map(|b| {
                    Ok(Branch {
                        names: b.names.clone(),
                        body: match &b.body {
                            Some(body) => Some(f(body, b.names.len())?),
                            None => None,
                        },
                    })
                })
                .collect::<stitchwort_core::budget::Result<Vec<_>>>()?
                .into(),
        ),
        Term::NumCase(i, arms, default) => Term::NumCase(
            *i,
            arms.iter()
                .map(|a| {
                    Ok(NumArm {
                        value: a.value.clone(),
                        body: f(&a.body, 0)?,
                    })
                })
                .collect::<stitchwort_core::budget::Result<Vec<_>>>()?
                .into(),
            f(default, 0)?,
        ),
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => t.clone(),
    })
}

/// `t` with every `let` substituted.
fn zeta(g: &Globals, t: &Term) -> stitchwort_core::budget::Result<Term> {
    g.budget.nesting("equations")?;
    if let Term::Let(_, _, v, b, _) = t {
        let v = zeta(g, v)?;
        let b = zeta(g, b)?;
        return b.instantiate(g, &v);
    }
    rebuild(t, &mut |s, _| Ok(Rc::new(zeta(g, s)?)))
}

/// `t` (at `depth`) with the effect library's plumbing at the empty row and
/// `Total` computed away (`bindDv Total Empty c next` is `next c`, `CompIn
/// Empty a` is `a`), so an effect-polymorphic definition's equation reads
/// as pure code (§3.2).
fn pure_at_empty(g: &Globals, t: &Term, depth: usize) -> stitchwort_core::budget::Result<Term> {
    g.budget.nesting("equations")?;
    let r = &g.registry;
    let plumbing = [
        Builtin::CompIn,
        Builtin::DoneIn,
        Builtin::BindIn,
        Builtin::CompD,
        Builtin::DoneD,
        Builtin::BindDv,
        Builtin::LiftD,
        Builtin::LiftIn,
    ]
    .map(|b| r.def(b));
    let t = rebuild(t, &mut |s, under| {
        Ok(Rc::new(pure_at_empty(g, s, depth + under)?))
    })?;
    let (head, args) = t.spine();
    let Term::Def(id) = head else {
        return Ok(t);
    };
    if args.is_empty() || !plumbing.contains(&Some(*id)) {
        return Ok(t);
    }
    // One step of its case tree, where its row or divergence is known.
    let env: Vec<Value> = (0..depth).map(Value::var).collect();
    let value = eval(g, &env, &t)?;
    let stepped = force(g, value)?;
    let back = stitchwort_core::value::quote_folded(g, depth, &stepped)?;
    if matches!(back.spine().0, Term::Def(d) if d == id) {
        return Ok(t);
    }
    let back = beta_rec(g, back)?;
    pure_at_empty(g, &back, depth)
}

/// The levels of a context of `depth` variables `t` mentions.
fn levels_in(t: &Term, depth: usize) -> Vec<usize> {
    let mut out = Vec::new();
    for (s, binders) in t.subterms() {
        if let Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) = s
            && *i >= binders
            && let Some(l) = depth.checked_sub(1 + (i - binders))
            && !out.contains(&l)
        {
            out.push(l);
        }
    }
    out
}

/// `t`, a term in a shape's context, in a context of `to` variables whose
/// first are the shape's variables in order.
fn remap_shape(g: &Globals, t: &Term, shape: &Shape, to: usize) -> R<Term> {
    remap(g, t, shape.depth, to, &|l| {
        shape
            .tele
            .iter()
            .position(|&x| x == l)
            .map(|j| Term::Var(to - 1 - j))
    })?
    .ok_or_else(|| Stop::Skip("its statement mentions a variable its arm doesn't bind".into()))
}

/// `t`, in a context of `from` variables, with each free variable at level
/// `l` replaced by `map(l)`, a term in a context of `to` variables; `None`
/// if one isn't mapped, or is a case's scrutinee.
fn remap(
    g: &Globals,
    t: &Term,
    from: usize,
    to: usize,
    map: &dyn Fn(usize) -> Option<Term>,
) -> stitchwort_core::budget::Result<Option<Term>> {
    struct Missing;
    fn go(
        g: &Globals,
        t: &Term,
        k: usize,
        from: usize,
        map: &dyn Fn(usize) -> Option<Term>,
    ) -> stitchwort_core::budget::Result<std::result::Result<Term, Missing>> {
        g.budget.nesting("equations")?;
        macro_rules! sub {
            ($t:expr, $k:expr) => {
                match go(g, $t, $k, from, map)? {
                    Ok(t) => Rc::new(t),
                    Err(m) => return Ok(Err(m)),
                }
            };
        }
        Ok(Ok(match t {
            Term::Var(i) if *i < k => Term::Var(*i),
            Term::Var(i) => {
                let Some(level) = from.checked_sub(1 + (i - k)) else {
                    return Ok(Err(Missing));
                };
                match map(level) {
                    Some(t) => t.shift(g, k, 0)?,
                    None => return Ok(Err(Missing)),
                }
            }
            Term::Def(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => t.clone(),
            Term::Data(d, args) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Data(*d, out)
            }
            Term::Ctor(d, c, args) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Ctor(*d, *c, out)
            }
            Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, sub!(a, k), sub!(b, k + 1)),
            Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, sub!(b, k + 1)),
            Term::App(f, a, i) => Term::App(sub!(f, k), sub!(a, k), *i),
            Term::Ann(e, ty) => Term::Ann(sub!(e, k), sub!(ty, k)),
            Term::Let(x, a, v, b, e) => {
                Term::Let(x.clone(), sub!(a, k), sub!(v, k), sub!(b, k + 1), *e)
            }
            Term::Eq(ty, a, b) => {
                let ty = match ty {
                    Some(ty) => Some(sub!(ty, k)),
                    None => None,
                };
                Term::Eq(ty, sub!(a, k), sub!(b, k))
            }
            Term::J(m, b, p) => Term::J(sub!(m, k), sub!(b, k), sub!(p, k)),
            Term::Quot(form, args, erased) => {
                let mut out = Vec::new();
                for a in args {
                    out.push(sub!(a, k));
                }
                Term::Quot(*form, out, *erased)
            }
            Term::Loc(span, t) => Term::Loc(*span, sub!(t, k)),
            // A case on a free variable can't be moved to a context where
            // it's a term; one on a bound variable stays.
            Term::Case(i, d, branches) if *i < k => {
                let mut out = Vec::new();
                for b in branches.iter() {
                    out.push(Branch {
                        names: b.names.clone(),
                        body: match &b.body {
                            Some(body) => Some(sub!(body, k + b.names.len())),
                            None => None,
                        },
                    });
                }
                Term::Case(*i, *d, out.into())
            }
            Term::NumCase(i, arms, default) if *i < k => {
                let mut out = Vec::new();
                for a in arms.iter() {
                    out.push(NumArm {
                        value: a.value.clone(),
                        body: sub!(&a.body, k),
                    });
                }
                Term::NumCase(*i, out.into(), sub!(default, k))
            }
            Term::Case(..) | Term::NumCase(..) => return Ok(Err(Missing)),
        }))
    }
    let _ = to;
    Ok(go(g, t, 0, from, map)?.ok())
}

/// What `%rec` stands for in a `decreasing` definition's equations, at
/// `depth`: `(y… [decreasing]) => f y…`.
fn rec_term(d: &Def, depth: usize) -> Term {
    let n = d.binders.len();
    let inner = depth + n + 1;
    let call = apps(
        Term::Def(d.f),
        (0..n).map(|i| (Term::Var(inner - 1 - (depth + i)), d.binders[i].icit)),
    );
    let mut names: Vec<(Name, Icit)> = d.binders.iter().map(|b| (b.name.clone(), b.icit)).collect();
    names.push(("decreasing".into(), Icit::Auto));
    lams(&names, call)
}

/// Applications of `%rec`'s lambda, reduced: `((y => f y) a)` is `f a`.
fn beta_rec(g: &Globals, t: Term) -> stitchwort_core::budget::Result<Term> {
    g.budget.nesting("equations")?;
    let (head, args) = {
        let (h, a) = t.spine();
        (h.clone(), a.into_iter().cloned().collect::<Vec<Term>>())
    };
    if let Term::Lam(..) = head
        && !args.is_empty()
    {
        let mut f = head;
        for a in args {
            let a = beta_rec(g, a)?;
            f = match f.strip_loc() {
                Term::Lam(_, _, body) => body.instantiate(g, &a)?,
                _ => Term::app(f, a),
            };
        }
        return Ok(f);
    }
    let go = |t: &Rc<Term>| -> stitchwort_core::budget::Result<Rc<Term>> {
        Ok(Rc::new(beta_rec(g, (**t).clone())?))
    };
    let all = |ts: &[Rc<Term>]| -> stitchwort_core::budget::Result<Vec<Rc<Term>>> {
        ts.iter().map(go).collect()
    };
    Ok(match &t {
        Term::App(f, a, i) => Term::App(go(f)?, go(a)?, *i),
        Term::Loc(s, inner) => Term::Loc(*s, go(inner)?),
        Term::Ctor(d, c, args) => Term::Ctor(*d, *c, all(args)?),
        Term::Data(d, args) => Term::Data(*d, all(args)?),
        Term::Quot(f, args, e) => Term::Quot(*f, all(args)?, *e),
        Term::Pi(x, i, a, b) => Term::Pi(x.clone(), *i, go(a)?, go(b)?),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, go(b)?),
        Term::Ann(a, b) => Term::Ann(go(a)?, go(b)?),
        Term::Let(x, a, v, b, e) => Term::Let(x.clone(), go(a)?, go(v)?, go(b)?, *e),
        Term::Eq(ty, a, b) => Term::Eq(ty.as_ref().map(go).transpose()?, go(a)?, go(b)?),
        Term::J(m, b, p) => Term::J(go(m)?, go(b)?, go(p)?),
        _ => t,
    })
}

enum Found {
    None,
    /// A leaf whose body mentions what the arm's patterns don't bind.
    Refined,
    /// A leaf whose body is a further case tree.
    Match,
    /// The right side, and the size of the leaf's body it came from.
    Rhs(Term, usize),
}

/// Looks through the tree, with the arm's arguments, for a leaf of row
/// `k` whose body says its right side in the arm's variables.
#[allow(clippy::too_many_arguments)]
fn find_rhs(
    g: &Globals,
    d: &Def,
    k: usize,
    shape: &Shape,
    t: &Term,
    fmap: &mut Vec<Option<Term>>,
    path: &mut Vec<u32>,
    found: &mut Found,
) -> R<()> {
    g.budget.nesting("equations")?;
    if matches!(found, Found::Rhs(..)) {
        return Ok(());
    }
    if let Some(row) = d.row_at(path) {
        if row != k {
            return Ok(());
        }
        let depth = fmap.len();
        let body = t.strip_loc();
        if matches!(body, Term::Case(..) | Term::NumCase(..)) {
            *found = Found::Match;
            return Ok(());
        }
        let mapped = remap(g, t, depth, shape.depth, &|l| fmap[l].clone())?;
        match mapped {
            Some(rhs) => {
                let rhs = if matches!(d.kind, Kind::Decreasing { .. }) {
                    beta_rec(g, rhs)?
                } else {
                    rhs
                };
                let rhs = if d.special.iter().any(Option::is_some) {
                    pure_at_empty(g, &rhs, shape.depth)?
                } else {
                    rhs
                };
                // `let`s substituted, as goals show them (§3.1).
                let rhs = zeta(g, &rhs)?;
                *found = Found::Rhs(rhs, t.subterms().count());
            }
            None => {
                if matches!(found, Found::None) {
                    *found = Found::Refined;
                }
            }
        }
        return Ok(());
    }
    match t.strip_loc() {
        Term::Case(ix, data, branches) => {
            let depth = fmap.len();
            let x = depth - 1 - ix;
            let known = fmap[x].as_ref().and_then(|v| ctor_view(g, v, *data));
            for (c, b) in branches.iter().enumerate() {
                let Some(body) = &b.body else { continue };
                let fields: Vec<Option<Term>> = match &known {
                    Some((kc, args)) if *kc == c => args.iter().cloned().map(Some).collect(),
                    Some(_) => continue,
                    None => vec![None; b.names.len()],
                };
                let mark = fmap.len();
                fmap.extend(fields);
                path.push(c as u32);
                find_rhs(g, d, k, shape, body, fmap, path, found)?;
                path.pop();
                fmap.truncate(mark);
            }
            Ok(())
        }
        Term::NumCase(ix, arms, default) => {
            let depth = fmap.len();
            let x = depth - 1 - ix;
            let known = fmap[x].as_ref().and_then(|v| match v.strip_loc() {
                Term::Nat(n) => Some((**n).clone()),
                _ => None,
            });
            for (i, a) in arms.iter().enumerate() {
                if known.as_ref().is_some_and(|n| *n != *a.value) {
                    continue;
                }
                path.push(i as u32);
                find_rhs(g, d, k, shape, &a.body, fmap, path, found)?;
                path.pop();
            }
            if !known
                .as_ref()
                .is_some_and(|n| arms.iter().any(|a| *a.value == *n))
            {
                path.push(arms.len() as u32);
                find_rhs(g, d, k, shape, default, fmap, path, found)?;
                path.pop();
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// `t` as constructor `c` of `data` applied to fields, if it is one (a
/// number, of `Nat`, as `Zero` or `Succ`).
fn ctor_view(g: &Globals, t: &Term, data: DataId) -> Option<(usize, Vec<Term>)> {
    match t.strip_loc() {
        Term::Ctor(d, c, args) if *d == data => {
            Some((*c, args.iter().map(|a| (**a).clone()).collect()))
        }
        Term::Nat(n) if g.builtins.nat == Some(data) => {
            if n.bits() == 0 {
                Some((0, Vec::new()))
            } else {
                Some((1, vec![Term::Nat(Rc::new((**n).clone() - 1u32))]))
            }
        }
        _ => None,
    }
}

impl Elaborator {
    /// The equations of the local definitions lifted from the declaration
    /// (or group) just admitted: `helpers` are their keys, ids and spans.
    /// In a `decreasing` definition they take `%rec`, which a statement
    /// can't use, so they get none (§3.2).
    pub(crate) fn local_equations(
        &mut self,
        helpers: &[(String, DefId, Span)],
        decreasing: bool,
    ) -> Result<()> {
        let asts = std::mem::take(&mut *self.local_asts.borrow_mut());
        for (key, id, _) in helpers {
            let Some((_, def)) = asts.iter().find(|(k, _)| k == key) else {
                continue;
            };
            if decreasing {
                for s in source_suffixes(&def.equations) {
                    self.equation_skips.push((
                        *id,
                        s,
                        "a local definition in a `decreasing` definition takes `%rec`, which a \
                         statement can't use; the owner's own equations cover it"
                            .to_string(),
                    ));
                }
                continue;
            }
            let kind = if self.globals.def(*id).opaque {
                Kind::Opaque
            } else {
                Kind::Plain
            };
            self.generate_equations_keyed(*id, &def.signature, &def.equations, kind, Some(key))?;
        }
        Ok(())
    }

    /// Whether a top-level definition's equations are made on demand, not
    /// with it: the core's and the library's (D2178's fallback). The core
    /// loads at every start, the playground's included, and a library
    /// file without the check cache with whatever uses it, so their
    /// equations, made eagerly, cost every run (+11% of a small program's
    /// steps). A program's own stay eager. Local definitions' too.
    pub(crate) fn defers_equations(&self) -> bool {
        self.loading_prelude
    }

    /// Makes the equations of the library's and the core's definitions
    /// with these keys (a reference to `f.eq2` names `f`), from their
    /// source in the library index, if they aren't made yet.
    pub(crate) fn ensure_equations<'a>(
        &mut self,
        keys: impl IntoIterator<Item = &'a String>,
    ) -> Result<()> {
        let keys: Vec<String> = keys.into_iter().cloned().collect();
        for key in keys {
            self.ensure_equations_of(&key)?;
        }
        Ok(())
    }

    fn ensure_equations_of(&mut self, key: &str) -> Result<()> {
        if self.equations_done.iter().any(|k| k == key) {
            return Ok(());
        }
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let Some(f) = index.owner(key) else {
            return Ok(());
        };
        let Some(id) = self.lookup_def(key) else {
            return Ok(());
        };
        if self.globals.def(id).state() != stitchwort_core::globals::State::Final {
            return Ok(());
        }
        let file = &index.files[f];
        let Some(span) = (file.names.iter()).find(|n| n.key == key).map(|n| n.span) else {
            return Ok(());
        };
        let Some((signature, equations)) = crate::project::grouped(&file.module.decls)
            .into_iter()
            .find(|(d, _)| matches!(d, Decl::Signature { name, .. } if name.span == span))
        else {
            return Ok(());
        };
        self.equations_done.push(key.to_string());
        // Made with the definition already (a library file replayed from
        // the check cache, whose own proofs named them).
        if source_suffixes(equations)
            .first()
            .is_some_and(|s| self.scope.get(&format!("{key}.{s}")).is_some())
        {
            return Ok(());
        }
        let saved_item = self.module.item.take();
        // Their full names are the library's, wherever they're made.
        let saved_module = std::mem::replace(&mut self.globals.module, "Std".into());
        let saved_leaves = std::mem::take(&mut self.leaf_log.borrow_mut().leaves);
        let decreasing = matches!(
            signature,
            Decl::Signature {
                decreasing: Some(_),
                ..
            }
        );
        let opaque = matches!(signature, Decl::Signature { opaque: true, .. });
        let result = if decreasing {
            self.decreasing_equations(id, signature, equations, Some(key))
        } else {
            let kind = if opaque { Kind::Opaque } else { Kind::Plain };
            self.generate_equations_keyed(id, signature, equations, kind, Some(key))
        };
        self.leaf_log.borrow_mut().leaves = saved_leaves;
        self.module.item = saved_item;
        self.globals.module = saved_module;
        result
    }

    /// The equations of the library file being loaded's own definitions
    /// that its proofs name: made, as on demand, once the definitions are.
    pub(crate) fn ensure_loading_file_equations(&mut self) {
        let (Some(f), Some(lib)) = (self.scope.loading, &self.library) else {
            return;
        };
        let needs = lib.index.files[f].equation_needs.clone();
        if !needs.is_empty() {
            let _ = self.ensure_equations(&needs);
        }
    }

    /// Makes every put-off equation of the core and the loaded library
    /// files: for listing them all (`search`, `doc`).
    pub fn generate_deferred_equations(&mut self) -> Result<()> {
        let Some(lib) = &self.library else {
            return Ok(());
        };
        let index = lib.index.clone();
        let mut files = vec![0];
        files.extend(lib.order.iter().copied());
        for f in files {
            let keys: Vec<String> = crate::project::grouped(&index.files[f].module.decls)
                .into_iter()
                .filter(|(d, e)| {
                    matches!(
                        d,
                        Decl::Signature {
                            theorem: false,
                            instance: false,
                            ..
                        }
                    ) && source_arms(e).is_some()
                })
                .filter_map(|(d, _)| {
                    let Decl::Signature { name, .. } = d else {
                        return None;
                    };
                    (index.files[f].names.iter())
                        .find(|n| n.span == name.span)
                        .map(|n| n.key.clone())
                })
                .collect();
            self.ensure_equations(&keys)?;
        }
        Ok(())
    }

    /// The leaves of the definition's case tree, when none were recorded
    /// (its equations made on demand, after it): its arms compiled again,
    /// as its body was, with a probe for each body, under a root of their
    /// own, and read off the log. `None` for an arm with `()`, which
    /// compiles differently as an alternative of a `match`.
    fn recompute_leaves(
        &mut self,
        d: &Def,
        arms: &[(Vec<Pattern>, bool, Span)],
        root: Span,
    ) -> R<Option<Vec<Leaf>>> {
        if arms.iter().any(|(_, has_rhs, _)| !has_rhs) {
            return Ok(None);
        }
        let g = &self.globals;
        let n = d.binders.len();
        let pred_ty = eval(g, &[], &pis(&d.binders, Term::Sort(Sort::Prop)))?;
        let nav = self.nav.take();
        let lambda_warnings = self.lambda_warnings.borrow().len();
        let branch_errors = self.branch_errors.borrow().len();
        let logged = self.leaf_log.borrow().leaves.len();
        let saved_root = self.leaf_log.borrow_mut().enter_root(root);
        let result = (|| -> Result<Option<()>> {
            let mut cx = Ctx::new(self, root);
            cx.bind_hidden("%P".into(), pred_ty.clone());
            for (i, b) in d.binders.iter().enumerate() {
                let ty = eval(g, &cx.env[1..], &b.ty)?;
                if let Some(value) = &d.special[i] {
                    let ty_term = cx.quote(&ty)?;
                    cx.define(
                        Some(&d.names[i]),
                        b.name.clone(),
                        ty,
                        ty_term,
                        value.clone(),
                    )?;
                } else {
                    cx.bind(&d.names[i], ty);
                }
                cx.set_kind(b.icit);
            }
            let goal_term = apps(
                Term::Var(n),
                (0..n).map(|i| (Term::Var(n - 1 - i), d.binders[i].icit)),
            );
            let goal = cx.eval(&goal_term)?;
            let var = |text: &str, span: Span| {
                Expr::Var(ast::Name {
                    text: text.into(),
                    span,
                })
            };
            let expr = Expr::Match {
                scrutinees: d
                    .columns
                    .iter()
                    .map(|&i| Scrutinee {
                        name: None,
                        expr: var(&d.names[i], root),
                    })
                    .collect(),
                alts: arms
                    .iter()
                    .map(|(patterns, _, span)| Alt {
                        patterns: patterns.clone(),
                        body: var(PROBE, *span),
                        span: *span,
                    })
                    .collect(),
                span: root,
                kind: MatchKind::Match,
            };
            match crate::matching::in_tree(&mut cx, &expr, &goal) {
                None => Ok(None),
                Some(r) => r.map(|_| Some(())),
            }
        })();
        self.nav = nav;
        self.lambda_warnings.borrow_mut().truncate(lambda_warnings);
        self.branch_errors.borrow_mut().truncate(branch_errors);
        let leaves = {
            let mut log = self.leaf_log.borrow_mut();
            log.leave_root(saved_root);
            let leaves: Vec<Leaf> = log.leaves[logged..]
                .iter()
                .filter(|l| l.root == root)
                .cloned()
                .collect();
            log.leaves.truncate(logged);
            leaves
        };
        self.clear_metas();
        match result {
            Ok(Some(())) => Ok(Some(leaves)),
            Ok(None) => Ok(None),
            Err(e) => Err(Stop::Error(e)),
        }
    }
}

// ------------------------------------------------------------- overlaps

enum Overlap {
    Disjoint,
    /// The earlier row takes every value this one does.
    Covers,
    /// The earlier row's variables the equations need, the equations (a
    /// level of this arm's shape, equal to a term in the earlier row's),
    /// and the earlier row's variables solved by terms of this one's.
    Meets {
        vars: Vec<usize>,
        eqs: Vec<(usize, Term)>,
        bound: HashMap<usize, Term>,
    },
    Unknown,
    /// The overlap's equation would be on an indexed family.
    Indexed,
}

/// Whether an earlier row (`other`) overlaps this one (`shape`): their
/// left sides unified, the earlier's variables solved by this one's terms
/// where they can be, and the rest left as equations of this one's
/// variables.
fn overlap(g: &Globals, other: &Shape, shape: &Shape) -> R<Overlap> {
    let mut bound: HashMap<usize, Term> = HashMap::default();
    let mut eqs: Vec<(usize, Term)> = Vec::new();
    // Every column, so one that's disjoint settles it even when another
    // can't be read.
    let mut worst = Unified::Yes;
    for (a, b) in other.lhs.iter().zip(&shape.lhs) {
        match unify(g, a, other.depth, b, shape.depth, &mut bound, &mut eqs) {
            Unified::Yes => {}
            Unified::No => return Ok(Overlap::Disjoint),
            Unified::Indexed => worst = Unified::Indexed,
            Unified::Unknown => {
                if !matches!(worst, Unified::Indexed) {
                    worst = Unified::Unknown;
                }
            }
        }
    }
    match worst {
        Unified::Indexed => return Ok(Overlap::Indexed),
        Unified::Unknown => return Ok(Overlap::Unknown),
        _ => {}
    }
    if eqs.is_empty() {
        // Every value this arm takes, the earlier one does too.
        return Ok(Overlap::Covers);
    }
    // The earlier row's variables the equations mention and nothing solved,
    // and those their types mention.
    let mut vars: Vec<usize> = Vec::new();
    let mut pending: Vec<usize> = eqs
        .iter()
        .flat_map(|(_, s)| levels_in(s, other.depth))
        .collect();
    while let Some(l) = pending.pop() {
        if vars.contains(&l) || bound.contains_key(&l) {
            continue;
        }
        let Some(pos) = other.tele.iter().position(|&x| x == l) else {
            return Ok(Overlap::Unknown);
        };
        vars.push(l);
        pending.extend(levels_in(&other.types[pos], other.depth));
    }
    vars.sort_by_key(|l| other.tele.iter().position(|x| x == l));
    Ok(Overlap::Meets { vars, eqs, bound })
}

enum Unified {
    Yes,
    No,
    Unknown,
    Indexed,
}

/// Unifies `a` (in the earlier row's context) with `b` (in this one's).
fn unify(
    g: &Globals,
    a: &Term,
    adepth: usize,
    b: &Term,
    bdepth: usize,
    bound: &mut HashMap<usize, Term>,
    eqs: &mut Vec<(usize, Term)>,
) -> Unified {
    let a = a.strip_loc();
    let b = b.strip_loc();
    // A variable of the earlier row matches anything.
    if let Term::Var(i) = a {
        let la = adepth - 1 - i;
        return match bound.get(&la) {
            None => {
                bound.insert(la, b.clone());
                Unified::Yes
            }
            Some(t) if stitchwort_core::value::same_term(t, b) => Unified::Yes,
            Some(_) => Unified::Unknown,
        };
    }
    if let Term::Var(i) = b {
        let lb = bdepth - 1 - i;
        if eqs.iter().any(|(l, _)| *l == lb) {
            return Unified::Unknown;
        }
        // On an indexed family, `x = C …` may compare values of different
        // types (D2185).
        if let Some(d) = data_of(a)
            && !g.data(d).indices.is_empty()
        {
            return Unified::Indexed;
        }
        eqs.push((lb, a.clone()));
        return Unified::Yes;
    }
    if let (Some(data), _) | (_, Some(data)) = (data_of(a), data_of(b))
        && let (Some((ca, xs)), Some((cb, ys))) = (ctor_view(g, a, data), ctor_view(g, b, data))
    {
        if ca != cb {
            return Unified::No;
        }
        for (x, y) in xs.iter().zip(&ys) {
            match unify(g, x, adepth, y, bdepth, bound, eqs) {
                Unified::Yes => {}
                other => return other,
            }
        }
        return Unified::Yes;
    }
    match (a, b) {
        (Term::Refl, Term::Refl) => Unified::Yes,
        (Term::Nat(x), Term::Nat(y)) => {
            if x == y {
                Unified::Yes
            } else {
                Unified::No
            }
        }
        _ if closed(a) && stitchwort_core::value::same_term(a, b) => Unified::Yes,
        _ => Unified::Unknown,
    }
}

fn closed(t: &Term) -> bool {
    levels_in(t, usize::MAX).is_empty()
}

fn data_of(t: &Term) -> Option<DataId> {
    match t.strip_loc() {
        Term::Ctor(d, _, _) => Some(*d),
        _ => None,
    }
}

/// A character literal `MkChar k rfl`'s character.
fn char_literal(g: &Globals, t: &Term) -> Option<char> {
    let char_data = g.registry.data(Builtin::Char)?;
    match t.strip_loc() {
        Term::Ctor(d, 0, args) if *d == char_data && args.len() == 2 => {
            let Term::Nat(code) = args[0].strip_loc() else {
                return None;
            };
            if !matches!(args[1].strip_loc(), Term::Refl) {
                return None;
            }
            u32::try_from(&**code).ok().and_then(char::from_u32)
        }
        _ => None,
    }
}

/// Whether `h` only says a variable isn't some number (`n ≠ k`).
fn number_overlap(h: &Hyp) -> bool {
    matches!(h, Hyp::Overlap { vars, eqs, .. }
        if vars.is_empty() && eqs.len() == 1 && matches!(eqs[0].1.strip_loc(), Term::Nat(_)))
}

/// The earlier rows that only say a variable isn't some character, merged
/// into one `c ∉ […]` per variable (§3.2), where the first of them was.
fn merge_chars(
    g: &Globals,
    hyps: Vec<Hyp>,
    shapes: &[std::result::Result<Shape, String>],
) -> Vec<Hyp> {
    let _ = shapes;
    let single = |h: &Hyp| -> Option<(usize, usize, char)> {
        match h {
            Hyp::Overlap { row, vars, eqs, .. } if vars.is_empty() && eqs.len() == 1 => {
                let (l, s) = &eqs[0];
                char_literal(g, s).map(|c| (*row, *l, c))
            }
            _ => None,
        }
    };
    let mut out: Vec<Hyp> = Vec::new();
    for h in hyps {
        if let Some((row, level, c)) = single(&h) {
            if let Some(Hyp::Listed { rows, .. }) = out
                .iter_mut()
                .find(|o| matches!(o, Hyp::Listed { level: l, .. } if *l == level))
            {
                rows.push((row, c));
                continue;
            }
            out.push(Hyp::Listed {
                level,
                rows: vec![(row, c)],
            });
            continue;
        }
        out.push(h);
    }
    out
}

// ---------------------------------------------------------------- proofs

/// The library's declarations the proofs use.
struct Lib {
    void: DataId,
    char: DataId,
    or: DataId,
    not: DefId,
    mem: DefId,
    exfalso: DefId,
    unique: DefId,
}

impl Lib {
    fn new(g: &Globals) -> Option<Lib> {
        let r = &g.registry;
        Some(Lib {
            void: r.data(Builtin::Void)?,
            char: r.data(Builtin::Char)?,
            or: r.data(Builtin::Or)?,
            not: r.def(Builtin::Not)?,
            mem: r.def(Builtin::ListMem)?,
            exfalso: r.def(Builtin::VoidExfalso)?,
            unique: r.def(Builtin::BoolUniqueEq)?,
        })
    }

    /// The list of these characters, as a literal is.
    fn char_list(&self, g: &Globals, chars: &Rc<[char]>) -> R<Term> {
        if let Some(text) = g.builtins.compact_literals() {
            return Ok(stitchwort_core::chars::term(
                text,
                &stitchwort_core::chars::Chars::whole(chars.clone()),
            ));
        }
        let list = g
            .registry
            .data(Builtin::List)
            .ok_or_else(|| Stop::Skip("`List` isn't loaded yet".into()))?;
        let mut t = Term::Ctor(list, 0, Vec::new());
        for c in chars.iter().rev() {
            let ch = Term::ctor(
                self.char,
                0,
                vec![Term::Nat(Rc::new(BigUint::from(u32::from(*c)))), Term::Refl],
            );
            t = Term::ctor(list, 1, vec![ch, t]);
        }
        Ok(t)
    }
}

/// A value in the proof's context: a variable (by level), a constructor,
/// a number, a term (at the depth given), or `%rec`.
#[derive(Clone)]
enum PV {
    Var(usize),
    Ctor(DataId, usize, Vec<PV>),
    Nat(Rc<BigUint>),
    Term(Term, usize),
    Rec,
}

/// The proof of one equation, built by walking the definition's tree.
struct Walk<'a> {
    e: &'a Elaborator,
    d: &'a Def<'a>,
    k: usize,
    shapes: &'a [std::result::Result<Shape, String>],
    hyps: &'a [Hyp],
    /// The equation's variables and hypotheses.
    base: usize,
    tk: usize,
    /// The statement's `lhs = rhs`, at `base`.
    body: &'a Term,
    /// What each variable of the proof's context is (itself, unless a
    /// split refined it).
    pvals: Vec<PV>,
    /// The numbers a variable is known not to be.
    apart: HashMap<usize, Vec<BigUint>>,
    /// `None` before the core's logic is loaded: then no leaf of an earlier
    /// arm can be refuted.
    lib: Option<Lib>,
}

impl<'a> Walk<'a> {
    #[allow(clippy::too_many_arguments)]
    fn new(
        e: &'a Elaborator,
        d: &'a Def<'a>,
        k: usize,
        shape: &'a Shape,
        shapes: &'a [std::result::Result<Shape, String>],
        hyps: &'a [Hyp],
        base: usize,
        body: &'a Term,
    ) -> R<Walk<'a>> {
        let lib = Lib::new(&e.globals);
        Ok(Walk {
            e,
            d,
            k,
            shapes,
            hyps,
            base,
            tk: shape.tele.len(),
            body,
            pvals: (0..base).map(PV::Var).collect(),
            apart: HashMap::default(),
            lib,
        })
    }

    fn g(&self) -> &'a Globals {
        &self.e.globals
    }

    fn lib(&self) -> R<&Lib> {
        self.lib
            .as_ref()
            .ok_or_else(|| Stop::Skip("the core's logic isn't loaded yet".into()))
    }

    fn depth(&self) -> usize {
        self.pvals.len()
    }

    /// A term of the arm's shape as a value here (at the start).
    fn pv_of(&self, t: &Term, shape: &Shape) -> R<PV> {
        Ok(match t.strip_loc() {
            Term::Var(i) => {
                let l = shape.depth - 1 - i;
                let j = shape.tele.iter().position(|&x| x == l).ok_or_else(|| {
                    Stop::Skip("its left side mentions a variable it doesn't take".into())
                })?;
                PV::Var(j)
            }
            Term::Ctor(d, c, args) => PV::Ctor(
                *d,
                *c,
                args.iter()
                    .map(|a| self.pv_of(a, shape))
                    .collect::<R<_>>()?,
            ),
            Term::Nat(n) => PV::Nat(n.clone()),
            other => PV::Term(
                remap_shape(self.g(), other, shape, self.depth())?,
                self.depth(),
            ),
        })
    }

    /// `v` with every refined variable replaced by what it is.
    fn resolve(&self, v: &PV) -> PV {
        match v {
            PV::Var(l) => match &self.pvals[*l] {
                PV::Var(m) if m == l => v.clone(),
                other => self.resolve(&other.clone()),
            },
            PV::Ctor(d, c, args) => {
                PV::Ctor(*d, *c, args.iter().map(|a| self.resolve(a)).collect())
            }
            other => other.clone(),
        }
    }

    /// `v` as a term here.
    fn term(&self, v: &PV) -> R<Term> {
        let depth = self.depth();
        Ok(match self.resolve(v) {
            PV::Var(l) => Term::Var(depth - 1 - l),
            PV::Ctor(d, c, args) => Term::Ctor(
                d,
                c,
                args.iter()
                    .map(|a| Ok(Rc::new(self.term(a)?)))
                    .collect::<R<_>>()?,
            ),
            PV::Nat(n) => Term::Nat(n),
            PV::Term(t, at) => {
                // Refinements since it was made are substituted.
                let shifted = t.shift(self.g(), depth - at, 0)?;
                self.refine(&shifted)?
            }
            PV::Rec => return skip("`%rec` escaped into a proof term"),
        })
    }

    /// A term here with every refined variable replaced by what it is.
    fn refine(&self, t: &Term) -> R<Term> {
        let depth = self.depth();
        let pvals = &self.pvals;
        let any_refined = (0..depth).any(|l| !matches!(&pvals[l], PV::Var(m) if *m == l));
        if !any_refined {
            return Ok(t.clone());
        }
        let mut cache: Vec<Option<Term>> = vec![None; depth];
        for (l, slot) in cache.iter_mut().enumerate() {
            *slot = Some(match &pvals[l] {
                PV::Var(m) if *m == l => Term::Var(depth - 1 - l),
                other => self.term(&other.clone())?,
            });
        }
        remap(self.g(), t, depth, depth, &|l| cache[l].clone())?
            .ok_or_else(|| Stop::Skip("a refined term couldn't be read".into()))
    }

    /// The proof for the tree `t` (in a context of the definition's
    /// `fvals`), here.
    fn go(&mut self, t: &Term, fvals: &mut Vec<PV>, path: &mut Vec<u32>) -> R<Term> {
        self.g().budget.nesting("equations")?;
        if let Some(row) = self.d.row_at(path) {
            return self.leaf(row, fvals);
        }
        match t.strip_loc() {
            Term::Case(ix, data, branches) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                let nat = self.g().builtins.nat == Some(*data);
                match v {
                    PV::Ctor(d, c, args) if d == *data => {
                        let Some(body) = &branches[c].body else {
                            return skip("a branch it takes is impossible");
                        };
                        let mark = fvals.len();
                        fvals.extend(args);
                        path.push(c as u32);
                        let r = self.go(body, fvals, path);
                        path.pop();
                        fvals.truncate(mark);
                        r
                    }
                    PV::Nat(n) if nat => {
                        let (c, args) = if n.bits() == 0 {
                            (0, Vec::new())
                        } else {
                            (1, vec![PV::Nat(Rc::new((*n).clone() - 1u32))])
                        };
                        let Some(body) = &branches[c].body else {
                            return skip("a branch it takes is impossible");
                        };
                        let mark = fvals.len();
                        fvals.extend(args);
                        path.push(c as u32);
                        let r = self.go(body, fvals, path);
                        path.pop();
                        fvals.truncate(mark);
                        r
                    }
                    PV::Var(t) if t < self.tk || t >= self.base => {
                        if !self.g().data(*data).indices.is_empty() {
                            return skip(
                                "proving it needs a split on an indexed family, which stage 1a \
                                 doesn't make",
                            );
                        }
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (c, b) in branches.iter().enumerate() {
                            let Some(body) = &b.body else {
                                out.push(Branch {
                                    names: b.names.clone(),
                                    body: None,
                                });
                                continue;
                            };
                            let m = b.names.len();
                            let fields: Vec<PV> = (depth..depth + m).map(PV::Var).collect();
                            let saved = self.pvals.clone();
                            self.pvals.extend(fields.iter().cloned());
                            self.pvals[t] = PV::Ctor(*data, c, fields.clone());
                            let mark = fvals.len();
                            fvals.extend(fields);
                            path.push(c as u32);
                            let r = self.go(body, fvals, path);
                            path.pop();
                            fvals.truncate(mark);
                            self.pvals = saved;
                            out.push(Branch {
                                names: b.names.clone(),
                                body: Some(Rc::new(r?)),
                            });
                        }
                        Ok(Term::Case(depth - 1 - t, *data, out.into()))
                    }
                    _ => skip(
                        "the definition's case tree is stuck on something that isn't a variable",
                    ),
                }
            }
            Term::NumCase(ix, arms, default) => {
                let x = fvals.len() - 1 - ix;
                let v = self.resolve(&fvals[x]);
                match v {
                    PV::Nat(n) => match arms.iter().position(|a| *a.value == *n) {
                        Some(i) => {
                            path.push(i as u32);
                            let r = self.go(&arms[i].body, fvals, path);
                            path.pop();
                            r
                        }
                        None => {
                            path.push(arms.len() as u32);
                            let r = self.go(default, fvals, path);
                            path.pop();
                            r
                        }
                    },
                    PV::Var(t) => {
                        let known = self.apart.get(&t).cloned().unwrap_or_default();
                        if arms.iter().all(|a| known.contains(&a.value)) {
                            path.push(arms.len() as u32);
                            let r = self.go(default, fvals, path);
                            path.pop();
                            return r;
                        }
                        let depth = self.depth();
                        let mut out = Vec::new();
                        for (i, a) in arms.iter().enumerate() {
                            let saved = self.pvals.clone();
                            self.pvals[t] = PV::Nat(a.value.clone());
                            path.push(i as u32);
                            let r = self.go(&a.body, fvals, path);
                            path.pop();
                            self.pvals = saved;
                            out.push(NumArm {
                                value: a.value.clone(),
                                body: Rc::new(r?),
                            });
                        }
                        let saved = self.apart.get(&t).cloned();
                        self.apart
                            .entry(t)
                            .or_default()
                            .extend(arms.iter().map(|a| (*a.value).clone()));
                        path.push(arms.len() as u32);
                        let r = self.go(default, fvals, path);
                        path.pop();
                        match saved {
                            Some(s) => {
                                self.apart.insert(t, s);
                            }
                            None => {
                                self.apart.remove(&t);
                            }
                        }
                        Ok(Term::NumCase(depth - 1 - t, out.into(), Rc::new(r?)))
                    }
                    _ => skip(
                        "the definition's number case is stuck on something that isn't a variable",
                    ),
                }
            }
            _ => skip("a leaf of the definition's case tree belongs to no arm"),
        }
    }

    /// The proof at a leaf of row `row`.
    fn leaf(&mut self, row: usize, fvals: &[PV]) -> R<Term> {
        if row == self.k {
            return match self.d.kind {
                Kind::Decreasing { unfold, .. } => {
                    let mut args = Vec::new();
                    for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
                        if let Some(i) = self.d.param_of_tree_level(level) {
                            args.push((self.term(v)?, self.d.binders[i].icit));
                        }
                    }
                    Ok(apps(Term::Def(unfold), args))
                }
                _ => Ok(Term::Refl),
            };
        }
        if row > self.k {
            return skip("a later arm's leaf is reached from its left side");
        }
        // An earlier row: its hypothesis is refuted here.
        let (i, h) = self
            .hyps
            .iter()
            .enumerate()
            .find(|(_, h)| match h {
                Hyp::Overlap { row: r, .. } => *r == row,
                Hyp::Listed { rows, .. } => rows.iter().any(|(r, _)| *r == row),
            })
            .ok_or_else(|| {
                Stop::Skip("an earlier arm is reached that no hypothesis rules out".into())
            })?;
        let other = self.shapes[row]
            .as_ref()
            .map_err(|e| Stop::Skip(e.clone()))?;
        // The earlier row's variables, as they are here.
        let mut jvals: HashMap<usize, PV> = HashMap::default();
        for (level, v) in fvals.iter().enumerate().take(self.d.tree_params()) {
            if let Some(p) = self.d.param_of_tree_level(level) {
                self.match_pv(&other.lhs[p], other.depth, v, &mut jvals)?;
            }
        }
        let depth = self.depth();
        let hyp = Term::Var(depth - 1 - (self.tk + i));
        let void = match h {
            Hyp::Overlap { vars, eqs, .. } => {
                let mut args = Vec::new();
                for v in vars {
                    let pv = jvals.get(v).ok_or_else(|| {
                        Stop::Skip("an earlier arm's variable has no value here".into())
                    })?;
                    args.push((self.term(pv)?, Icit::Explicit));
                }
                for (lk, s) in eqs {
                    let j = self.shapes_tele(lk).ok_or_else(|| {
                        Stop::Skip("an equation's variable isn't the arm's".into())
                    })?;
                    let y = self.pv_in(s, other, &jvals)?;
                    args.push((self.eq_proof(&PV::Var(j), &y)?, Icit::Explicit));
                }
                apps(hyp, args)
            }
            Hyp::Listed { level, rows } => {
                let j = self
                    .shapes_tele(level)
                    .ok_or_else(|| Stop::Skip("an equation's variable isn't the arm's".into()))?;
                let x = self.resolve(&PV::Var(j));
                let at = rows
                    .iter()
                    .position(|(r, _)| *r == row)
                    .expect("found above");
                let c = rows[at].1;
                let lit = PV::Ctor(
                    self.lib()?.char,
                    0,
                    vec![
                        PV::Nat(Rc::new(BigUint::from(u32::from(c)))),
                        PV::Term(Term::Refl, depth),
                    ],
                );
                // `List.Any (y => y = x)`: the element first.
                let or = self.lib()?.or;
                let mut proof = Term::ctor(or, 0, vec![self.eq_proof(&lit, &x)?]);
                for _ in 0..at {
                    proof = Term::ctor(or, 1, vec![proof]);
                }
                Term::app(hyp, proof)
            }
        };
        let goal = self.refine(&self.body.shift(self.g(), depth - self.base, 0)?)?;
        Ok(apps(
            Term::Def(self.lib()?.exfalso),
            [(goal, Icit::Implicit), (void, Icit::Explicit)],
        ))
    }

    /// The position in the equation's variables of the arm's level `l`.
    fn shapes_tele(&self, l: &usize) -> Option<usize> {
        self.shapes[self.k]
            .as_ref()
            .ok()?
            .tele
            .iter()
            .position(|x| x == l)
    }

    /// Matches an earlier row's left-side term (at `depth`) with a value
    /// here, solving its variables.
    fn match_pv(&self, t: &Term, depth: usize, v: &PV, out: &mut HashMap<usize, PV>) -> R<()> {
        let v = self.resolve(v);
        match t.strip_loc() {
            Term::Var(i) => {
                out.insert(depth - 1 - i, v);
                Ok(())
            }
            Term::Ctor(d, c, args) => match v {
                PV::Ctor(d2, c2, vs) if *d == d2 && *c == c2 => {
                    for (a, w) in args.iter().zip(&vs) {
                        self.match_pv(a, depth, w, out)?;
                    }
                    Ok(())
                }
                PV::Nat(n) if self.g().builtins.nat == Some(*d) => {
                    let (c2, vs) = if n.bits() == 0 {
                        (0, vec![])
                    } else {
                        (1, vec![PV::Nat(Rc::new((*n).clone() - 1u32))])
                    };
                    if c2 != *c {
                        return skip("an earlier arm's leaf doesn't match its patterns");
                    }
                    for (a, w) in args.iter().zip(&vs) {
                        self.match_pv(a, depth, w, out)?;
                    }
                    Ok(())
                }
                _ => skip("an earlier arm's leaf doesn't match its patterns"),
            },
            _ => Ok(()),
        }
    }

    /// A term of an earlier row's shape, with its variables' values here.
    fn pv_in(&self, t: &Term, other: &Shape, jvals: &HashMap<usize, PV>) -> R<PV> {
        Ok(match t.strip_loc() {
            Term::Var(i) => jvals
                .get(&(other.depth - 1 - i))
                .cloned()
                .ok_or_else(|| Stop::Skip("an earlier arm's variable has no value here".into()))?,
            Term::Ctor(d, c, args) => PV::Ctor(
                *d,
                *c,
                args.iter()
                    .map(|a| self.pv_in(a, other, jvals))
                    .collect::<R<_>>()?,
            ),
            Term::Nat(n) => PV::Nat(n.clone()),
            Term::Refl => PV::Term(Term::Refl, self.depth()),
            _ => return skip("an overlap's pattern isn't constructors and variables"),
        })
    }

    /// A proof of `x = y` here: `rfl` when they're the same up to proofs
    /// of `Bool` equations in constructors' fields (a character `MkChar k
    /// p` against the literal `MkChar k rfl`), and then one `J` along
    /// `Bool.uniqueEq` for each such field that differs, each moving the
    /// right side's field from the left side's proof to its own.
    fn eq_proof(&self, x: &PV, y: &PV) -> R<Term> {
        // The left side as the motive states it: a variable as itself, so
        // the equation's type is its (a constructor alone has none).
        let lx_var = match x {
            PV::Var(l) => Some(Term::Var(self.depth() - 1 - l)),
            _ => None,
        };
        let x = self.resolve(x);
        let y = self.resolve(y);
        let mut diffs: Vec<Diff> = Vec::new();
        if !self.differ(&x, &y, &mut Vec::new(), &mut diffs)? {
            return skip("an overlap's equation isn't true by computation here");
        }
        let depth = self.depth();
        let g = self.g();
        let lx = match lx_var {
            Some(v) => v,
            None => self.term(&x)?,
        };
        let mut proof = Term::Refl;
        // The right side so far: the left side's proofs at the fields not
        // moved yet.
        let mut right = x.clone();
        for diff in &diffs {
            let unique = apps(
                Term::Def(self.lib()?.unique),
                [
                    (diff.a.clone(), Icit::Explicit),
                    (diff.b.clone(), Icit::Explicit),
                    (self.term(&diff.left)?, Icit::Explicit),
                    (self.term(&diff.right)?, Icit::Explicit),
                ],
            );
            // `q e => x = right[q]`, under `q` and `e`.
            let hole = PV::Term(Term::Var(1), depth + 2);
            let with_q = replace_at(&right, &diff.path, hole);
            let motive_body = Term::Eq(
                None,
                Rc::new(lx.shift(g, 2, 0)?),
                Rc::new(self.term_at(&with_q, depth + 2)?),
            );
            let motive = Term::Lam(
                "q".into(),
                Icit::Explicit,
                Rc::new(Term::Lam("e".into(), Icit::Explicit, Rc::new(motive_body))),
            );
            proof = Term::J(Rc::new(motive), Rc::new(proof), Rc::new(unique));
            right = replace_at(&right, &diff.path, diff.right.clone());
        }
        Ok(proof)
    }

    /// Whether `x` and `y` are equal but for proofs of `Bool` equations in
    /// fields of parameterless constructors (each recorded, with its path
    /// and the equation's sides); `false` if they differ otherwise.
    fn differ(&self, x: &PV, y: &PV, path: &mut Vec<usize>, out: &mut Vec<Diff>) -> R<bool> {
        let g = self.g();
        let x = nat_as_ctor(g, x);
        let y = nat_as_ctor(g, y);
        if same_pv(&x, &y) {
            return Ok(true);
        }
        match (&x, &y) {
            (PV::Ctor(d, c, xs), PV::Ctor(d2, c2, ys))
                if d == d2 && c == c2 && xs.len() == ys.len() =>
            {
                let data = g.data(*d);
                for (i, (a, b)) in xs.iter().zip(ys).enumerate() {
                    path.push(i);
                    let fine = self.differ(a, b, path, out)?;
                    path.pop();
                    if fine {
                        continue;
                    }
                    // A proof field of a `Bool` equation: any two of its
                    // proofs are equal by `Bool.uniqueEq`.
                    if !data.params.is_empty() {
                        return Ok(false);
                    }
                    let mut env = Vec::new();
                    for f in &xs[..i] {
                        let Some(t) = closed_term(f) else {
                            return Ok(false);
                        };
                        env.push(eval(g, &[], &t)?);
                    }
                    let ty = eval(g, &env, &data.ctors[*c].fields[i].1)?;
                    let Value::Eq(ty, l, r) = force(g, ty)? else {
                        return Ok(false);
                    };
                    if !matches!(force(g, (*ty).clone())?, Value::Data(b, _) if g.registry.is_data(Builtin::Bool, b))
                    {
                        return Ok(false);
                    }
                    let depth = self.depth();
                    let mut p = path.clone();
                    p.push(i);
                    out.push(Diff {
                        path: p,
                        left: a.clone(),
                        right: b.clone(),
                        a: stitchwort_core::value::quote(g, depth, &l)?,
                        b: stitchwort_core::value::quote(g, depth, &r)?,
                    });
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// `v` as a term at `depth` (at least this context's).
    fn term_at(&self, v: &PV, depth: usize) -> R<Term> {
        let here = self.depth();
        match v {
            PV::Term(t, at) if *at >= here => Ok(t.shift(self.g(), depth - at, 0)?),
            PV::Ctor(d, c, args) => Ok(Term::Ctor(
                *d,
                *c,
                args.iter()
                    .map(|a| Ok(Rc::new(self.term_at(a, depth)?)))
                    .collect::<R<_>>()?,
            )),
            _ => Ok(self.term(v)?.shift(self.g(), depth - here, 0)?),
        }
    }
}

/// A field where two sides of an equation differ in their proofs of a
/// `Bool` equation `a = b`.
struct Diff {
    path: Vec<usize>,
    left: PV,
    right: PV,
    a: Term,
    b: Term,
}

/// `v` with the field at `path` replaced by `with`.
fn replace_at(v: &PV, path: &[usize], with: PV) -> PV {
    match (path.split_first(), v) {
        (None, _) => with,
        (Some((i, rest)), PV::Ctor(d, c, args)) => {
            let mut args = args.clone();
            args[*i] = replace_at(&args[*i], rest, with);
            PV::Ctor(*d, *c, args)
        }
        _ => v.clone(),
    }
}

/// `v` as a closed term, if it mentions no variable.
fn closed_term(v: &PV) -> Option<Term> {
    match v {
        PV::Var(_) | PV::Rec => None,
        PV::Ctor(d, c, args) => Some(Term::Ctor(
            *d,
            *c,
            args.iter()
                .map(|a| closed_term(a).map(Rc::new))
                .collect::<Option<_>>()?,
        )),
        PV::Nat(n) => Some(Term::Nat(n.clone())),
        PV::Term(t, _) => closed(t).then(|| t.clone()),
    }
}

/// A number as `Zero` or `Succ` of a number, to compare with constructors.
fn nat_as_ctor(g: &Globals, v: &PV) -> PV {
    match v {
        PV::Nat(n) => match g.builtins.nat {
            Some(nat) if n.bits() == 0 => PV::Ctor(nat, 0, Vec::new()),
            Some(nat) => PV::Ctor(nat, 1, vec![PV::Nat(Rc::new((**n).clone() - 1u32))]),
            None => v.clone(),
        },
        _ => v.clone(),
    }
}

fn same_pv(a: &PV, b: &PV) -> bool {
    match (a, b) {
        (PV::Var(x), PV::Var(y)) => x == y,
        // A number and the constructors it stands for.
        (PV::Nat(n), PV::Ctor(_, c, args)) | (PV::Ctor(_, c, args), PV::Nat(n)) => match c {
            0 => n.bits() == 0 && args.is_empty(),
            1 if n.bits() > 0 && args.len() == 1 => {
                same_pv(&PV::Nat(Rc::new((**n).clone() - 1u32)), &args[0])
            }
            _ => false,
        },
        (PV::Ctor(d, c, xs), PV::Ctor(d2, c2, ys)) => {
            d == d2
                && c == c2
                && xs.len() == ys.len()
                && xs.iter().zip(ys).all(|(x, y)| same_pv(x, y))
        }
        (PV::Nat(x), PV::Nat(y)) => x == y,
        (PV::Term(x, dx), PV::Term(y, dy)) => dx == dy && stitchwort_core::value::same_term(x, y),
        _ => false,
    }
}

/// Whether `name` is a generated equation's: `f.eqK` or `f.eqK.orN` (the
/// names are reserved for them, D2176).
pub fn is_equation_name(name: &str) -> bool {
    let number = |s: &str, prefix: &str| {
        s.strip_prefix(prefix)
            .is_some_and(|d| !d.is_empty() && d.chars().all(|c| c.is_ascii_digit()))
    };
    let parts: Vec<&str> = name.split('.').collect();
    match parts.as_slice() {
        [.., owner, last] if !owner.is_empty() && number(last, "eq") => parts.len() >= 2,
        [.., owner, eq, or] if !owner.is_empty() && number(eq, "eq") && number(or, "or") => {
            parts.len() >= 3
        }
        _ => false,
    }
}

// ------------------------------------------------------------ E-NO-EQUATION

/// `E-NO-EQUATION` if `name` is an equation the source implies that wasn't
/// generated, with the reason (D2176, D2185).
pub(crate) fn no_equation(e: &Elaborator, name: &ast::Name) -> Option<Diagnostic> {
    let (owner, suffix) = reserved_suffix(&name.text)?;
    let Some((Global::Def(f), _)) = e.named(owner) else {
        return None;
    };
    let def = e.globals.def(*f);
    let lazy = if def.theorem {
        Some("a theorem's arms have no equations: nothing unfolds a proof".to_string())
    } else if def.instance {
        Some(
            "an instance's arms have no equations: write the method as a named `def` the \
             instance points to, which gets them"
                .to_string(),
        )
    } else {
        None
    };
    let why = match lazy {
        Some(why) => why,
        None => e
            .equation_skips
            .iter()
            .rev()
            .find(|(g, s, _)| g == f && s == suffix)?
            .2
            .clone(),
    };
    Some(
        Diagnostic::error(
            "E-NO-EQUATION",
            format!("`{}.{suffix}` isn't generated", e.globals.def(*f).name),
        )
        .with_label(name.span, why)
        .with_note(
            "an equation for each arm is generated where it can be stated and proved \
             (docs/proposals/function-equations.md); prove this one by hand, or use \
             `f.unfold` and a `match`",
        ),
    )
}

impl Elaborator {
    /// The equations the source implies that weren't generated, by key,
    /// with the reason.
    pub fn equation_skips(&self) -> &[(DefId, String, String)] {
        &self.equation_skips
    }
}
