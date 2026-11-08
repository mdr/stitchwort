//! Which handler clauses could answer their operation where it is performed
//! (docs/proposals/operations-in-place.md §2.3, stage A). A measurement
//! and recognition pass only: nothing here changes what a backend does.
//!
//! A `handle` is elaborated to a fold whose step is
//! `handlePlus (A.%elim clause₁ … clauseₙ) forward`, each clause `x => k =>
//! body`. Each clause gets a [`Kind`]:
//!
//! - [`Kind::Forward`]: `bind (Call O (r => Done r)) (y => k y)` (or `k`
//!   itself as the continuation), where `O` is one operation of the outer
//!   row (`L`/`R` around an operation's constructor) given the clause's own
//!   argument or `()`. `k (Parse.span passes)` in `optional` is this.
//! - [`Kind::Tail`]: every occurrence of `k` is `k e` in tail position,
//!   following `let`s, applied lambdas, `if`, `Decidable.elim`, case trees,
//!   lifted `match`es (where the caller supplies their bodies) and the
//!   continuations of `bind`, `bindIn`, `bindDv` and `callD`; there is at
//!   least one.
//! - [`Kind::Abort`]: `k` doesn't occur.
//! - [`Kind::General`]: anything else (`k` twice in sequence, under a
//!   lambda, stored, or not last).
//!
//! A state-passing fold that stage 4d runs as a loop ([`crate::fusion`]) is
//! classified on fusion's own rewrite of its clauses, so the two can't
//! disagree about what a tail resumption is: a clause whose `k v s′` all
//! became jumps and that has no other `k` is Tail, one with neither is
//! Abort, and one that still mentions `k` is General. An unfused fold whose
//! clauses return a function of a state (an open-row state handler, say)
//! has `k` under that function's lambda, so its resuming clauses are
//! General here, as they are for the runtime today.
//!
//! The generated forward gets a [`ForwardShape`] from its head, one per
//! branch of the elaborator's construction (`crates/elab/src/effects.rs`,
//! "Everything else is forwarded").
//!
//! [`census`] counts the kinds over a set of definitions, with where each
//! fold's call sits ([`Position`]): the in-place design runs an operation in
//! place only through handlers whose fold call hands its result straight
//! on (the consumer link, §2.2), and a fold that is a `let`'s value or an
//! argument can never be one of those, whatever calls its definition.

use std::collections::BTreeMap;
use std::rc::Rc;

use stitchwort_core::budget::Result;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Icit;
use stitchwort_core::{DataId, DefId, Ev, Term};

use crate::erasure::{def_shape, is_done_continuation};
use crate::fusion::{MatchBodies, StateFusion, inline, is_lifted_match, spine_icit, strip};

/// How deeply a clause's tail positions are followed.
const MAX_DEPTH: usize = 200;

/// How many lifted `match`es are inlined while classifying one clause.
const MAX_INLINED: usize = 16;

/// What a handler clause does with its continuation `k`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Kind {
    /// Performs one outer operation with its own argument or `()` and
    /// resumes with the answer.
    Forward,
    /// Resumes once, as its last step, on every path that resumes.
    Tail,
    /// Never resumes.
    Abort,
    /// Anything else.
    General,
}

/// The shape of a fold step's generated forward of the other abilities.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ForwardShape {
    /// `o k => Call (sigInject m o) (y => k (sigReply m o y))`.
    Plain,
    /// The outer row is a bare row variable: `lowerIn e (Call …)`, or
    /// `runPure (Call …)` once the empty row has been specialised in.
    Bare,
    /// The outer row is partial: `bindD (lift (Call …)) …`.
    Partial,
    /// The outer row has a divergence index: `callD d row …`.
    Divergence,
    /// None of these.
    Other,
}

/// Which fold a `handle` became.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fold {
    /// `foldComp`, run by the effect runtime's fold natives.
    Comp,
    /// `foldCompD` at a constant divergence index.
    IndexedConstant,
    /// `foldCompD` at a divergence index that is a variable: the runtime
    /// calls the library's `foldCompD`, whose own `foldComp` gets this step
    /// as an opaque function value.
    IndexedVariable,
}

/// One fold's clauses, classified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Classified {
    pub fold: Fold,
    /// Run as a loop by stage 4d's state fusion.
    pub state: bool,
    /// Each operation clause's kind, in the order of the ability's
    /// operations.
    pub clauses: Vec<Kind>,
    pub forward: ForwardShape,
}

/// What the classification needs to know about the core.
pub struct Classifier {
    fold: DefId,
    fold_d: Option<DefId>,
    comp: DataId,
    plus: DataId,
    unit: Option<DataId>,
    handle_plus: DefId,
    handle_plus_mask: Vec<bool>,
    /// Sequencing forms whose last argument is the continuation, with how
    /// many arguments they take when saturated: `bind`, `bindIn`, `bindDv`
    /// and `callD`.
    sequences: Vec<(DefId, usize)>,
    run_pure: DefId,
    lower_in: Option<DefId>,
    bind_d: Option<DefId>,
    call_d: Option<DefId>,
    if_then_else: Option<DefId>,
    elim_dec: Option<DefId>,
    fusion: Option<StateFusion>,
}

impl Classifier {
    pub fn new(g: &Ev) -> Option<Classifier> {
        let r = &g.env.registry();
        let handle_plus = r.loaded_def(Builtin::HandlePlus)?;
        let handle_plus_mask = def_shape(g, handle_plus, false).ok()?.mask().to_vec();
        let params = |id: DefId| def_shape(g, id, false).ok().map(|s| s.params.len());
        let sequences = [
            Builtin::Bind,
            Builtin::BindIn,
            Builtin::BindDv,
            Builtin::CallD,
        ]
        .into_iter()
        .filter_map(|b| {
            let id = r.loaded_def(b)?;
            Some((id, params(id)?))
        })
        .collect();
        Some(Classifier {
            fold: r.loaded_def(Builtin::FoldComp)?,
            fold_d: r.loaded_def(Builtin::FoldCompD),
            comp: r.loaded_data(Builtin::Comp)?,
            plus: r.loaded_data(Builtin::Plus)?,
            unit: r.loaded_data(Builtin::UnitType),
            handle_plus,
            handle_plus_mask,
            sequences,
            run_pure: r.loaded_def(Builtin::RunPure)?,
            lower_in: r.loaded_def(Builtin::LowerIn),
            bind_d: r.loaded_def(Builtin::BindD),
            call_d: r.loaded_def(Builtin::CallD),
            if_then_else: r.loaded_def(Builtin::IfThenElse),
            elim_dec: r.loaded_def(Builtin::ElimDec),
            fusion: StateFusion::new(g),
        })
    }

    /// Whether `id` is a fold this pass classifies.
    pub fn is_fold(&self, id: DefId) -> bool {
        id == self.fold || Some(id) == self.fold_d
    }

    /// The fold `head args` classified, if `head` is `foldComp` or
    /// `foldCompD` applied to at least its step, and the step has the
    /// elaborator's shape. `bodies` gives lifted `match`es' case trees, as
    /// for [`StateFusion::fuse`].
    pub fn classify(
        &self,
        g: &Ev,
        head: DefId,
        args: &[&Term],
        bodies: Option<MatchBodies>,
    ) -> Result<Option<Classified>> {
        // `foldComp [op] [res] [a] [r] done call comp`; `foldCompD [op1]
        // [res1] [a] [b] d out done call comp`.
        let (fold, step) = if head == self.fold {
            (Fold::Comp, 5)
        } else if Some(head) == self.fold_d {
            let constant = args
                .get(4)
                .is_some_and(|d| matches!(strip(d), Term::Ctor(..)));
            let fold = if constant {
                Fold::IndexedConstant
            } else {
                Fold::IndexedVariable
            };
            (fold, 7)
        } else {
            return Ok(None);
        };
        let Some(step_term) = args.get(step) else {
            return Ok(None);
        };
        let Some((clauses, forward)) = self.step_parts(g, step_term) else {
            return Ok(None);
        };
        let forward = self.forward_shape(forward);
        if fold == Fold::Comp
            && let Some(fusion) = &self.fusion
            && let Some(fused) = fusion.fuse(g, args, bodies)?
            && let Some((fused_clauses, _)) = self.step_parts(g, &fused.call)
        {
            // Each is `x => k => jump => s => body′`, `k` Var(2) in `body′`.
            let clauses = fused_clauses
                .iter()
                .map(|clause| {
                    let body = peel(clause, 4);
                    match body {
                        Some(b) if b.mentions(2) => Kind::General,
                        Some(b) if b.mentions(1) => Kind::Tail,
                        Some(_) => Kind::Abort,
                        None => Kind::General,
                    }
                })
                .collect();
            return Ok(Some(Classified {
                fold,
                state: true,
                clauses,
                forward,
            }));
        }
        let mut kinds = Vec::with_capacity(clauses.len());
        for clause in &clauses {
            kinds.push(self.clause(g, clause, bodies)?);
        }
        Ok(Some(Classified {
            fold,
            state: false,
            clauses: kinds,
            forward,
        }))
    }

    /// The runtime clauses of `handlePlus [5 implicit] (elim [implicit…]
    /// clause…) forward`, and the forward. The runtime arguments are told
    /// by erasure, not by how they're applied.
    fn step_parts<'t>(&self, g: &Ev, step: &'t Term) -> Option<(Vec<&'t Term>, &'t Term)> {
        let (head, plus_args) = spine_icit(step)?;
        if !matches!(head, Term::Def(id) if *id == self.handle_plus)
            || plus_args.len() > self.handle_plus_mask.len()
        {
            return None;
        }
        let runtime: Vec<&Term> = plus_args
            .iter()
            .enumerate()
            .filter(|(i, _)| !self.handle_plus_mask[*i])
            .map(|(_, (a, _))| *a)
            .collect();
        // The step is `handlePlus` given its two clauses' functions and no
        // operation yet.
        let [elim, forward] = runtime[..] else {
            return None;
        };
        if !std::ptr::eq(forward, plus_args.last()?.0) {
            return None;
        }
        let (Term::Def(elim_id), elim_args) = spine_icit(elim)? else {
            return None;
        };
        let elim_mask = def_shape(g, *elim_id, false).ok()?.mask().to_vec();
        if elim_args.len() > elim_mask.len() {
            return None;
        }
        let clauses = elim_args
            .iter()
            .enumerate()
            .filter(|(i, _)| !elim_mask[*i])
            .map(|(_, (a, _))| *a)
            .collect();
        Some((clauses, forward))
    }

    fn forward_shape(&self, forward: &Term) -> ForwardShape {
        let Some(body) = peel(forward, 2) else {
            return ForwardShape::Other;
        };
        let body = strip(body);
        if matches!(body, Term::Ctor(d, 1, _) if *d == self.comp) {
            return ForwardShape::Plain;
        }
        match body.spine().0 {
            Term::Def(id) if Some(*id) == self.lower_in || *id == self.run_pure => {
                ForwardShape::Bare
            }
            Term::Def(id) if Some(*id) == self.bind_d => ForwardShape::Partial,
            Term::Def(id) if Some(*id) == self.call_d => ForwardShape::Divergence,
            _ => ForwardShape::Other,
        }
    }

    /// One clause `x => k => body`, not state-passing.
    fn clause(&self, g: &Ev, clause: &Term, bodies: Option<MatchBodies>) -> Result<Kind> {
        let Some(body) = peel(clause, 2) else {
            return Ok(Kind::General);
        };
        if !body.mentions(0) {
            return Ok(Kind::Abort);
        }
        if self.forward(g, body) {
            return Ok(Kind::Forward);
        }
        let mut inlined = 0;
        Ok(if self.tail(g, body, 0, bodies, &mut inlined)? {
            Kind::Tail
        } else {
            Kind::General
        })
    }

    /// Whether `body` (under `x` and `k`) performs one outer operation of
    /// `x` or `()` and resumes with its answer.
    fn forward(&self, g: &Ev, body: &Term) -> bool {
        let Some((head, args)) = spine_icit(body) else {
            return false;
        };
        let Term::Def(id) = head else {
            return false;
        };
        let Some(&(_, arity)) = self.sequences.iter().find(|(s, _)| s == id) else {
            return false;
        };
        if args.len() != arity {
            return false;
        }
        let next = args[arity - 1].0;
        let continues = match strip(next) {
            Term::Var(0) => true,
            Term::Lam(_, _, b) => matches!(strip(b), Term::App(f, y, _)
                if matches!(strip(f), Term::Var(1)) && matches!(strip(y), Term::Var(0))),
            _ => false,
        };
        if !continues {
            return false;
        }
        // `callD [b] d row o k`, or `bind… (Call o (r => Done r)) k`.
        let op = if Some(*id) == self.call_d {
            args[arity - 2].0
        } else {
            match strip(args[arity - 2].0) {
                Term::Ctor(d, 1, fields)
                    if *d == self.comp
                        && matches!(strip(&fields[1]), Term::Lam(_, _, b) if is_done_continuation(g, b)) =>
                {
                    &fields[0]
                }
                _ => return false,
            }
        };
        self.own_operation(op)
    }

    /// Whether `op` is an operation injected into a row (`L`s and `R`s
    /// around a constructor) whose fields are the clause's argument `x`
    /// (Var(1) under `k`) or `()`.
    fn own_operation(&self, op: &Term) -> bool {
        let mut op = strip(op);
        let mut injected = false;
        while let Term::Ctor(d, _, fields) = op
            && *d == self.plus
            && fields.len() == 1
        {
            injected = true;
            op = strip(&fields[0]);
        }
        let Term::Ctor(_, _, fields) = op else {
            return false;
        };
        injected
            && fields.iter().all(|f| match strip(f) {
                Term::Var(1) => true,
                Term::Ctor(d, 0, unit) => Some(*d) == self.unit && unit.is_empty(),
                _ => false,
            })
    }

    /// Whether every occurrence of `k` (Var(`depth`)) in `term` is a
    /// resumption in tail position.
    fn tail(
        &self,
        g: &Ev,
        term: &Term,
        depth: usize,
        bodies: Option<MatchBodies>,
        inlined: &mut usize,
    ) -> Result<bool> {
        let term = strip(term);
        if !term.mentions(depth) {
            return Ok(true);
        }
        if depth > MAX_DEPTH {
            return Ok(false);
        }
        let fresh = |t: &Term, extra: usize| !t.mentions(depth + extra);
        match term {
            Term::App(f, e, _) if matches!(strip(f), Term::Var(i) if *i == depth) => {
                return Ok(fresh(e, 0));
            }
            Term::Let(_, _, value, body, _) => {
                return Ok(fresh(value, 0) && self.tail(g, body, depth + 1, bodies, inlined)?);
            }
            Term::App(f, value, _) if matches!(strip(f), Term::Lam(..)) => {
                let Term::Lam(_, _, body) = strip(f) else {
                    unreachable!("matched above")
                };
                return Ok(fresh(value, 0) && self.tail(g, body, depth + 1, bodies, inlined)?);
            }
            Term::Case(_, _, branches) => {
                for branch in branches.iter() {
                    if let Some(body) = &branch.body
                        && !self.tail(g, body, depth + branch.names.len(), bodies, inlined)?
                    {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
            Term::NumCase(_, arms, default) => {
                for arm in arms.iter() {
                    if !self.tail(g, &arm.body, depth, bodies, inlined)? {
                        return Ok(false);
                    }
                }
                return self.tail(g, default, depth, bodies, inlined);
            }
            _ => {}
        }
        let Some((Term::Def(id), args)) = spine_icit(term) else {
            return Ok(false);
        };
        let args: Vec<&Term> = args.iter().map(|(a, _)| *a).collect();
        // A sequence: everything before the continuation runs first and
        // mustn't resume; the continuation's result is the clause's.
        if let Some(&(_, arity)) = self.sequences.iter().find(|(s, _)| s == id)
            && args.len() == arity
        {
            let (next, before) = args.split_last().expect("a continuation");
            if !before.iter().all(|a| fresh(a, 0)) {
                return Ok(false);
            }
            return match strip(next) {
                Term::Var(i) if *i == depth => Ok(true),
                Term::Lam(_, _, body) => self.tail(g, body, depth + 1, bodies, inlined),
                _ => Ok(false),
            };
        }
        // `Bool.ifThenElse [a] c (_ => t) (_ => e)`, `Decidable.elim [p] [a]
        // d (h => t) (r => e)`.
        let branches = if Some(*id) == self.if_then_else && args.len() == 4 {
            Some(2)
        } else if Some(*id) == self.elim_dec && args.len() == 5 {
            Some(3)
        } else {
            None
        };
        if let Some(at) = branches {
            if !args[..at].iter().all(|a| fresh(a, 0)) {
                return Ok(false);
            }
            for branch in &args[at..] {
                let Term::Lam(_, _, body) = strip(branch) else {
                    return Ok(false);
                };
                if !self.tail(g, body, depth + 1, bodies, inlined)? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        // A lifted `match` given `k`: its arms, in place.
        if let Some(bodies) = bodies
            && *inlined < MAX_INLINED
            && is_lifted_match(g, *id)
            && args.len() == g.def(*id).arity()
            && let Some(tree) = bodies(*id, &args)
        {
            *inlined += 1;
            let inlined_term = inline(g, &tree, &args)?;
            return self.tail(g, &inlined_term, depth, Some(bodies), inlined);
        }
        Ok(false)
    }
}

/// The body under `n` lambdas, if `term` starts with that many.
fn peel(term: &Term, n: usize) -> Option<&Term> {
    let mut term = strip(term);
    for _ in 0..n {
        let Term::Lam(_, _, body) = term else {
            return None;
        };
        term = strip(body);
    }
    Some(term)
}

/// Where a fold's call sits in the body it's in, for the consumer link
/// (operations-in-place.md §2.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Position {
    /// Its result goes straight to the definition's own result or to an
    /// enclosing activation: the tail of the body, the first argument of a
    /// `bind` in such a position, a continuation's body, a `handle`'s body
    /// or clause, the body of `runPure` or `translate`. Whether the
    /// definition's own frame is linked is a run-time question.
    Consuming,
    /// The value of a `let` (or of an applied lambda's argument).
    LetValue,
    /// Under a row helper (`bindIn`, `liftIn`, `lowerIn`, `widenIn`,
    /// `bindDv`, `liftD`, `doneD`, `callD`), an ordinary call to the
    /// in-place design until stage E.
    RowHelper,
    /// Any other argument, a constructor's field, or under a lambda that
    /// isn't a continuation.
    Other,
}

/// A fold found by [`census`].
#[derive(Clone, Debug)]
pub struct Found {
    /// The definition it's in.
    pub def: DefId,
    /// In the definition's empty-row variant, not its generic body.
    pub variant: bool,
    pub position: Position,
    /// `None` if its step doesn't have the elaborator's shape.
    pub classified: Option<Classified>,
}

/// The folds in `body` (under its definition's parameters), with where
/// each sits.
pub fn folds_in(
    g: &Ev,
    classifier: &Classifier,
    def: DefId,
    variant: bool,
    body: &Term,
    bodies: Option<MatchBodies>,
    out: &mut Vec<Found>,
) -> Result<()> {
    let helpers: Vec<DefId> = [
        Builtin::BindIn,
        Builtin::LiftIn,
        Builtin::LowerIn,
        Builtin::WidenIn,
        Builtin::BindDv,
        Builtin::LiftD,
        Builtin::DoneD,
        Builtin::CallD,
    ]
    .into_iter()
    .filter_map(|b| g.env.registry().loaded_def(b))
    .collect();
    let r = &g.env.registry();
    let scan = Scan {
        classifier,
        def,
        variant,
        bodies,
        helpers,
        bind: r.loaded_def(Builtin::Bind),
        passes_body: [Builtin::RunPure, Builtin::Translate]
            .into_iter()
            .filter_map(|b| r.loaded_def(b))
            .collect(),
    };
    scan.walk(g, body, Position::Consuming, 0, out)
}

struct Scan<'a> {
    classifier: &'a Classifier,
    def: DefId,
    variant: bool,
    bodies: Option<MatchBodies<'a>>,
    helpers: Vec<DefId>,
    bind: Option<DefId>,
    passes_body: Vec<DefId>,
}

impl Scan<'_> {
    fn walk(
        &self,
        g: &Ev,
        term: &Term,
        at: Position,
        depth: usize,
        out: &mut Vec<Found>,
    ) -> Result<()> {
        if depth > 4 * MAX_DEPTH {
            return Ok(());
        }
        let d = depth + 1;
        let term = strip(term);
        match term {
            Term::App(..) => {
                let (head, args) = spine_icit(term).expect("an application");
                let args: Vec<&Term> = args.iter().map(|(a, _)| *a).collect();
                if let Term::Lam(_, _, body) = head {
                    // An applied lambda: a `let`.
                    self.walk(g, body, at, d, out)?;
                    for a in &args {
                        self.walk(g, a, Position::LetValue, d, out)?;
                    }
                    return Ok(());
                }
                let Term::Def(id) = head else {
                    self.walk(g, head, Position::Other, d, out)?;
                    for a in &args {
                        self.walk(g, a, Position::Other, d, out)?;
                    }
                    return Ok(());
                };
                if self.classifier.is_fold(*id) {
                    out.push(Found {
                        def: self.def,
                        variant: self.variant,
                        position: at,
                        classified: self.classifier.classify(g, *id, &args, self.bodies)?,
                    });
                    // The body is applied under the fold's activation, and
                    // a clause run in place under the handler's.
                    let comp = if *id == self.classifier.fold { 6 } else { 8 };
                    for (i, a) in args.iter().enumerate() {
                        if i == comp {
                            self.walk(g, a, Position::Consuming, d, out)?;
                        } else {
                            self.walk_continuation(g, a, d, out)?;
                        }
                    }
                    return Ok(());
                }
                if Some(*id) == self.bind && args.len() == 6 {
                    self.walk(g, args[4], at, d, out)?;
                    return self.walk_continuation(g, args[5], d, out);
                }
                if self.passes_body.contains(id) {
                    for a in &args {
                        self.walk(g, a, Position::Consuming, d, out)?;
                    }
                    return Ok(());
                }
                let branch = (Some(*id) == self.classifier.if_then_else && args.len() == 4)
                    || (Some(*id) == self.classifier.elim_dec && args.len() == 5);
                if branch {
                    let at_branch = args.len() - 2;
                    for (i, a) in args.iter().enumerate() {
                        if i >= at_branch
                            && let Term::Lam(_, _, body) = strip(a)
                        {
                            self.walk(g, body, at, d, out)?;
                        } else {
                            self.walk(g, a, Position::Other, d, out)?;
                        }
                    }
                    return Ok(());
                }
                let inner = if self.helpers.contains(id) {
                    Position::RowHelper
                } else {
                    Position::Other
                };
                for a in &args {
                    self.walk(g, a, inner, d, out)?;
                }
                Ok(())
            }
            Term::Let(_, _, value, body, _) => {
                self.walk(g, value, Position::LetValue, d, out)?;
                self.walk(g, body, at, d, out)
            }
            Term::Case(_, _, branches) => {
                for b in branches.iter() {
                    if let Some(body) = &b.body {
                        self.walk(g, body, at, d, out)?;
                    }
                }
                Ok(())
            }
            Term::NumCase(_, arms, default) => {
                for arm in arms.iter() {
                    self.walk(g, &arm.body, at, d, out)?;
                }
                self.walk(g, default, at, d, out)
            }
            Term::Lam(_, _, body) => self.walk(g, body, Position::Other, d, out),
            Term::Ctor(_, _, fields) => {
                for f in fields {
                    self.walk(g, f, Position::Other, d, out)?;
                }
                Ok(())
            }
            Term::Def(id) if self.classifier.is_fold(*id) => {
                out.push(Found {
                    def: self.def,
                    variant: self.variant,
                    position: Position::Other,
                    classified: None,
                });
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// A continuation, clause or fold body: a lambda's body is consuming;
    /// anything else is an argument.
    fn walk_continuation(
        &self,
        g: &Ev,
        term: &Term,
        depth: usize,
        out: &mut Vec<Found>,
    ) -> Result<()> {
        let mut body = strip(term);
        let mut lams = 0;
        while let Term::Lam(_, _, b) = body {
            body = strip(b);
            lams += 1;
        }
        let at = if lams > 0 {
            Position::Consuming
        } else {
            Position::Other
        };
        // A step `handlePlus … (elim clause…) forward` is walked as a call;
        // its clauses' bodies are lambdas, so consuming.
        if lams == 0
            && let Some((Term::Def(_), args)) = spine_icit(body)
        {
            for (a, _) in args {
                self.walk_continuation(g, a, depth + 1, out)?;
            }
            return Ok(());
        }
        self.walk(g, body, at, depth + 1, out)
    }
}

/// Counts over a set of folds.
#[derive(Clone, Debug, Default)]
pub struct Census {
    pub folds: usize,
    /// Folds whose step doesn't have the elaborator's shape.
    pub unrecognised: usize,
    pub state: usize,
    pub by_fold: BTreeMap<Fold, usize>,
    pub by_forward: BTreeMap<ForwardShape, usize>,
    pub by_position: BTreeMap<Position, usize>,
    pub clauses: BTreeMap<Kind, usize>,
    /// Clause kinds in folds that state fusion runs as a loop.
    pub state_clauses: BTreeMap<Kind, usize>,
}

impl Census {
    pub fn add(&mut self, found: &Found) {
        self.folds += 1;
        *self.by_position.entry(found.position).or_default() += 1;
        let Some(c) = &found.classified else {
            self.unrecognised += 1;
            return;
        };
        *self.by_fold.entry(c.fold).or_default() += 1;
        *self.by_forward.entry(c.forward).or_default() += 1;
        if c.state {
            self.state += 1;
        }
        for kind in &c.clauses {
            *self.clauses.entry(*kind).or_default() += 1;
            if c.state {
                *self.state_clauses.entry(*kind).or_default() += 1;
            }
        }
    }
}

/// The folds in each of `defs`' bodies as the runtime's lowering sees them
/// (the generic body, with calls of row eliminators at `Empty` inlined) and
/// in their empty-row variants, where one can be made.
pub fn census(g: &Ev, defs: &[DefId]) -> Result<Vec<Found>> {
    let Some(classifier) = Classifier::new(g) else {
        return Ok(Vec::new());
    };
    let spec = crate::specialise::Specialiser::new(g);
    let bodies = |id: DefId, args: &[&Term]| -> Option<Rc<Term>> {
        if spec.empty_call(id, args).ok()? {
            return spec.empty_body(id).ok()?;
        }
        if let Some(body) = spec.generic_body(id).ok()? {
            return Some(body);
        }
        let def = g.def(id);
        Some(Term::peel_lams_rc(def.run_body()?, def.arity()))
    };
    let mut out = Vec::new();
    for &id in defs {
        let def = g.def(id);
        // `foldComp`'s own recursion is the native's, never lowered; a
        // theorem's body, and a `match` lifted from one, never run.
        if id == classifier.fold || def.theorem() {
            continue;
        }
        let Some(run) = def.run_body() else {
            continue;
        };
        if !mentions_fold(run, &classifier) || lifted_from_theorem(g, id) {
            continue;
        }
        let generic = spec.generic_body(id).ok().flatten();
        let body = generic
            .as_deref()
            .unwrap_or_else(|| run.peel_lams(def.arity()));
        folds_in(g, &classifier, id, false, body, Some(&bodies), &mut out)?;
        if let Ok(Some(variant)) = spec.empty_body(id) {
            folds_in(g, &classifier, id, true, &variant, Some(&bodies), &mut out)?;
        }
    }
    Ok(out)
}

/// Whether `id` is a `match` lifted out of a theorem (`t.%match1`).
fn lifted_from_theorem(g: &Ev, id: DefId) -> bool {
    if !is_lifted_match(g, id) {
        return false;
    }
    let path = g.def(id).path();
    let Some((owner, _)) = path.rsplit_once('.') else {
        return false;
    };
    (0..g.env.defs().len())
        .map(DefId)
        .find(|d| &**g.def(*d).path() == owner)
        .is_some_and(|d| g.def(d).theorem())
}

fn mentions_fold(term: &Term, classifier: &Classifier) -> bool {
    term.subterms()
        .any(|(t, _)| matches!(t, Term::Def(id) if classifier.is_fold(*id)))
}

/// A short rendering of `term` for messages and the census: implicit
/// arguments and types are elided, variables are de Bruijn indices.
pub fn sketch(g: &Ev, term: &Term) -> String {
    let mut out = String::new();
    sketch_into(g, term, &mut out, 0);
    out
}

fn sketch_into(g: &Ev, term: &Term, out: &mut String, depth: usize) {
    if depth > 40 || out.len() > 4000 {
        out.push('…');
        return;
    }
    let d = depth + 1;
    match term {
        Term::Loc(_, t) | Term::Ann(t, _) => sketch_into(g, t, out, depth),
        Term::Var(i) => out.push_str(&format!("#{i}")),
        Term::Def(id) => out.push_str(g.def(*id).path()),
        Term::Data(id, _) => out.push_str(&format!("<{}>", g.data(*id).name())),
        Term::Ctor(id, c, fields) => {
            out.push('(');
            out.push_str(&g.data(*id).ctors()[*c].name);
            for f in fields {
                out.push(' ');
                sketch_into(g, f, out, d);
            }
            out.push(')');
        }
        Term::Nat(n) => out.push_str(&n.to_string()),
        Term::Lam(x, _, b) => {
            out.push_str(&format!("(\\{x}. "));
            sketch_into(g, b, out, d);
            out.push(')');
        }
        Term::App(..) => {
            let (head, args) = spine_icit(term).expect("an application");
            out.push('(');
            sketch_into(g, head, out, d);
            for (a, i) in args {
                if i == Icit::Implicit {
                    out.push_str(" _");
                } else {
                    out.push(' ');
                    sketch_into(g, a, out, d);
                }
            }
            out.push(')');
        }
        Term::Let(x, _, v, b, _) => {
            out.push_str(&format!("(let {x} := "));
            sketch_into(g, v, out, d);
            out.push_str("; ");
            sketch_into(g, b, out, d);
            out.push(')');
        }
        Term::Case(ix, data, branches) => {
            out.push_str(&format!("(case #{ix} of {}", g.data(*data).name()));
            for b in branches.iter() {
                out.push_str(" | ");
                match &b.body {
                    Some(body) => sketch_into(g, body, out, d),
                    None => out.push_str("impossible"),
                }
            }
            out.push(')');
        }
        Term::Pi(..) | Term::Sort(_) | Term::Eq(..) => out.push_str("<type>"),
        _ => out.push_str("<…>"),
    }
}
