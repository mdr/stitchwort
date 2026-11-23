//! `cases` and `cases then t` (docs/syntax.md, "cases"; docs/proposals/simp.md
//! §5): a proof by case splitting on what the goal, and the hypotheses that
//! say "this is a constructor", are stuck on.
//!
//! ```text
//! cases             -- split until each case is closed automatically
//! cases then t      -- and try `t` in each case
//! cases x, y then t -- split only `x` and `y` (and their fields)
//! ```
//!
//! At each case (a *node*), the closers are tried, cheapest first (§5.4):
//!
//! 1. **computation**: the goal is an equation whose sides compute to the
//!    same thing (`byComputing`);
//! 2. **contradiction**: a hypothesis is an equation between different
//!    constructors (`False = True`), refuted by `J` along it into a family
//!    that is `Unit` at one constructor and `Void` at the other; or `e =
//!    True` beside `e = False` for the same Bool `e`, stuck or not
//!    ([`bool_clash`]);
//! 3. **taking an equation apart**: a hypothesis `C a = C b` adds `a = b`
//!    (by `J` along it with a projection), and the node starts again;
//! 4. **a hypothesis** of exactly the goal's type, or a part of one: a
//!    side of a conjunction, or what a test fact reads as
//!    (docs/proposals/bool-as-proposition.md §9: `(a && b) = True` as `a ∧
//!    b`), taken apart in turn; past the bounds of taking them apart, a
//!    side of a `&&` reached through `&&`s only ([`auto::AndSides`], SW-4485);
//! 5. **`t`**, for `cases then t`, elaborated in the case;
//! 6. **a conjunction or a record of proofs** whose parts each close by 1
//!    or 4, or are such conjunctions or records in turn: the pair (or
//!    record) of their proofs ([`by_parts`], SW-4472, SW-4485);
//! 7. **`arithmetic`**, only where nothing is left to split (D1319).
//!
//! Between 5 and the splits, an equation 3 added with a variable side, `x =
//! t`, puts `t` in place of `x` in the goal and the hypotheses, and the node
//! starts again ([`substitute`], SW-3344).
//!
//! If none closes it, a hypothesis `h: P → Q` whose premise holds in the
//! case (an equation whose sides compute to the same thing, such as `b =
//! True → fact` once `b` is split, or a hypothesis of type `P`) adds `Q`,
//! and the case starts again (SW-948, [`apply_guarded`]).
//!
//! In the first try ([`Run::or_first`], SW-4472), a hypothesis `A ∨ B`,
//! neither side known, is then split into a case with `A` and one with `B`,
//! each a fact [`substitute`] may use ([`split_disjunction`]). A first try
//! that split one and failed is followed by the same try without it, which
//! is `cases` as it was before, so what that proved still checks.
//!
//! If nothing is added, `cases` finds an *atom* (§5.2): following what the
//! goal is stuck on inwards (a definition's case tree, run on its arguments,
//! stops at a `case` on a stuck value; that value may itself be a stuck call,
//! and so on), the innermost value whose type is *splittable* (data with two
//! or more constructors, not recursive, not an indexed family, not a
//! proposition). A one-constructor type (a record) is split only when
//! nothing else is stuck. The goal is searched first, then the hypotheses
//! that are an equation between a constructor and a stuck term (D1318),
//! latest first. Unfolding doesn't make a new atom: the atom is the value
//! the case tree tested, so `Float.isNaN x`, not its body.
//!
//! Before that, a survey of the same chains (SW-939): when two or more of
//! them, each with an atom on it, end at the same value of a recursive type
//! other than `Nat`, with nothing but recursive types between their last
//! atom and it (`List.get t 0 = List.head t`, both waiting for `t`), that
//! value is split first, so they compute together; splitting their atoms
//! one by one would make cases that can't happen (one `None`, the other
//! `Some`). Only once: a field of an earlier split of its type (`xs` after
//! `t = Cons x xs`) isn't split again, so `cases` never does induction by
//! itself ([`Finder::shared`]).
//!
//! An `Int` `==` that something outside tests (`if x + 1 == y then …`) is
//! split as the `Bool` it is, not through `Int.decEq` into the `Int`'s
//! constructors ([`number_equality`]).
//!
//! `Int`'s own arithmetic (`-x`, `+`, `-`, `*`, `/`, `%`, `<=`, `<`, and
//! `Int.subNatNat`, which they compute through) is as far in as the search
//! goes (SW-937): what its case trees test (`OfNat`/`NegSucc` of an
//! operand, `Int.subNatNatFrom …`) is never an atom, and a call of it is one
//! only when a definition outside it tests the call (a program's own `match`
//! on `a + b`). `arithmetic` and `algebra` reason about the arithmetic instead. An
//! `Int` variable is still split as a fallback (below), which
//! `aimedDepthAfter` in AoC 2021 day 2 needs.
//!
//! The split is the generated `match` that `match e: atom with` writes
//! (`matching::generalised_named`, lifted as `owner.%matchN`), one
//! alternative per constructor, the equation bound as `%splitN`, and each
//! alternative's body is this `cases` again: so the proof is ordinary
//! `match`es and the closers' terms, and the kernel checks it as such.
//!
//! A case still open then is tried by its goal's decision procedure, as
//! `auto` finds and runs one (docs/proposals/decide.md §6.1.2): a test that
//! computes to `True` closes it with `auto`'s term, `d.sound byComputing`; `False` doesn't fail
//! it, since its hypotheses may still contradict each other.
//!
//! A case still open then, whose goal is a `Π`, has the goal's leading
//! binders introduced, and starts again under them (docs/proposals/decide.md
//! §6.1.1): `theorem t: (x: Bool) → P x := cases` is the proof `x => cases`.
//! This comes after the closers, so a `Π` goal they prove whole (a
//! hypothesis of that type, `arithmetic` on `P → Void`, `t`) keeps that proof.
//!
//! A case still open then, not a `Π`, is closed if applying an implication
//! once to a hypothesis, or a part of one, that is its premise (a plain
//! proposition too, and each premise in turn while they hold) lets a closer
//! that doesn't split close it ([`apply_to_part`], SW-4472, SW-4485);
//! otherwise nothing is added.
//!
//! A case still open then, not a `Π`, has the *last resort* split, if any
//! ([`Finder::last_resort_atom`], SW-3752): on the first chain that has one,
//! the goal's before the hypotheses', the innermost value that `cases`
//! doesn't otherwise split: a number a `NumCase` compares with numbers,
//! split into those numbers and the rest (where the number is apart from
//! them, docs/core.md, so the `NumCase` takes its default); or a value of a
//! recursive type other than `Nat`, split into its constructors, unless it
//! is a field of an earlier split of its type. Or an atom split already
//! that a later split exposed again, split once more.
//!
//! A case still open then, not a `Π`, is split anyway, as a *fallback*
//! (§6.1.3): of the variables the goal mentions, as computed, that are
//! splittable and not known in this case, the one with the fewest
//! constructors (a record's 1, `Bool`'s 2), ties to the latest bound. That
//! is what proves `key ∈ keys`, a disjunction of equations not stuck on
//! `key`. Its splits are marked "(fallback)" in the diagnostics.
//!
//! A `cases` that fails tries once more ([`Run::thrifty`]): the
//! hypotheses and their parts first (records and the last resort's splits
//! too), then the last resort's splits of the goal, then its atoms; with
//! `arithmetic` tried before every split, and [`THRIFTY_CASES`] cases. In a
//! case still open after its fallback, it splits what an earlier split's
//! own equation is still stuck on ([`Finder::under_split`], SW-4226): the
//! search takes a native comparison (`5 <= level tok`) whole, so once it is
//! split, `tok` under it is split too. The first try's proofs are
//! unchanged.
//!
//! `cases x, y then t` (SW-4474, D3709) takes the choice of splits from
//! the search and gives it to the proof ([`named_target`], [`named_rest`]):
//! in each case, after closers 1 to 4, the first named value not yet split
//! is split (data into its constructors, an `∨` into its sides, and a side
//! that is an `∨` in turn); once all are, `t` and the steps that don't split
//! run as above, and where the case is still open a field of a named split
//! is split, the one the goal is stuck on first, then the others the case
//! mentions (not a field of a recursive type). Nothing else is split: no
//! atom, last resort or fallback, and there is one try, not three.
//!
//! In `t`, each named value split on the way is a local definition of what
//! the case says it is ([`named_aliases`]), as the goal has it. There, a
//! hypothesis as written that equates a variable with a
//! constructor form (`kind = Minus`) is used by [`substitute`] as a fact
//! `cases` added would be.
//!
//! A case nothing closes, with nothing left to split, is `E-CASES`, showing
//! the path of choices to it and the hypotheses in scope (only the latest
//! copy of each, as generalising copies them). More than [`CASES`] cases, or
//! more than [`STEPS`] evaluation steps, is `E-CASES-BUDGET`.

use num_bigint::BigUint;
use std::cell::{Cell, RefCell};
use std::rc::Rc;
use stitchwort_core::Ev;
use stitchwort_core::ProofMark;

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{
    Elim, Head, body_seen, conv, eval, force, is_folded, quote_at_most, unfold_folded,
};
use stitchwort_core::{DataId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::ast::{self, Alt, Expr, Pattern};
use stitchwort_syntax::{Diagnostic, Span};

use crate::check::{Ctx, Result, builtin_ctor, builtin_data, builtin_def};

/// The most cases one `cases` makes (§5.8): the largest tree the motivating
/// proofs need has 12.
pub(crate) const CASES: usize = 64;

/// The most cases the second try makes ([`Run::thrifty`]), which only a
/// `cases` that ran out of [`CASES`] gets to: inverting a hypothesis about a
/// function of nine guarded arms over character ranges (`lexemeStart … =
/// Some WordLexeme`) takes about a hundred, every one of them needed.
const THRIFTY_CASES: usize = 4 * CASES;

/// The most evaluation steps one try of a `cases` takes, its closers and
/// splits together; past them there is no second try. A case whose goal
/// holds a large computation stuck on a variable (a level's whole 20 by 66
/// terrain, each cell waiting for the level) costs millions of steps to
/// search and to split, so the [`CASES`]-case budget alone let a wrong
/// proof run for over 15 minutes (SW-3846). The most any `cases` in the
/// toy formatter's proofs, the roguelike's and the `cases` examples took
/// was 5.6 million (17 Nov 2026). Most of a search's time isn't counted
/// as steps (reading values back, comparing them), so these 20 million
/// take a few seconds.
const STEPS: u64 = 20_000_000;

/// The prefix of the names the split equations are bound to: not one a
/// program can write.
const EQUATION: &str = "%case";

/// One `cases`, while its cases are checked.
pub(crate) struct Run {
    /// `t`, for `cases then t`.
    body: Option<Box<Expr>>,
    /// The `cases` as written: the alternatives' bodies are `cases`s with
    /// this span, which continue this one.
    span: Span,
    /// Cases made so far.
    cases: Cell<usize>,
    /// The atoms split on, as shown, in the order first split, and whether
    /// each was first split as a fallback.
    atoms: RefCell<Vec<(String, bool)>>,
    /// How the closed cases were closed.
    closed: RefCell<Closed>,
    /// Set once the budget is exceeded: every case after that fails at once.
    over: Cell<bool>,
    /// Set when the budget ran out because a case was too large to split
    /// ([`SPLIT_READ_BACK_NODES`]), not because of the number of cases.
    over_size: Cell<bool>,
    /// Set when the budget ran out because the cases took more than
    /// [`STEPS`] evaluation steps between them.
    over_steps: Cell<bool>,
    /// The split that exceeded the budget, `x : T`, when it was a fallback.
    over_fallback: RefCell<Option<String>>,
    /// Whether an `Int` was split into its constructors (`OfNat`, `NegSucc`).
    split_int: Cell<bool>,
    /// For each atom in `atoms`, its type, when it is a variable.
    atom_types: RefCell<Vec<Option<Value>>>,
    /// When the budget ran out and every atom split was a variable of a
    /// type with a `Finite` instance: those variables, `x : T`, for the
    /// note pointing to `Finite.check`.
    over_finite: RefCell<Option<Vec<String>>>,
    /// The first case still open when the budget ran out, as shown.
    open_at: RefCell<Option<String>>,
    /// Facts added by taking equations apart, for their names.
    facts: Cell<usize>,
    /// The names of the facts [`take_apart`] added (and of their copies,
    /// which keep the name): those [`substitute`] may eliminate a variable
    /// by.
    injected: RefCell<Vec<Name>>,
    /// The facts [`substitute`] has used on the way to this case (used
    /// again, the variable left would be replaced back), each with how
    /// `E-CASES` shows it ("`y` is replaced by `x`: …").
    substituted: RefCell<Vec<(Name, String)>>,
    /// Whether each data type is splittable, and its constructor count.
    splittable: RefCell<HashMap<DataId, Option<usize>>>,
    /// The second try, after the first ran out of cases ([`cases_goal`]):
    /// the hypotheses are split before the goal, and every case tries
    /// `arithmetic` before it is split.
    thrifty: bool,
    /// The first try ([`cases_goal`]): a hypothesis `A ∨ B` is split before
    /// what the goal is stuck on ([`or_hypothesis`]).
    or_first: bool,
    /// The names of the `∨` hypotheses split on the way to this case (a
    /// copy keeps the name), never split again.
    split_ors: RefCell<Vec<Name>>,
    /// Whether an `∨` was split at all.
    split_or: Cell<bool>,
    /// The values `cases x, y then t` names (SW-4474): only they, and the
    /// fields and sides of their splits, are split ([`named_split`]).
    /// Empty for `cases` choosing its own splits.
    targets: Vec<ast::Name>,
    /// The facts that splitting a named `∨` (or a side of one) added, each
    /// with the index of the target it came from: a side that is an `∨` in
    /// turn is split deeper.
    named_facts: RefCell<Vec<(Name, usize)>>,
    /// The named split being made, as the budget error shows it.
    splitting: RefCell<Option<String>>,
}

impl Run {
    /// The most cases this try may make.
    fn limit(&self) -> usize {
        if self.thrifty { THRIFTY_CASES } else { CASES }
    }
}

#[derive(Default)]
struct Closed {
    computation: usize,
    contradiction: usize,
    hypothesis: usize,
    term: usize,
    omega: usize,
    decision: usize,
}

impl Closed {
    fn total(&self) -> usize {
        self.computation
            + self.contradiction
            + self.hypothesis
            + self.term
            + self.omega
            + self.decision
    }

    fn describe(&self) -> String {
        let parts: Vec<String> = [
            (self.computation, "by computation"),
            (self.contradiction, "by contradiction"),
            (self.hypothesis, "by a hypothesis"),
            (self.term, "by the term after `then`"),
            (self.omega, "by `arithmetic`"),
            (self.decision, "by deciding"),
        ]
        .iter()
        .filter(|(n, _)| *n > 0)
        .map(|(n, how)| format!("{n} {how}"))
        .collect();
        parts.join(", ")
    }
}

/// `cases` where nothing says what it should prove.
pub(crate) fn no_goal(_cx: &Ctx, expr: &Expr) -> Diagnostic {
    Diagnostic::error("E-CASES", "`cases` needs to know what it proves")
        .with_label(expr.span(), "the expected type isn't known here")
        .with_note("give it a type: `(cases: P)`")
}

/// `cases` against the goal `expected`. Outside a split of a `cases`, one
/// that fails while the goal holds an unknown the declaration will still
/// settle waits for it, whole, and tries again (`queue::tactic_or_wait`;
/// docs/proposals/postponement.md, step 4.2). Inside a split it runs as
/// before: the split's alternatives can't wait in the middle of it.
pub(crate) fn check_cases(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    if cx.cases.is_some() {
        return cases_goal(cx, expr, expected);
    }
    crate::queue::tactic_or_wait(cx, expr, expected, cases_goal)
}

/// [`check_cases`]'s `cases` itself.
fn cases_goal(cx: &mut Ctx, expr: &Expr, expected: &Value) -> Result<Term> {
    let Expr::Cases {
        targets,
        body,
        span,
    } = expr
    else {
        unreachable!("only called on `cases`")
    };
    // An alternative of a split this `cases` made: go on splitting.
    if let Some(run) = cx.cases.clone()
        && run.span == *span
    {
        return node(cx, &run, expected);
    }
    // The splits are the proof's: one try, with nothing to choose
    // differently a second time.
    if !targets.is_empty() {
        for target in targets {
            named_kind(cx, target)?;
        }
        let unused = Cell::new(false);
        return attempt(
            cx, targets, body, *span, expected, false, false, &unused, &unused,
        );
    }
    let out_of_cases = Cell::new(false);
    // The first try splits a hypothesis `A ∨ B` before what the goal is
    // stuck on (SW-4472): one split of two cases, where the goal's own
    // atom may have sixty. A try that split one and failed is followed by
    // the try without it, as `cases` was before, so what that proved it
    // still proves.
    let split_or = Cell::new(false);
    let first = attempt(
        cx,
        targets,
        body,
        *span,
        expected,
        false,
        true,
        &out_of_cases,
        &split_or,
    );
    let first = match first {
        Err(e) if split_or.get() && !crate::undo::fatal(&e) => {
            out_of_cases.set(false);
            attempt(
                cx,
                targets,
                body,
                *span,
                expected,
                false,
                false,
                &out_of_cases,
                &split_or,
            )
        }
        first => first,
    };
    // A `cases` that failed tries once more, another way (SW-3752): the
    // hypotheses, and the parts of them, are split before the goal, and
    // every case tries `arithmetic` before it is split. Split goal first,
    // ten comparisons of `c` in the goal each took the four comparisons of
    // a hypothesis that `c` is a letter again (SW-3459); and a hypothesis
    // that a call is a constructor is inverted where the goal's own splits
    // left nothing to say (SW-3461). Only a `cases` that would fail gets
    // here, so the proofs it gave before keep their terms; a failure
    // reports the first try, which follows the goal as it is written.
    let Err(e) = first else {
        return first;
    };
    if crate::undo::fatal(&e) || e.code == "E-CASES-BUDGET" && !out_of_cases.get() {
        return Err(e);
    }
    let ran_out = out_of_cases.get();
    match attempt(
        cx,
        targets,
        body,
        *span,
        expected,
        true,
        false,
        &out_of_cases,
        &split_or,
    ) {
        Ok(term) => Ok(term),
        Err(second) if crate::undo::fatal(&second) => Err(second),
        Err(_) if ran_out => Err(e.with_note(format!(
            "a second try, splitting the hypotheses before the goal and trying `arithmetic` \
             before each split, didn't close them all either, in {THRIFTY_CASES} cases"
        ))),
        Err(_) => Err(e),
    }
}

/// One try of [`cases_goal`]'s `cases`; `thrifty` for the second
/// ([`Run::thrifty`]); `or_first` for one that splits `∨` hypotheses first
/// ([`Run::or_first`]). `out_of_cases` is set when it fails for making more
/// than [`CASES`] cases, `split_or` when it split an `∨`.
#[allow(clippy::too_many_arguments)]
fn attempt(
    cx: &mut Ctx,
    targets: &[ast::Name],
    body: &Option<Box<Expr>>,
    span: Span,
    expected: &Value,
    thrifty: bool,
    or_first: bool,
    out_of_cases: &Cell<bool>,
    split_or: &Cell<bool>,
) -> Result<Term> {
    let snapshot = crate::undo::Snapshot::take(cx);
    let result = attempt_once(
        cx,
        targets,
        body,
        span,
        expected,
        thrifty,
        or_first,
        out_of_cases,
        split_or,
    );
    if result.is_err() {
        snapshot.restore(cx);
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn attempt_once(
    cx: &mut Ctx,
    targets: &[ast::Name],
    body: &Option<Box<Expr>>,
    span: Span,
    expected: &Value,
    thrifty: bool,
    or_first: bool,
    out_of_cases: &Cell<bool>,
    split_or: &Cell<bool>,
) -> Result<Term> {
    let run = Rc::new(Run {
        thrifty,
        or_first,
        split_ors: RefCell::new(Vec::new()),
        body: body.clone(),
        span,
        cases: Cell::new(1),
        atoms: RefCell::new(Vec::new()),
        split_int: Cell::new(false),
        closed: RefCell::new(Closed::default()),
        over: Cell::new(false),
        over_size: Cell::new(false),
        over_steps: Cell::new(false),
        over_fallback: RefCell::new(None),
        atom_types: RefCell::new(Vec::new()),
        over_finite: RefCell::new(None),
        open_at: RefCell::new(None),
        facts: Cell::new(0),
        injected: RefCell::new(Vec::new()),
        substituted: RefCell::new(Vec::new()),
        splittable: RefCell::new(HashMap::default()),
        split_or: Cell::new(false),
        targets: targets.to_vec(),
        named_facts: RefCell::new(Vec::new()),
        splitting: RefCell::new(None),
    });
    let saved = cx.cases.replace(run.clone());
    let errors = cx.e.attempt.branch_errors.borrow().len();
    let g = cx.g();
    let mut steps = STEPS;
    let result = match g
        .machine
        .budget
        .limited(&mut steps, || node(cx, &run, expected))
    {
        Ok(Some(term)) => Ok(term),
        Ok(None) => {
            run.over.set(true);
            run.over_steps.set(true);
            Err(Diagnostic::error("E-CASES-BUDGET", "over budget"))
        }
        Err(e) => Err(e),
    };
    cx.cases = saved;
    split_or.set(split_or.get() || run.split_or.get());
    let error = match result {
        Ok(term) => return Ok(term),
        Err(e) if crate::undo::fatal(&e) => return Err(e),
        Err(e) => e,
    };
    // The other cases that failed were kept for the definition to report
    // after this one (`check_tree`): one error says it for the `cases`.
    let others = cx.e.attempt.branch_errors.borrow().len() - errors;
    cx.e.attempt.branch_errors.borrow_mut().truncate(errors);
    if run.over.get() {
        // A case too large to split, or cases too costly to search, would
        // be as large and as costly on the second try.
        out_of_cases.set(!run.over_size.get() && !run.over_steps.get());
        return Err(budget_error(&run));
    }
    let closed = run.closed.borrow();
    let mut error = error;
    if others > 0 {
        error = error.with_note(format!(
            "{others} other case{} couldn't be closed either",
            if others == 1 { "" } else { "s" }
        ));
    }
    if closed.total() > 0 {
        error = error.with_note(format!(
            "{} other case{} {} closed ({})",
            closed.total(),
            if closed.total() == 1 { "" } else { "s" },
            if closed.total() == 1 { "was" } else { "were" },
            closed.describe()
        ));
    }
    Err(error)
}

fn budget_error(run: &Run) -> Diagnostic {
    let atoms = run.atoms.borrow();
    let message = if run.over_steps.get() {
        format!(
            "`cases` took more than {} evaluation steps without closing every case",
            stitchwort_core::budget::with_commas(STEPS)
        )
    } else if run.over_size.get() {
        "`cases` made a case too large to split: its goal and hypotheses, written out in \
         full, have more than a million parts"
            .to_string()
    } else {
        format!("`cases` made more than {CASES} cases without closing them all")
    };
    let mut d = Diagnostic::error("E-CASES-BUDGET", message).with_label(run.span, "this `cases`");
    if let Some(split) = &*run.splitting.borrow()
        && !run.over_steps.get()
    {
        d = d.with_note(format!("it went over splitting {split}"));
    }
    if let Some(split) = &*run.over_fallback.borrow() {
        d = d.with_note(format!(
            "`cases` tried splitting `{split}` as a fallback; this would exceed the \
             {CASES}-case budget"
        ));
    }
    d = d.with_note(format!(
        "it split on {}: {}",
        atoms.len(),
        atoms
            .iter()
            .map(|(a, fallback)| if *fallback {
                format!("`{a}` (fallback)")
            } else {
                format!("`{a}`")
            })
            .collect::<Vec<_>>()
            .join(", ")
    ));
    if run.split_int.get() {
        d = d.with_note(
            "`cases` is taking an `Int` apart into `OfNat` and `NegSucc` (`Int.natAbs`, `max`, \
             `Int.subNatNat` … test them); split on a comparison of the `Int`s instead, as `match \
             a <= b with` or an `if` the goal depends on, and let `arithmetic` read each side",
        );
    }
    if let Some(open) = &*run.open_at.borrow() {
        d = d.with_note(format!("the first case still open: {open}"));
    }
    if let Some(vars) = &*run.over_finite.borrow() {
        d = d.with_note(format!(
            "every variable it split has a finite type ({}): to check every value by \
             computing instead, state it as a `Bool` function `p` of one record or pair \
             holding them and prove `p v = True` by `Finite.check p byComputing v` (`import Std \
             (Finite)`)",
            vars.join(", ")
        ));
    }
    if !run.targets.is_empty() {
        return d.with_generic_note(
            "name fewer values to split, prove a fact that decides some of the cases at once \
             and use it in `t`, or split by hand with `match`",
        );
    }
    d.with_generic_note(
        "prove a fact that decides some of the cases at once and give it as `cases then t`, \
         or split by hand with `match`",
    )
}

/// One case: close it, or split it.
fn node(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Term> {
    if run.over.get() {
        return Err(Diagnostic::error("E-CASES-BUDGET", "over budget"));
    }
    if let Some(term) = by_computation(cx, goal)? {
        run.closed.borrow_mut().computation += 1;
        return Ok(term);
    }
    if let Some(term) = by_contradiction(cx, goal, &visible(cx))? {
        run.closed.borrow_mut().contradiction += 1;
        return Ok(term);
    }
    if let Some(term) = take_apart(cx, run, goal)? {
        return Ok(term);
    }
    if let Some(term) = by_hypothesis(cx, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    if let Some(term) = by_hypothesis_part(cx, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    // The values the proof names are split before `t` is tried: until
    // they are, `t` faces the goal the proof says to split.
    if !run.targets.is_empty()
        && let Some(split) = named_target(cx, run)?
    {
        return named_split(cx, run, split, goal);
    }
    let mut failed_body = None;
    if let Some(body) = &run.body {
        let snapshot = crate::undo::Snapshot::take(cx);
        let errors = cx.e.attempt.branch_errors.borrow().len();
        let mark = cx.mark();
        let checked = named_aliases(cx, run)
            .and_then(|aliases| Ok((crate::check::check(cx, body, goal)?, aliases)));
        cx.reset(mark);
        match checked {
            Ok((mut term, aliases)) => {
                for (name, ty, value) in aliases.into_iter().rev() {
                    term = Term::let_(name, ty, value, term);
                }
                run.closed.borrow_mut().term += 1;
                return Ok(term);
            }
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(e) => {
                cx.e.attempt.branch_errors.borrow_mut().truncate(errors);
                snapshot.restore(cx);
                failed_body = Some(e);
            }
        }
    }
    // A conjunction whose parts each close as above (SW-4472). After `t`,
    // so a case `t` closed keeps its proof; before the splits, which a goal
    // already proved doesn't need (a closed conjunction took 46 ms of
    // splitting hypotheses, against 2 for the pair).
    if let Some(term) = by_parts(cx, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    // After the closers and `t`: a case they close at this node keeps its
    // proof. One closed deeper (after a split, an implication or `arithmetic`)
    // now goes through the substitution first, so its term changes.
    if let Some(term) = substitute(cx, run, goal)? {
        return Ok(term);
    }
    if let Some(term) = apply_guarded(cx, run, goal)? {
        return Ok(term);
    }
    if !run.targets.is_empty() {
        return named_rest(cx, run, goal, failed_body);
    }
    if run.or_first
        && let Some(level) = or_hypothesis(cx, run, goal)?
    {
        return split_disjunction(cx, run, level, goal, None);
    }
    if run.body.is_some()
        && let Some(atom) = visible_condition(cx, run, goal)?
    {
        return split_on(cx, run, atom, goal, false);
    }
    let (atom, stuck, fallback, last_resort) = {
        let mut finder = Finder::new(cx, run);
        let atom = finder.find(goal)?;
        let fallback = match atom {
            None => finder.fallback()?,
            Some(_) => None,
        };
        (
            atom,
            finder.stuck.take(),
            fallback,
            finder.last_resort.take(),
        )
    };
    if let Some(atom) = atom {
        // Splitting on the goal's own side (`Nat.leq a b = True` into
        // `True = True` and `False = True`) is the last resort: `arithmetic` may
        // prove it whole, which is one case instead of two.
        if (atom.side || run.thrifty)
            && let Some(term) = crate::omega::prove_case(cx, goal, run.span)?
        {
            run.closed.borrow_mut().omega += 1;
            return Ok(term);
        }
        return split_on(cx, run, atom, goal, false);
    }
    let found = crate::omega::prove_case(cx, goal, run.span)?;
    if let Some(term) = found {
        run.closed.borrow_mut().omega += 1;
        return Ok(term);
    }
    // Only a case that would otherwise be open reaches the steps below, so
    // a proof that `cases` gave before them keeps its term.
    let decided = by_decision(cx, goal)?;
    if let Decided::Yes(term) = decided {
        run.closed.borrow_mut().decision += 1;
        return Ok(term);
    }
    // Everything above saw the goal as it stands, so a `Π` goal that a
    // hypothesis, `arithmetic` or `t` proves whole keeps that proof; only a case
    // that would otherwise be open goes on to have its binders introduced.
    if let Some(term) = introduce(cx, run, goal)? {
        return Ok(term);
    }
    // An implication applied to a part of a hypothesis (SW-4472), only
    // where the case would otherwise be open or split anyway, and only to
    // close it there: so the cases `cases` closed before keep their proofs.
    if let Some(term) = apply_to_part(cx, run, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    // The last resort (SW-3752): what the goal, or a hypothesis, is stuck on
    // that `cases` doesn't otherwise split: a number compared with numbers
    // (a character pattern's code), or a value of a recursive type, once.
    // Only a case that would otherwise be open or a fallback gets here, so
    // a proof `cases` gave before keeps its term.
    if let Some(atom) = last_resort {
        return split_on(cx, run, atom, goal, false);
    }
    // The fallback (docs/proposals/decide.md §6.1.3): the goal isn't stuck
    // on anything splittable, so split a variable it mentions anyway, the
    // one whose split makes the fewest cases, ties to the latest bound. In
    // each case it is a constructor, which may let a closer finish.
    if let Some(atom) = fallback {
        return split_on(cx, run, atom, goal, true);
    }
    // What an earlier split's own equation is still stuck on (SW-4226):
    // after `5 <= level tok` is split, the case `(5 <= level tok) = True`
    // has the goal `True = False`, which mentions nothing, while the
    // comparison, which the search took whole, still waits for `tok`.
    // Splitting `tok` computes the equation in each case, and the cases
    // where it is false contradict it. Only in the second try, and only in
    // a case that would otherwise be open: the first try is as it was, so
    // its proofs keep their terms and a failure it reports doesn't turn
    // into running out of steps, which would skip the second try.
    let under_split = if run.thrifty {
        Finder::new(cx, run).under_split()?
    } else {
        None
    };
    if let Some(atom) = under_split {
        return split_on(cx, run, atom, goal, false);
    }
    let error = open_case(cx, run, goal, stuck, failed_body);
    Err(match decided {
        Decided::No if !visibly_false(cx, goal)? => {
            error.with_note("the goal's decision procedure says it is false")
        }
        _ => error,
    })
}

// `cases x, y then t` (SW-4474): the splits the proof names.

/// What a named split takes apart: a variable of data type `d` at a level,
/// into its constructors, or the `∨` hypothesis at a level into its sides.
#[derive(Clone, Copy)]
enum NamedSplit {
    Data(usize, DataId),
    Or(usize),
}

/// A named split to make: what, the index of the target it comes from, and
/// how the budget error shows it.
struct Planned {
    split: NamedSplit,
    root: usize,
    shown: String,
}

/// What `target` names, checked before the first case: a variable or
/// hypothesis in scope, of a type `cases` can split.
fn named_kind(cx: &Ctx, target: &ast::Name) -> Result<NamedSplit> {
    let Some(level) = cx.lookup(&target.text) else {
        return Err(Diagnostic::error(
            "E-CASES",
            format!("`{}` isn't a variable or hypothesis in scope", target.text),
        )
        .with_label(target.span, "not in scope here")
        .with_note(
            "`cases x then t` splits a variable or hypothesis of the proof; to split a value \
             computed from them, write `match e with`",
        ));
    };
    classify(cx, level).map_err(|why| {
        Diagnostic::error(
            "E-CASES",
            format!("`{}` can't be split: {why}", target.text),
        )
        .with_label(target.span, "named here")
        .with_note(
            "`cases x then t` splits data into its constructors (a `Bool` into `True` and \
                 `False`) and an `∨` hypothesis into its two sides",
        )
    })
}

/// How the value at `level` splits, or why it can't.
fn classify(cx: &Ctx, level: usize) -> std::result::Result<NamedSplit, String> {
    let g = cx.g();
    let ty =
        force(&g, cx.types[level].clone()).map_err(|_| "its type can't be read".to_string())?;
    let shown = cx.show(&ty);
    let Value::Data(d, args) = &ty else {
        return Err(format!("its type `{shown}` isn't data, an `∨` or a `Bool`"));
    };
    if g.env.registry().is_data(Builtin::Or, *d) && args.len() == 2 {
        return Ok(NamedSplit::Or(level));
    }
    let data = g.data(*d);
    if data.sort() == Sort::Prop {
        return Err(format!(
            "it is a proof of `{shown}`, a proposition other than an `∨`"
        ));
    }
    if !data.indices().is_empty() {
        return Err(format!(
            "its type `{shown}` is an indexed family, which `cases` doesn't split; write the \
             `match` by hand"
        ));
    }
    if data.ctors().is_empty() {
        return Err(format!("its type `{shown}` has no constructors"));
    }
    Ok(NamedSplit::Data(level, *d))
}

/// The first named value not split yet in this case, in the order written.
fn named_target(cx: &Ctx, run: &Run) -> Result<Option<Planned>> {
    let finder = Finder::new(cx, run);
    for (root, target) in run.targets.iter().enumerate() {
        // A value a substitution replaced is no longer in scope.
        let Some(level) = cx.lookup(&target.text) else {
            continue;
        };
        let Ok(split) = classify(cx, level) else {
            continue;
        };
        let open = match split {
            NamedSplit::Data(..) => !finder.is_known(&Value::var(level))?,
            NamedSplit::Or(_) => !run.split_ors.borrow().contains(&cx.names[level]),
        };
        if open {
            return Ok(Some(Planned {
                split,
                root,
                shown: format!("`{}`", target.text),
            }));
        }
    }
    // A side of a named `∨` that is an `∨` in turn: `A ∨ B ∨ C` is split
    // into its three cases before `t` is tried, as one split.
    let facts = run.named_facts.borrow().clone();
    for (name, root) in facts.into_iter().rev() {
        let Some(level) = cx.lookup(&name) else {
            continue;
        };
        if let Ok(NamedSplit::Or(level)) = classify(cx, level)
            && !run.split_ors.borrow().contains(&cx.names[level])
        {
            return Ok(Some(Planned {
                split: NamedSplit::Or(level),
                root,
                shown: format!("a side of `{}`", run.targets[root].text),
            }));
        }
    }
    Ok(None)
}

/// Makes the named split `planned`.
fn named_split(cx: &mut Ctx, run: &Rc<Run>, planned: Planned, goal: &Value) -> Result<Term> {
    *run.splitting.borrow_mut() = Some(planned.shown);
    match planned.split {
        NamedSplit::Data(level, d) => split_on(
            cx,
            run,
            Atom {
                value: Value::var(level),
                d,
                side: false,
                numbers: None,
            },
            goal,
            false,
        ),
        NamedSplit::Or(level) => split_disjunction(cx, run, level, goal, Some(planned.root)),
    }
}

/// In a case of `cases x then t`, each named data value split on the way
/// here, bound under its own name to what the case says it is (`d` to
/// `False`, `edge` to `Plain (Some w)`), so that `t` naming it agrees with
/// the goal, which has the constructor in its place. Each is a local
/// definition, returned as the `let`s to wrap `t`'s term in.
fn named_aliases(cx: &mut Ctx, run: &Run) -> Result<Vec<(Name, Term, Term)>> {
    let mut aliases = Vec::new();
    for target in &run.targets {
        let Some(level) = cx.lookup(&target.text) else {
            continue;
        };
        let Ok(NamedSplit::Data(..)) = classify(cx, level) else {
            continue;
        };
        let value = case_value(cx, &Value::var(level), 32)?;
        if matches!(&value, Value::Neutral(Head::Var(l, _, _), spine) if *l == level && spine.is_empty())
        {
            continue;
        }
        let ty = cx.types[level].clone();
        let (ty_term, value_term) = (cx.quote_folded(&ty)?, cx.quote_folded(&value)?);
        let name = Name::from(target.text.as_str());
        cx.define(
            Some(&target.text),
            name.clone(),
            ty,
            ty_term.clone(),
            value_term.clone(),
        )?;
        aliases.push((name, ty_term, value_term));
    }
    Ok(aliases)
}

/// `value` as this case's split equations say it is: a variable a split
/// equation (the latest copy) gives a constructor form for is that form,
/// with its fields given the same way, `depth` levels deep.
fn case_value(cx: &Ctx, value: &Value, depth: usize) -> Result<Value> {
    let g = cx.g();
    let value = force(&g, value.clone())?;
    if depth == 0 {
        return Ok(value);
    }
    match &value {
        Value::Neutral(Head::Var(level, _, _), spine) if spine.is_empty() => {
            for l in (0..cx.level()).rev() {
                if !is_equation(cx, l) || stale(cx, l) {
                    continue;
                }
                let Value::Eq(_, lhs, rhs) = force(&g, cx.types[l].clone())? else {
                    continue;
                };
                if matches!(force(&g, (*lhs).clone())?, Value::Neutral(Head::Var(x, _, _), s) if x == *level && s.is_empty())
                {
                    return case_value(cx, &rhs, depth - 1);
                }
            }
            Ok(value)
        }
        Value::Ctor(d, c, args) => {
            let args: Vec<Value> = args
                .iter()
                .map(|a| case_value(cx, a, depth - 1))
                .collect::<Result<_>>()?;
            Ok(Value::Ctor(*d, *c, args.into()))
        }
        _ => Ok(value),
    }
}

/// The variables a constructor form holds, its own fields' fields too.
fn ctor_vars(g: &Ev, value: &Value, out: &mut Vec<usize>) -> Result<()> {
    match force(g, value.clone())? {
        Value::Neutral(Head::Var(level, _, _), spine) if spine.is_empty() => out.push(level),
        Value::Ctor(_, _, args) => {
            for arg in args.iter() {
                ctor_vars(g, arg, out)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// The fields of the named splits so far, transitively (a field of a
/// field), each with the target it comes from, in the order split.
fn named_fields(cx: &Ctx, run: &Run) -> Result<Vec<(usize, usize)>> {
    let g = cx.g();
    let mut found: Vec<(usize, usize)> = Vec::new();
    for (root, target) in run.targets.iter().enumerate() {
        if let Some(level) = cx.lookup(&target.text) {
            found.push((level, root));
        }
    }
    let equations: Vec<usize> = (0..cx.level()).filter(|&l| is_equation(cx, l)).collect();
    let mut done = vec![false; equations.len()];
    loop {
        let mut grew = false;
        for (i, &level) in equations.iter().enumerate() {
            if done[i] {
                continue;
            }
            let Value::Eq(_, l, r) = force(&g, cx.types[level].clone())? else {
                done[i] = true;
                continue;
            };
            let Value::Neutral(Head::Var(left, _, _), spine) = force(&g, (*l).clone())? else {
                done[i] = true;
                continue;
            };
            let Some(&(_, root)) = found.iter().find(|(f, _)| *f == left && spine.is_empty())
            else {
                continue;
            };
            done[i] = true;
            grew = true;
            let mut vars = Vec::new();
            ctor_vars(&g, &r, &mut vars)?;
            for var in vars {
                if !found.iter().any(|(f, _)| *f == var) {
                    found.push((var, root));
                }
            }
        }
        if !grew {
            break;
        }
    }
    Ok(found)
}

/// The deeper splits a case may still make once every named value is
/// split: the fields of their splits not split yet, of a type `cases`
/// splits (data that isn't recursive, a record too) and mentioned by the
/// goal or a hypothesis, in the order split; each with how it is shown.
fn named_candidates(cx: &Ctx, run: &Run, goal: &Value) -> Result<Vec<Planned>> {
    let g = cx.g();
    let n = cx.level();
    let finder = Finder::new(cx, run);
    let mut mentioned = crate::matching::free_levels(&cx.quote_folded(goal)?, n);
    for level in visible(cx) {
        if !is_equation(cx, level) {
            mentioned.extend(crate::matching::free_levels(
                &cx.quote_folded(&cx.types[level])?,
                n,
            ));
        }
    }
    let mut out = Vec::new();
    for (level, root) in named_fields(cx, run)? {
        if !mentioned.contains(&level) || stale(cx, level) || is_equation(cx, level) {
            continue;
        }
        let Value::Data(d, _) = force(&g, cx.types[level].clone())? else {
            continue;
        };
        if finder.ctors(d).is_none() || finder.is_known(&Value::var(level))? {
            continue;
        }
        let field = cx.show(&Value::var(level));
        out.push(Planned {
            split: NamedSplit::Data(level, d),
            root,
            shown: format!(
                "`{field} : {}`, a field of `{}`",
                cx.show(&cx.types[level]),
                run.targets[root].text
            ),
        });
    }
    Ok(out)
}

/// A case of `cases x, y then t` with every named value split, that
/// neither the closers nor `t` closed: a field of a named split is split
/// further, the one the goal is stuck on first; otherwise
/// `arithmetic`, deciding the goal, introducing its binders and applying an
/// implication are tried, as `cases` tries them; then any field still
/// mentioned. Nothing the proof didn't name is split.
fn named_rest(
    cx: &mut Ctx,
    run: &Rc<Run>,
    goal: &Value,
    failed_body: Option<Diagnostic>,
) -> Result<Term> {
    let g = cx.g();
    let mut candidates = named_candidates(cx, run, goal)?;
    if !candidates.is_empty() {
        let atom = Finder::new(cx, run).find(goal)?;
        let stuck_on = atom.and_then(|atom| match force(&g, atom.value).ok()? {
            Value::Neutral(Head::Var(level, _, _), spine) if spine.is_empty() => Some(level),
            _ => None,
        });
        if let Some(at) = candidates
            .iter()
            .position(|c| matches!(c.split, NamedSplit::Data(l, _) if Some(l) == stuck_on))
        {
            return named_split(cx, run, candidates.swap_remove(at), goal);
        }
    }
    if let Some(term) = crate::omega::prove_case(cx, goal, run.span)? {
        run.closed.borrow_mut().omega += 1;
        return Ok(term);
    }
    let decided = by_decision(cx, goal)?;
    if let Decided::Yes(term) = decided {
        run.closed.borrow_mut().decision += 1;
        return Ok(term);
    }
    if let Some(term) = introduce(cx, run, goal)? {
        return Ok(term);
    }
    if let Some(term) = apply_to_part(cx, run, goal)? {
        run.closed.borrow_mut().hypothesis += 1;
        return Ok(term);
    }
    if !candidates.is_empty() {
        return named_split(cx, run, candidates.remove(0), goal);
    }
    let error = open_case(cx, run, goal, None, failed_body);
    Err(match decided {
        Decided::No if !visibly_false(cx, goal)? => {
            error.with_note("the goal's decision procedure says it is false")
        }
        _ => error,
    })
}

/// Whether `goal` is an equation between two constructors or literals
/// (`False = True`), which the note on the goal shows to be false already.
fn visibly_false(cx: &Ctx, goal: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(&g, goal.clone())? {
        Value::Eq(_, l, r) => {
            is_ctor_form(&force(&g, (*l).clone())?) && is_ctor_form(&force(&g, (*r).clone())?)
        }
        _ => false,
    })
}

/// What the decision closer made of a goal.
enum Decided {
    /// Its decision procedure's test is `True`: the proof.
    Yes(Term),
    /// The test is `False`. The case isn't failed for that: its hypotheses may
    /// still contradict each other (decide/closer_order.sw,
    /// `falseGoalImpossibleCase`), which a later step may show.
    No,
    /// No procedure was found, or running it got stuck.
    Unknown,
}

/// The decision closer (docs/proposals/decide.md §6.1.2): the goal's
/// decision procedure, found as `auto` finds one (`auto::decide`), run now,
/// and when its test is `True` the proof `d.sound byComputing` (`auto::from_yes`).
///
/// Trust: nothing new enters the trusted base. The term is the one `auto`
/// writes for `[auto h: P]`; the kernel checks it by running `d` again
/// itself, as it does for `auto`, so running it here is only to choose the
/// closer and to say what happened, never what is believed.
fn by_decision(cx: &mut Ctx, goal: &Value) -> Result<Decided> {
    let goal = force(&cx.g(), goal.clone())?;
    if !is_proposition(cx, &goal)? {
        return Ok(Decided::Unknown);
    }
    let mut no = false;
    let found = crate::undo::transaction(cx, |cx| {
        let decision = match crate::auto::decide(cx, &goal, 0) {
            Ok(decision) => decision,
            Err(e) if crate::undo::fatal(&e) => return Err(e),
            Err(_) => return Ok(None),
        };
        match crate::auto::verdict(cx, &decision)? {
            Some(true) => crate::auto::from_yes(cx, &goal, decision).map(Some),
            Some(false) => {
                no = true;
                Ok(None)
            }
            None => Ok(None),
        }
    })?;
    Ok(match found {
        Some(term) => Decided::Yes(term),
        None if no => Decided::No,
        None => Decided::Unknown,
    })
}

/// The prefix of the names unnamed binders are introduced under: not one a
/// program can write.
const UNNAMED: &str = "%hyp";

/// A goal that is a `Π`, introduced (docs/proposals/decide.md §6.1.1): every
/// leading binder, explicit, implicit and `auto`, whatever its type, bound
/// under its written name, or an unnamed one (`A → B`) under `%hypN`, and
/// the case goes on under them. The proof is one lambda per binder, the
/// term `x y => cases` elaborates to. `None` if the goal isn't a `Π`.
fn introduce(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let mut goal = force(&g, goal.clone())?;
    if !matches!(goal, Value::Pi(..)) {
        return Ok(None);
    }
    let mark = cx.mark();
    let mut binders: Vec<(Name, Icit)> = Vec::new();
    while let Value::Pi(x, icit, dom, cod, _) = goal {
        let var = Value::var(cx.level());
        let name = if &*x == "_" || x.is_empty() {
            let unnamed = cx.names.iter().filter(|n| n.starts_with(UNNAMED)).count();
            Name::from(format!("{UNNAMED}{}", unnamed + 1).as_str())
        } else {
            x.clone()
        };
        cx.bind(&name, (*dom).clone());
        if icit != Icit::Explicit {
            cx.set_kind(icit);
        }
        binders.push((name, icit));
        goal = force(&g, cod.apply(&g, var)?)?;
    }
    let body = node(cx, run, &goal);
    cx.reset(mark);
    let mut body = body?;
    for (name, icit) in binders.into_iter().rev() {
        body = Term::Lam(name, icit, Rc::new(body), ProofMark::Unknown);
    }
    Ok(Some(body))
}

/// How the hypothesis at `level` is shown: its name, for one introduced
/// from an unnamed binder `hypothesis N (unnamed)`, and for a fact `cases`
/// added (`%factN`, which can't be written) `fact N (added by cases)`.
fn hypothesis_name(cx: &Ctx, level: usize, name: &str) -> String {
    if &*cx.names[level] != name {
        return name.to_string();
    }
    if let Some(n) = name.strip_prefix(UNNAMED) {
        return format!("hypothesis {n} (unnamed)");
    }
    match name.strip_prefix(FACT) {
        Some(n) => format!("fact {n} (added by `cases`)"),
        None => name.to_string(),
    }
}

/// The prefix of the names of the facts `cases` adds: not one a program can
/// write.
const FACT: &str = "%fact";

/// The equations of the splits made on the way to this case, oldest first,
/// as shown: the latest copy of each.
fn path(cx: &Ctx) -> Vec<String> {
    (0..cx.level())
        .filter(|&l| is_equation(cx, l) && cx.name_of_level(l).is_some())
        .map(|l| {
            // A split is shown as the assignment it is, `b = True`, not as
            // the fact `b` that goals show it as.
            let shown = match force(&cx.g(), cx.types[l].clone()) {
                Ok(Value::Eq(_, a, b)) => format!("{} = {}", cx.show_side(&a), cx.show_side(&b)),
                _ => cx.show(&cx.types[l]),
            };
            if is_fallback(cx, l) {
                format!("{shown} (fallback)")
            } else {
                shown
            }
        })
        .collect()
}

/// The end of the names of the equations of fallback splits.
const FALLBACK: &str = "%fallback";

/// Whether the variable at `level` is the equation of a fallback split.
fn is_fallback(cx: &Ctx, level: usize) -> bool {
    is_equation(cx, level) && cx.names[level].ends_with(FALLBACK)
}

/// Whether the variable at `level` is a hypothesis a generalising `match`
/// has copied: it can't be referred to, and a later variable of the same
/// name can.
pub(crate) fn stale(cx: &Ctx, level: usize) -> bool {
    cx.name_of_level(level).is_none()
        && (level + 1..cx.level())
            .any(|l| cx.names[l] == cx.names[level] && cx.name_of_level(l).is_some())
}

fn is_equation(cx: &Ctx, level: usize) -> bool {
    cx.names[level].starts_with(EQUATION)
}

/// `E-CASES` for a case nothing closed, with nothing left to split.
fn open_case(
    cx: &Ctx,
    run: &Run,
    goal: &Value,
    stuck: Option<Stuck>,
    failed_body: Option<Diagnostic>,
) -> Diagnostic {
    let path = path(cx);
    let case = if path.is_empty() {
        String::new()
    } else {
        path.join(", ")
    };
    if let Some(e) = failed_body {
        let note = if case.is_empty() {
            "`cases` found nothing to split on, and this is what the term after `then` gave"
                .to_string()
        } else {
            format!("in the case {case}, this is what the term after `then` gave")
        };
        return e.with_note(note);
    }
    let mut d = if case.is_empty() {
        Diagnostic::error(
            "E-CASES",
            "`cases` found nothing to split on, and nothing closes the goal",
        )
        .with_label(run.span, "this `cases`")
    } else {
        Diagnostic::error(
            "E-CASES",
            format!("`cases` couldn't close the case it reached by the splits {case}"),
        )
        .with_label(run.span, "this `cases`")
    };
    for level in 0..cx.level() {
        if is_equation(cx, level) {
            continue;
        }
        let Some(name) = cx.name_of_level(level) else {
            continue;
        };
        if run
            .substituted
            .borrow()
            .iter()
            .any(|(n, _)| *n == cx.names[level])
        {
            continue;
        }
        if is_fact(cx, &cx.types[level]) && !trivial(cx, &cx.types[level]) {
            d = d.with_note(format!(
                "{}: {}",
                hypothesis_name(cx, level, name),
                cx.show(&cx.types[level])
            ));
        }
    }
    for (_, shown) in run.substituted.borrow().iter() {
        d = d.with_note(shown.clone());
    }
    d = d.with_note(format!("goal: {}", cx.show(goal)));
    // The case's own equations hold the atoms split on, where an unused
    // equation's left side may be (SW-882).
    let mut searched = vec![goal];
    searched.extend(
        (0..cx.level())
            .filter(|&l| is_equation(cx, l))
            .map(|l| &cx.types[l]),
    );
    d = cx.with_unused_equation_notes(d, &searched);
    let d = match stuck {
        Some(Stuck { what, ty, again }) => {
            let a = if ty.starts_with(['A', 'E', 'I', 'O', 'U']) {
                "an"
            } else {
                "a"
            };
            d.with_note(if again {
                format!(
                    "it stopped here because the goal is stuck on `{what}`, {a} `{ty}` that is \
                     part of one `cases` took apart already: taking it apart again would be \
                     induction, which is written as recursion (a `match` whose arm calls the \
                     theorem on `{what}`)"
                )
            } else {
                format!(
                    "it stopped here because the goal is stuck on `{what}`, {a} `{ty}`, which \
                     `cases` doesn't take apart; give this case's proof as `cases then t`"
                )
            })
        }
        None => d.with_generic_note(
            "the goal isn't stuck on anything `cases` can take apart, and neither `byComputing`, a \
             contradiction, a hypothesis, `arithmetic` nor deciding it (as `byDecision` does) proves \
             it; give this case's proof as `cases then t`",
        ),
    };
    // The fallback splits on the way here, by what they split.
    let fallbacks: Vec<String> = (0..cx.level())
        .filter(|&l| is_fallback(cx, l) && cx.name_of_level(l).is_some())
        .filter_map(|l| match force(&cx.g(), cx.types[l].clone()) {
            Ok(Value::Eq(_, split, _)) => Some(format!("`{}`", cx.show(&split))),
            _ => None,
        })
        .collect();
    if fallbacks.is_empty() {
        return d;
    }
    d.with_note(format!(
        "it split {} as a fallback, though the goal wasn't stuck on {}",
        fallbacks.join(", "),
        if fallbacks.len() == 1 { "it" } else { "them" }
    ))
}

/// Whether `ty` is an equation whose sides compute to the same thing, such
/// as the copy `Some x = Some x` a substitution leaves of `Some x = Some y`:
/// it says nothing, so `E-CASES` doesn't show it.
fn trivial(cx: &Ctx, ty: &Value) -> bool {
    match force(&cx.g(), ty.clone()) {
        Ok(Value::Eq(_, l, r)) => cx.conv_now(&l, &r).unwrap_or(false),
        _ => false,
    }
}

/// Whether a hypothesis of type `ty` is worth showing: a proposition, as
/// far as can be told cheaply (an equation, or a type of proofs).
fn is_fact(cx: &Ctx, ty: &Value) -> bool {
    match force(&cx.g(), ty.clone()) {
        Ok(Value::Eq(..)) => true,
        Ok(Value::Data(d, _)) => cx.g().data(d).sort() == Sort::Prop,
        Ok(Value::Neutral(Head::Def(_), _)) => true,
        _ => false,
    }
}

// The closers.

/// `cases`' closers that don't split or search: a contradiction among the
/// hypotheses, a hypothesis of the goal's type, or a part of one. For
/// `rewrite repeatedly`, after computing has failed to close the goal.
pub(crate) fn close_by_hypotheses(cx: &mut Ctx, goal: &Value) -> Result<Option<Term>> {
    if let Some(term) = by_contradiction(cx, goal, &visible(cx))? {
        return Ok(Some(term));
    }
    if let Some(term) = by_hypothesis(cx, goal)? {
        return Ok(Some(term));
    }
    by_hypothesis_part(cx, goal)
}

fn by_computation(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    if let Value::Eq(_, l, r) = force(&cx.g(), goal.clone())?
        && cx.conv_now(&l, &r)?
    {
        return Ok(Some(Term::Refl));
    }
    Ok(None)
}

/// The hypotheses that can be referred to, by level, latest first: a
/// variable's latest copy, never a stale one.
fn visible(cx: &Ctx) -> Vec<usize> {
    (0..cx.level())
        .rev()
        .filter(|&l| cx.name_of_level(l).is_some())
        .collect()
}

fn by_hypothesis(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    let levels = visible(cx);
    let found = |l: usize| Ok(Some(Term::Var(cx.level() - 1 - l)));
    for &level in &levels {
        if conv(&cx.g(), cx.level(), &cx.types[level], goal)? {
            return found(level);
        }
    }
    // Again with what's been solved since the goal or a hypothesis was
    // computed (`Ctx::conv_now`), the goal computed again only once.
    if cx.metas().meta_trail.borrow().is_empty() {
        return Ok(None);
    }
    let goal = crate::interfaces::refresh(cx, goal)?;
    for level in levels {
        let ty = crate::interfaces::refresh(cx, &cx.types[level])?;
        if conv(&cx.g(), cx.level(), &ty, &goal)? {
            return found(level);
        }
    }
    Ok(None)
}

/// A part of a hypothesis of exactly the goal's type: a side of a
/// conjunction, or what a test fact reads as, taken apart in turn
/// (`auto::hypothesis_parts`; docs/proposals/bool-as-proposition.md §9).
fn by_hypothesis_part(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    Parts::of(cx, &visible(cx))?.find(cx, goal)
}

/// The parts of the hypotheses in scope (`auto::hypothesis_parts`), and
/// whether reading them stopped at its bound with test facts left unread.
struct Parts {
    parts: Vec<(Term, Value)>,
    cut: bool,
    levels: Vec<usize>,
    /// The sides of the hypotheses' `&&`s, collected when first needed.
    and_sides: std::cell::OnceCell<crate::auto::AndSides>,
}

impl Parts {
    fn of(cx: &Ctx, levels: &[usize]) -> Result<Parts> {
        let (parts, cut) = crate::auto::hypothesis_parts_cut(cx, levels)?;
        Ok(Parts {
            parts,
            cut,
            levels: levels.to_vec(),
            and_sides: std::cell::OnceCell::new(),
        })
    }

    /// A part of type `goal`; or, where reading stopped at its bound, a
    /// side of a hypothesis's `&&` that is the goal `t = True`
    /// ([`auto::AndSides`]).
    fn find(&self, cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
        for (proof, ty) in &self.parts {
            if conv(&cx.g(), cx.level(), ty, goal)? {
                return Ok(Some(proof.clone()));
            }
        }
        if self.cut {
            if self.and_sides.get().is_none() {
                let sides = crate::auto::AndSides::collect(cx, &self.levels)?;
                let _ = self.and_sides.set(sides);
            }
            if let Some(sides) = self.and_sides.get() {
                return sides.find(cx, goal);
            }
        }
        Ok(None)
    }
}

/// The most levels of `∧` [`by_parts`] goes into: past it the goal is left
/// to the other closers.
const MAX_CONJUNCTS_DEPTH: usize = 16;

/// The two parts of `goal`, if it is a conjunction `p ∧ q`, and its type.
pub(crate) fn conjuncts(cx: &Ctx, goal: &Value) -> Result<Option<(DataId, Value, Value)>> {
    if let Value::Data(d, args) = force(&cx.g(), goal.clone())?
        && cx.g().env.registry().is_data(Builtin::And, d)
        && args.len() == 2
    {
        return Ok(Some((d, args[0].clone(), args[1].clone())));
    }
    Ok(None)
}

/// The parts of `goal` if it is a conjunction `p ∧ q` (its two sides) or a
/// record of proofs (its fields' statements, `facts::is_record_of_proofs`),
/// with its type: what [`by_parts`] proves one by one.
fn goal_parts(cx: &Ctx, goal: &Value) -> Result<Option<(DataId, Vec<Value>)>> {
    if let Some((and, p, q)) = conjuncts(cx, goal)? {
        return Ok(Some((and, vec![p, q])));
    }
    let g = cx.g();
    let Value::Data(d, args) = force(&g, goal.clone())? else {
        return Ok(None);
    };
    if !crate::facts::is_record_of_proofs(cx, d) {
        return Ok(None);
    }
    let data = g.data(d);
    let np = data.params().len();
    let mut parts = Vec::new();
    // No field's type mentions an earlier field, so `Refl` stands for each.
    for (i, (_, field_ty)) in data.ctors()[0].fields.iter().enumerate() {
        let env: Vec<Value> = args[..np]
            .iter()
            .cloned()
            .chain(std::iter::repeat_n(Value::Refl, i))
            .collect();
        parts.push(eval(&g, &env, field_ty)?);
    }
    Ok(Some((d, parts)))
}

/// A conjunction, or a record of proofs, each of whose parts closes by
/// computing, by a hypothesis or a part of one, or is such a conjunction or
/// record in turn: the pair (or record) of their proofs. No search: each
/// part is tried by those closers only, so a goal that is already proved
/// (`True = True ∧ (a == a) = True`) closes at once, and doesn't wait for a
/// split or a decision procedure.
fn by_parts(cx: &Ctx, goal: &Value) -> Result<Option<Term>> {
    if goal_parts(cx, goal)?.is_none() {
        return Ok(None);
    }
    // The hypotheses' parts are taken apart once, for every part of the goal.
    let mut parts = None;
    by_parts_at(cx, goal, 0, &mut parts)
}

fn by_parts_at(
    cx: &Ctx,
    goal: &Value,
    depth: usize,
    parts: &mut Option<Parts>,
) -> Result<Option<Term>> {
    if depth >= MAX_CONJUNCTS_DEPTH {
        return Ok(None);
    }
    let Some((d, goals)) = goal_parts(cx, goal)? else {
        return Ok(None);
    };
    let mut proofs = Vec::with_capacity(goals.len());
    for part in goals {
        let mut proof = by_computation(cx, &part)?;
        if proof.is_none() {
            proof = by_hypothesis(cx, &part)?;
        }
        if proof.is_none() {
            let parts = match parts {
                Some(parts) => parts,
                None => parts.insert(Parts::of(cx, &visible(cx))?),
            };
            proof = parts.find(cx, &part)?;
        }
        if proof.is_none() {
            proof = by_parts_at(cx, &part, depth + 1, parts)?;
        }
        match proof {
            Some(proof) => proofs.push(proof),
            None => return Ok(None),
        }
    }
    Ok(Some(Term::ctor(d, 0, proofs)))
}

/// An equation `l = r` of data `d` whose sides compute to constructors.
struct CtorEquation {
    level: usize,
    ty: Value,
    d: DataId,
    left: (usize, Vec<Value>),
    right: (usize, Vec<Value>),
}

fn ctor_equations(cx: &Ctx, levels: &[usize]) -> Result<Vec<CtorEquation>> {
    let mut out = Vec::new();
    for &level in levels {
        out.extend(ctor_equation(cx, level)?);
    }
    Ok(out)
}

/// The variable at `level`, if its type equates two constructors of a data
/// type that isn't a proposition or an indexed family.
fn ctor_equation(cx: &Ctx, level: usize) -> Result<Option<CtorEquation>> {
    let g = cx.g();
    let Value::Eq(ty, l, r) = force(&g, cx.types[level].clone())? else {
        return Ok(None);
    };
    let (Value::Ctor(d, c1, f1), Value::Ctor(d2, c2, f2)) =
        (force(&g, (*l).clone())?, force(&g, (*r).clone())?)
    else {
        return Ok(None);
    };
    if d != d2 || g.data(d).sort() == Sort::Prop || !g.data(d).indices().is_empty() {
        return Ok(None);
    }
    Ok(Some(CtorEquation {
        level,
        ty: (*ty).clone(),
        d,
        left: (c1, f1.to_vec()),
        right: (c2, f2.to_vec()),
    }))
}

/// Whether the variable at `level` has a type that equates two different
/// constructors, which [`refute_equation`] refutes.
pub(crate) fn equates_different_ctors(cx: &Ctx, level: usize) -> Result<bool> {
    Ok(ctor_equation(cx, level)?.is_some_and(|eq| eq.left.0 != eq.right.0))
}

/// The variable at `level`'s equation with its sides computed, as it would
/// read in a message (`Equal = Less`), when that differs from how it's
/// written: what [`equates_different_ctors`] refutes, and why. Only asked
/// once a reason is found.
pub(crate) fn computed_equation(cx: &Ctx, level: usize) -> Result<Option<String>> {
    let g = cx.g();
    let Value::Eq(_, l, r) = force(&g, cx.types[level].clone())? else {
        return Ok(None);
    };
    let (left, right) = (force(&g, (*l).clone())?, force(&g, (*r).clone())?);
    let written = format!("{} = {}", cx.show_side(&l), cx.show_side(&r));
    let computed = format!("{} = {}", cx.show_side(&left), cx.show_side(&right));
    Ok((written != computed).then_some(computed))
}

/// A proof of `goal` from the variable at `level`, when its type equates
/// two different constructors (an argument matched by `()`).
pub(crate) fn refute_equation(cx: &mut Ctx, level: usize, goal: &Value) -> Result<Option<Term>> {
    match ctor_equation(cx, level)? {
        Some(eq) if eq.left.0 != eq.right.0 => contradiction(cx, eq, goal).map(Some),
        _ => Ok(None),
    }
}

/// A proof of `goal` from hypotheses that can't both hold: an equation
/// between different constructors, or `e = True` beside `e = False`. (`auto`
/// uses it too, over every level: its context has no names.) `levels` are
/// the hypotheses to look at.
pub(crate) fn by_contradiction(
    cx: &mut Ctx,
    goal: &Value,
    levels: &[usize],
) -> Result<Option<Term>> {
    if let Some(eq) = ctor_equations(cx, levels)?
        .into_iter()
        .find(|e| e.left.0 != e.right.0)
    {
        return contradiction(cx, eq, goal).map(Some);
    }
    bool_clash(cx, goal, levels)
}

/// A hypothesis `e = C` or `C = e` (`C` a Bool constructor, `e` a Bool term
/// that doesn't compute to one), as `(level, e, C is True, C on the left)`.
fn bool_facts(cx: &Ctx, levels: &[usize]) -> Result<Vec<(usize, Value, bool, bool)>> {
    let g = cx.g();
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    let tru = builtin_ctor(cx, Builtin::True)?.1;
    let mut out = Vec::new();
    for &level in levels {
        let Value::Eq(ty, l, r) = force(&g, cx.types[level].clone())? else {
            continue;
        };
        if !matches!(force(&g, (*ty).clone())?, Value::Data(d, _) if d == bool_data) {
            continue;
        }
        let (l, r) = (force(&g, (*l).clone())?, force(&g, (*r).clone())?);
        let ctor = |v: &Value| match v {
            Value::Ctor(d, c, _) if *d == bool_data => Some(*c == tru),
            _ => None,
        };
        match (ctor(&l), ctor(&r)) {
            (None, Some(is_true)) => out.push((level, l, is_true, false)),
            (Some(is_true), None) => out.push((level, r, is_true, true)),
            _ => {}
        }
    }
    Ok(out)
}

/// Hypotheses `h1: e = True` and `h2: e = False` (either way round) for the
/// same `e`, whatever `e` is: no reader or decision needed.
///
/// With both turned to the form `e = C` (a `J` along `C = e` into `y = C`,
/// when the constructor is on the left), the proof of `False = True` is
/// two `J`s: along `h2` into `y = e`, from `byComputing`, gives `False = e`; along
/// `h1` into `False = y`, from that, gives `False = True`. `Bool.falseNotTrue`
/// refutes it.
fn bool_clash(cx: &mut Ctx, goal: &Value, levels: &[usize]) -> Result<Option<Term>> {
    let facts = bool_facts(cx, levels)?;
    let g = cx.g();
    let mut pair = None;
    'search: for a in &facts {
        if !a.2 {
            continue;
        }
        for b in &facts {
            if !b.2 && conv(&g, cx.level(), &a.1, &b.1)? {
                pair = Some((a.clone(), b.clone()));
                break 'search;
            }
        }
    }
    let Some(((t_level, e, _, t_left), (f_level, _, _, f_left))) = pair else {
        return Ok(None);
    };
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    let bool_ty = || Some(Rc::new(Term::data(bool_data, Vec::new())));
    let (tru, fls) = (
        builtin_ctor(cx, Builtin::True)?,
        builtin_ctor(cx, Builtin::False)?,
    );
    let ctor = |(d, c): (DataId, usize)| Term::ctor(d, c, Vec::new());
    let motive = |body: Term| {
        Term::Lam(
            "y".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "q".into(),
                Icit::Explicit,
                Rc::new(body),
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        )
    };
    let var = |level: usize| Term::Var(cx.level() - 1 - level);
    // `h: C = e` turned into `e = C`.
    let turned = |h: Term, c: Term, flipped: bool| {
        if !flipped {
            return h;
        }
        let body = Term::Eq(bool_ty(), Rc::new(Term::Var(1)), Rc::new(c));
        Term::J(
            Rc::new(motive(body)),
            Rc::new(Term::Refl),
            Rc::new(h),
            ProofMark::Unknown,
        )
    };
    let e_term = cx.quote_or_written(&e)?;
    let h_true = turned(var(t_level), ctor(tru), t_left);
    let h_false = turned(var(f_level), ctor(fls), f_left);
    let e_under = e_term.shift(&g, 2, 0)?;
    let back = Term::Eq(bool_ty(), Rc::new(Term::Var(1)), Rc::new(e_under));
    let false_eq_e = Term::J(
        Rc::new(motive(back)),
        Rc::new(Term::Refl),
        Rc::new(h_false),
        ProofMark::Unknown,
    );
    let forward = Term::Eq(bool_ty(), Rc::new(ctor(fls)), Rc::new(Term::Var(1)));
    let false_eq_true = Term::J(
        Rc::new(motive(forward)),
        Rc::new(false_eq_e),
        Rc::new(h_true),
        ProofMark::Unknown,
    );
    let void_proof = Term::app(
        Term::Def(builtin_def(cx, Builtin::FalseNotTrue)?),
        false_eq_true,
    );
    absurd(cx, void_proof, goal).map(Some)
}

/// `Void.impossible` (or `Void.absurd`, for a goal that isn't a proposition)
/// of `J (y q => D y) Trivial h`, where `D` is a helper that is `Unit` at
/// `h`'s left constructor and `Void` at the others. Two kinds of equation
/// need no helper: on `Bool`, `Bool.falseNotTrue`, and on `Ordering`, its
/// six lemmas such as `Ordering.lessNotEqual`, once they're bound. The
/// `compare` laws meet `Ordering`'s equations in most of their cases, and
/// a helper for each would be a declaration of its own.
fn contradiction(cx: &mut Ctx, eq: CtorEquation, goal: &Value) -> Result<Term> {
    let h = Term::Var(cx.level() - 1 - eq.level);
    if let Some(lemma) = ordering_distinct(cx, &eq) {
        return absurd(cx, Term::app(Term::Def(lemma), h), goal);
    }
    let g = cx.g();
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    // Until the prelude has admitted `Bool.falseNotTrue`, a `Bool` equation
    // takes the helper below like any other type's; that is how the lemma
    // itself is proved, by `()`.
    let false_not_true = g.env.registry().def(Builtin::FalseNotTrue);
    let void_proof = if let (true, Some(lemma)) = (eq.d == bool_data, false_not_true) {
        // `Bool.falseNotTrue h`, or for `h: True = False`, of `h` turned
        // round by `J (y q => y = True) byComputing h`.
        let tru = builtin_ctor(cx, Builtin::True)?;
        let false_true = if eq.left.0 == tru.1 {
            let motive_body = Term::Eq(
                Some(Rc::new(Term::data(bool_data, Vec::new()))),
                Rc::new(Term::Var(1)),
                Rc::new(Term::ctor(tru.0, tru.1, Vec::new())),
            );
            let motive = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam(
                    "q".into(),
                    Icit::Explicit,
                    Rc::new(motive_body),
                    ProofMark::Unknown,
                )),
                ProofMark::Unknown,
            );
            Term::J(
                Rc::new(motive),
                Rc::new(Term::Refl),
                Rc::new(h),
                ProofMark::Unknown,
            )
        } else {
            h
        };
        Term::app(Term::Def(lemma), false_true)
    } else {
        let unit = builtin_data(cx, Builtin::Unit)?;
        let void = builtin_data(cx, Builtin::Void)?;
        let trivial = builtin_ctor(cx, Builtin::Trivial)?;
        let data = g.data(eq.d);
        let branches: Vec<Branch> = data
            .ctors()
            .iter()
            .enumerate()
            .map(|(c, ctor)| Branch {
                names: ctor.fields.iter().map(|(n, _)| n.clone()).collect(),
                body: Some(Rc::new(Term::data(
                    if c == eq.left.0 { unit } else { void },
                    Vec::new(),
                ))),
            })
            .collect();
        let left = force(&g, cx.types[eq.level].clone())?;
        let Value::Eq(_, l, _) = left else {
            unreachable!("an equation")
        };
        let motive = family(cx, &eq.ty, &l, eq.d, branches, &Value::Sort(Sort::Prop))?;
        Term::J(
            Rc::new(motive),
            Rc::new(Term::ctor(trivial.0, trivial.1, Vec::new())),
            Rc::new(h),
            ProofMark::Unknown,
        )
    };
    absurd(cx, void_proof, goal)
}

/// The lemma refuting `eq` when it's an equation of two different
/// `Ordering`s (`Ordering.lessNotEqual` for `Less = Equal`): `None` for
/// another type, or while the prelude loads, before the lemma is admitted.
fn ordering_distinct(cx: &Ctx, eq: &CtorEquation) -> Option<stitchwort_core::DefId> {
    let g = cx.g();
    let registry = g.env.registry();
    if registry.data(Builtin::Ordering) != Some(eq.d) {
        return None;
    }
    let which = |c: usize| {
        [
            Builtin::OrderingLess,
            Builtin::OrderingEqual,
            Builtin::OrderingGreater,
        ]
        .into_iter()
        .find(|b| registry.ctor(*b) == Some((eq.d, c)))
    };
    let lemma = match (which(eq.left.0)?, which(eq.right.0)?) {
        (Builtin::OrderingLess, Builtin::OrderingEqual) => Builtin::LessNotEqual,
        (Builtin::OrderingLess, Builtin::OrderingGreater) => Builtin::LessNotGreater,
        (Builtin::OrderingEqual, Builtin::OrderingLess) => Builtin::EqualNotLess,
        (Builtin::OrderingEqual, Builtin::OrderingGreater) => Builtin::EqualNotGreater,
        (Builtin::OrderingGreater, Builtin::OrderingLess) => Builtin::GreaterNotLess,
        (Builtin::OrderingGreater, Builtin::OrderingEqual) => Builtin::GreaterNotEqual,
        _ => return None,
    };
    registry.def(lemma)
}

/// `goal` from a proof of `Void`: `Void.impossible` for a proposition,
/// `Void.absurd` otherwise.
pub(crate) fn absurd(cx: &mut Ctx, void_proof: Term, goal: &Value) -> Result<Term> {
    let goal_term = cx.quote_folded(goal)?;
    let via = if is_proposition(cx, goal)? {
        builtin_def(cx, Builtin::VoidImpossible)?
    } else {
        builtin_def(cx, Builtin::VoidAbsurd)?
    };
    Ok(Term::app(
        Term::app_icit(Term::Def(via), goal_term, Icit::Implicit),
        void_proof,
    ))
}

/// `y q => helper … y`, a motive for `J` along an equation `l = y` of type
/// `ty`, where the helper is lifted with the case tree `case y of branches`
/// (of type `result`, which mustn't mention `y`).
fn family(
    cx: &mut Ctx,
    ty: &Value,
    l: &Value,
    d: DataId,
    branches: Vec<Branch>,
    result: &Value,
) -> Result<Term> {
    let mark = cx.mark();
    let y = cx.level();
    cx.bind_hidden("y".into(), ty.clone());
    cx.bind_hidden(
        "q".into(),
        Value::Eq(
            Rc::new(ty.clone()).into(),
            Rc::new(l.clone()).into(),
            Rc::new(Value::var(y)).into(),
        ),
    );
    let body = Term::Case(1, d, branches.into());
    let call = crate::lift::draft(cx, cx.level(), Vec::new(), body, result, cx.span);
    cx.reset(mark);
    let call = call?;
    Ok(Term::Lam(
        "y".into(),
        Icit::Explicit,
        Rc::new(Term::Lam(
            "q".into(),
            Icit::Explicit,
            Rc::new(call),
            ProofMark::Unknown,
        )),
        ProofMark::Unknown,
    ))
}

pub(crate) fn is_proposition(cx: &Ctx, goal: &Value) -> Result<bool> {
    let g = cx.g();
    Ok(match force(&g, goal.clone())? {
        Value::Eq(..) => true,
        Value::Data(d, _) => g.data(d).sort() == Sort::Prop,
        other => {
            // The type read back as written first: its sort is the same as
            // its unfolding's, since a term has one type up to conversion
            // (no cumulativity, docs/core.md), and for a statement about a
            // large program (`SelfFollows self selfTwin`, a two-run walk's
            // premise) reading it back unfolded is most of the cost
            // (SW-4469). Not with an unknown in it, which the kernel can't
            // type, nor where the kernel refuses it: then as before.
            let folded = cx.quote_folded(&other)?;
            if !folded.subterms().any(|(t, _)| matches!(t, Term::Meta(_))) {
                let mut kcx = crate::rewrite::kernel_context(cx)?;
                match crate::kernel::without_glue(&g, || crate::kernel::infer(&mut kcx, &folded)) {
                    Ok((_, ty)) => return Ok(matches!(force(&g, ty)?, Value::Sort(Sort::Prop))),
                    Err(e) if crate::undo::fatal(&e) => return Err(e),
                    Err(_) => {}
                }
            }
            let term = cx.quote_unfolded(&other)?;
            let mut kcx = crate::rewrite::kernel_context(cx)?;
            match crate::kernel::without_glue(&g, || crate::kernel::infer(&mut kcx, &term)) {
                Ok((_, ty)) => matches!(force(&g, ty)?, Value::Sort(Sort::Prop)),
                Err(e) if crate::undo::fatal(&e) => return Err(e),
                Err(_) => true,
            }
        }
    })
}

/// A hypothesis `C a1 … = C b1 …` adds `ai = bi` for each field that
/// differs and isn't known equal already (§5.4, 3), as `let`s, and the case
/// starts again with them. `None` if there's nothing to add.
fn take_apart(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let mut facts: Vec<(usize, usize, Value, Value, Value)> = Vec::new();
    for eq in ctor_equations(cx, &visible(cx))? {
        if eq.left.0 != eq.right.0 {
            continue;
        }
        let ctor = &g.data(eq.d).ctors()[eq.left.0];
        for (i, (a, b)) in eq.left.1.iter().zip(&eq.right.1).enumerate() {
            // `mentions_fields` before `conv`: a field whose type depends on
            // an earlier field could have different types on the two sides,
            // and `conv` needs one type, as it skips proofs by position.
            if ctor.field_erased.get(i).copied().unwrap_or(false)
                || mentions_fields(&ctor.fields[i].1, i)
                || conv(&g, cx.level(), a, b)?
            {
                continue;
            }
            let Value::Data(_, params) = force(&g, eq.ty.clone())? else {
                continue;
            };
            // A field's type is in the context of the parameters and the
            // earlier fields (SW-975: evaluating it under the parameters
            // alone misread `List a` in `Cons`'s tail and `b` in a pair's
            // second field). It doesn't mention those fields (checked
            // above), so either side's fields will do; the left's are used.
            let np = g.data(eq.d).params().len();
            let env: Vec<Value> = params[..np]
                .iter()
                .chain(&eq.left.1[..i])
                .cloned()
                .collect();
            let field_ty = eval(&g, &env, &ctor.fields[i].1)?;
            let fact = Value::Eq(
                Rc::new(field_ty.clone()).into(),
                Rc::new(a.clone()).into(),
                Rc::new(b.clone()).into(),
            );
            if visible(cx)
                .into_iter()
                .any(|l| conv(&g, cx.level(), &cx.types[l], &fact).unwrap_or(false))
            {
                continue;
            }
            facts.push((eq.level, i, a.clone(), field_ty, fact));
        }
    }
    if facts.is_empty() {
        return Ok(None);
    }
    let mark = cx.mark();
    let mut lets = Vec::new();
    for (level, i, a, field_ty, fact) in facts {
        let proof = field_proof(cx, level, i, &a, &field_ty)?;
        let fact_term = cx.quote_or_written(&fact)?;
        run.facts.set(run.facts.get() + 1);
        let name = format!("{FACT}{}", run.facts.get());
        run.injected.borrow_mut().push(Name::from(name.as_str()));
        lets.push((Name::from(name.as_str()), fact_term.clone(), proof.clone()));
        cx.define(Some(&name), name.as_str().into(), fact, fact_term, proof)?;
    }
    let body = node(cx, run, goal);
    cx.reset(mark);
    let mut body = body?;
    for (name, ty, value) in lets.into_iter().rev() {
        body = Term::let_(name, ty, value, body);
    }
    Ok(Some(body))
}

/// The proof that field `i` of the constructor equation at `level` has
/// equal sides, `a = b` (`a` the left side's field, of type `field_ty`):
/// `J` along the equation with a projection ([`take_apart`]).
fn field_proof(cx: &mut Ctx, level: usize, i: usize, a: &Value, field_ty: &Value) -> Result<Term> {
    let g = cx.g();
    let Value::Eq(ty, l, _) = force(&g, cx.types[level].clone())? else {
        unreachable!("an equation")
    };
    let Value::Data(d, _) = force(&g, (*ty).clone())? else {
        unreachable!("data")
    };
    let data = g.data(d);
    let Value::Ctor(_, c, _) = force(&g, (*l).clone())? else {
        unreachable!("a constructor")
    };
    // `case y of C … fi … => fi | _ => a`, under each branch's fields.
    let a_term = cx.quote_or_written(a)?;
    let mut branches = Vec::new();
    for (k, ctor) in data.ctors().iter().enumerate() {
        let fields = ctor.fields.len();
        // The branch is under y, q and the fields.
        let body = if k == c {
            Term::Var(fields - 1 - i)
        } else {
            a_term.shift(&g, 2 + fields, 0)?
        };
        branches.push(Branch {
            names: ctor.fields.iter().map(|(n, _)| n.clone()).collect(),
            body: Some(Rc::new(body)),
        });
    }
    let project = family(cx, &ty, &l, d, branches, field_ty)?;
    // `J (y q => a = project y) byComputing h : a = project r`, which computes to
    // `a = b`.
    let Term::Lam(_, _, inner, _) = &project else {
        unreachable!("a lambda")
    };
    let Term::Lam(_, _, call, _) = &**inner else {
        unreachable!("a lambda")
    };
    let motive_body = Term::Eq(
        Some(Rc::new(cx.quote_or_written(field_ty)?.shift(&g, 2, 0)?)),
        Rc::new(a_term.shift(&g, 2, 0)?),
        call.clone(),
    );
    let motive = Term::Lam(
        "y".into(),
        Icit::Explicit,
        Rc::new(Term::Lam(
            "q".into(),
            Icit::Explicit,
            Rc::new(motive_body),
            ProofMark::Unknown,
        )),
        ProofMark::Unknown,
    );
    let proof = Term::J(
        Rc::new(motive),
        Rc::new(Term::Refl),
        Rc::new(Term::Var(cx.level() - 1 - level)),
        ProofMark::Unknown,
    );
    Ok(proof)
}

/// The equations a fact `C a… = C b…` at `level` gives for its fields
/// whose sides differ, as [`take_apart`] finds them: the field's number,
/// `aᵢ = bᵢ` and its proof. `None` if it isn't such an equation.
pub(crate) fn field_equations(
    cx: &mut Ctx,
    level: usize,
) -> Result<Option<Vec<(usize, Value, Term)>>> {
    let g = cx.g();
    let Some(eq) = ctor_equation(cx, level)? else {
        return Ok(None);
    };
    if eq.left.0 != eq.right.0 {
        return Ok(None);
    }
    let Value::Data(_, params) = force(&g, eq.ty.clone())? else {
        return Ok(None);
    };
    let ctor = &g.data(eq.d).ctors()[eq.left.0];
    let np = g.data(eq.d).params().len();
    let mut out = Vec::new();
    for (i, (a, b)) in eq.left.1.iter().zip(&eq.right.1).enumerate() {
        if ctor.field_erased.get(i).copied().unwrap_or(false)
            || mentions_fields(&ctor.fields[i].1, i)
            || conv(&g, cx.level(), a, b)?
        {
            continue;
        }
        let env: Vec<Value> = params[..np]
            .iter()
            .chain(&eq.left.1[..i])
            .cloned()
            .collect();
        let field_ty = eval(&g, &env, &ctor.fields[i].1)?;
        let fact = Value::Eq(
            Rc::new(field_ty.clone()).into(),
            Rc::new(a.clone()).into(),
            Rc::new(b.clone()).into(),
        );
        let proof = field_proof(cx, level, i, a, &field_ty)?;
        out.push((i, fact, proof));
    }
    Ok(Some(out))
}

/// A fact [`take_apart`] added, `x = t` or `t = x` with `x` a variable that
/// something else in scope mentions, eliminates `x` (SW-3344): `t` is put in
/// its place in the goal and in every hypothesis that mentions it, and the
/// case starts again. So `h: Some x = Some y` proves `f x = f y`. When both
/// sides are variables, the right one is replaced.
///
/// The hypotheses that mention `x` (and those that mention them) are
/// copied with `t` in its place, under their own names, so the originals
/// can no longer be referred to (as a split's copies replace them). The
/// proof is `J (z q => (d…: D… [z/x]) → G [z/x]) (d… => cases) e d…`,
/// where `e: t = x` is the fact, or the fact turned round by `J`. `None`
/// if no fact fits: `t` mentions `x`, or a hypothesis `t` mentions would
/// have to be copied, or nothing but the fact mentions `x`.
fn substitute(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let n = cx.level();
    let injected = run.injected.borrow().clone();
    // In `cases x then t` (SW-4474), a hypothesis as written, `kind =
    // Minus`, is used too: with a constructor on one side and a variable on
    // the other, it says what the split isn't allowed to learn by splitting
    // the variable. Plain `cases` doesn't, so its proofs keep their terms.
    let written = !run.targets.is_empty();
    if injected.is_empty() && !written {
        return Ok(None);
    }
    let substituted: Vec<Name> = run
        .substituted
        .borrow()
        .iter()
        .map(|(n, _)| n.clone())
        .collect();
    let visible = visible(cx);
    let mut facts: Vec<usize> = Vec::new();
    for &l in &visible {
        if substituted.contains(&cx.names[l]) {
            continue;
        }
        if injected.contains(&cx.names[l]) || written && written_fact(cx, l)? {
            facts.push(l);
        }
    }
    if facts.is_empty() {
        return Ok(None);
    }
    // The facts with a variable side, before anything is read back: most
    // nodes have none.
    let mut candidates = Vec::new();
    for fact in facts {
        let Value::Eq(a, l, r) = force(&g, cx.types[fact].clone())? else {
            continue;
        };
        let (l, r) = (force(&g, (*l).clone())?, force(&g, (*r).clone())?);
        for (var_on_right, side, other) in [(true, &r, &l), (false, &l, &r)] {
            let Value::Neutral(Head::Var(x, _, _), spine) = side else {
                continue;
            };
            let x = *x;
            if spine.is_empty() && crate::matching::is_var(&cx.env[x], x) && cx.lets[x].is_none() {
                candidates.push((fact, x, var_on_right, (*a).clone(), other.clone()));
            }
        }
    }
    if candidates.is_empty() {
        return Ok(None);
    }
    let goal_term = cx.quote_folded(goal)?;
    let goal_free = crate::matching::free_levels(&goal_term, n);
    let first = candidates.iter().map(|c| c.1).min().unwrap_or(n);
    let mut types: Vec<Option<Vec<usize>>> = vec![None; n];
    for (l, free) in types.iter_mut().enumerate().skip(first + 1) {
        *free = Some(crate::matching::free_levels(
            &cx.quote_folded(&cx.types[l])?,
            n,
        ));
    }
    let free_of = |l: usize| types[l].as_deref().unwrap_or(&[]);
    let mut found = None;
    for (fact, x, var_on_right, a, other) in candidates {
        // The hypotheses `x` reaches: those after it (but the fact) whose
        // type mentions it, or one reached already.
        let mut reached: Vec<usize> = Vec::new();
        for l in x + 1..n {
            if l != fact && free_of(l).iter().any(|&f| f == x || reached.contains(&f)) {
                reached.push(l);
            }
        }
        let other_free = crate::matching::free_levels(&cx.quote_folded(&other)?, n);
        let a_free = crate::matching::free_levels(&cx.quote_folded(&a)?, n);
        if other_free
            .iter()
            .chain(&a_free)
            .any(|&f| f == x || reached.contains(&f))
        {
            continue;
        }
        // Of those, what must be copied: the visible ones, and what the goal
        // or a copy mentions. A hidden one nothing copied mentions (an old
        // copy) is left as it is, as nothing can name it: copying those too
        // doubled the copies at each substitution (SW-3344 review, F2).
        let mut needed: Vec<usize> = reached
            .iter()
            .copied()
            .filter(|l| visible.contains(l) || goal_free.contains(l))
            .collect();
        let mut i = 0;
        while i < needed.len() {
            for &f in free_of(needed[i]) {
                if reached.contains(&f) && !needed.contains(&f) {
                    needed.push(f);
                }
            }
            i += 1;
        }
        needed.sort_unstable();
        if needed.is_empty() && !goal_free.contains(&x) {
            continue;
        }
        found = Some((fact, x, var_on_right, a, other, needed));
        break;
    }
    let Some((fact, x, var_on_right, a, t, deps)) = found else {
        return Ok(None);
    };
    let dep_types: Vec<Term> = deps
        .iter()
        .map(|&d| cx.quote_folded(&cx.types[d]))
        .collect::<Result<_>>()?;
    // `value` (a type or the goal, in the first `n` variables) with `x`
    // as `with`, and each copied hypothesis as its copy, from `copies` on.
    let replaced = |cx: &Ctx, value: &Term, with: Value, copies: usize| -> Result<Value> {
        let mut env = cx.env[..n].to_vec();
        env[x] = with;
        for (i, &d) in deps.iter().enumerate() {
            env[d] = Value::var(copies + i);
        }
        Ok(eval(&g, &env, value)?)
    };
    let copy_name =
        |cx: &Ctx, d: usize| (cx.name_of_level(d).map(str::to_string), cx.names[d].clone());

    // The motive, `z q => (d…: D… [z/x]) → G [z/x]`.
    let mark = cx.mark();
    let motive = (|| -> Result<Term> {
        let z = Value::var(n);
        cx.bind_hidden("z".into(), a.clone());
        let q_ty = Value::Eq(
            Rc::new(a.clone()).into(),
            Rc::new(t.clone()).into(),
            Rc::new(z.clone()).into(),
        );
        cx.bind_hidden("q".into(), q_ty);
        let mut pis = Vec::new();
        for (&d, d_ty) in deps.iter().zip(&dep_types) {
            let ty = replaced(cx, d_ty, z.clone(), n + 2)?;
            pis.push((cx.names[d].clone(), cx.quote_folded(&ty)?));
            cx.bind_hidden(cx.names[d].clone(), ty);
        }
        let goal = replaced(cx, &goal_term, z.clone(), n + 2)?;
        let mut body = cx.quote_folded(&goal)?;
        for (name, ty) in pis.into_iter().rev() {
            body = Term::Pi(
                name,
                Icit::Explicit,
                Rc::new(ty),
                Rc::new(body),
                ProofMark::Unknown,
            );
        }
        Ok(Term::Lam(
            "z".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "q".into(),
                Icit::Explicit,
                Rc::new(body),
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        ))
    })();
    cx.reset(mark);
    let motive = motive?;

    let shown = match cx.name_of_level(fact) {
        Some(name) if !injected.contains(&cx.names[fact]) => format!(
            "`{}` is replaced by `{}`: `{name}` says they are equal",
            cx.show(&Value::var(x)),
            cx.show(&t),
        ),
        _ => format!(
            "`{}` is replaced by `{}`: an equation `cases` took apart says they are equal",
            cx.show(&Value::var(x)),
            cx.show(&t),
        ),
    };
    // The base, `d… => cases`, with the copies in scope.
    let base = (|| -> Result<Term> {
        let mut names = Vec::new();
        for (&d, d_ty) in deps.iter().zip(&dep_types) {
            let ty = replaced(cx, d_ty, t.clone(), n)?;
            let (visible_name, name) = copy_name(cx, d);
            match visible_name {
                Some(shown) => cx.bind(&shown, ty),
                None => cx.bind_hidden(name.clone(), ty),
            }
            names.push(name);
        }
        // `x`'s name now stands for `t`, so a term after `then` that names it
        // still checks against the goal, which says `t` (review F1).
        let alias = match cx.name_of_level(x) {
            Some(name) => {
                let name = name.to_string();
                let (a_term, t_term) = (cx.quote_folded(&a)?, cx.quote_folded(&t)?);
                cx.define(
                    Some(&name),
                    name.as_str().into(),
                    a.clone(),
                    a_term.clone(),
                    t_term.clone(),
                )?;
                Some((Name::from(name.as_str()), a_term, t_term))
            }
            None => None,
        };
        let goal = replaced(cx, &goal_term, t.clone(), n)?;
        run.substituted
            .borrow_mut()
            .push((cx.names[fact].clone(), shown.clone()));
        let body = node(cx, run, &goal);
        run.substituted.borrow_mut().pop();
        let mut body = body?;
        if let Some((name, ty, value)) = alias {
            body = Term::let_(name, ty, value, body);
        }
        for name in names.into_iter().rev() {
            body = Term::Lam(name, Icit::Explicit, Rc::new(body), ProofMark::Unknown);
        }
        Ok(body)
    })();
    cx.reset(mark);
    let base = base?;

    let at = |l: usize| Term::Var(n - 1 - l);
    let equation = if var_on_right {
        at(fact)
    } else {
        // `J (z q => z = x) byComputing fact : t = x`.
        let a_term = cx.quote_folded(&a)?.shift(&g, 2, 0)?;
        let turn = Term::Eq(
            Some(Rc::new(a_term)),
            Rc::new(Term::Var(1)),
            Rc::new(Term::Var(n + 1 - x)),
        );
        let turn = Term::Lam(
            "z".into(),
            Icit::Explicit,
            Rc::new(Term::Lam(
                "q".into(),
                Icit::Explicit,
                Rc::new(turn),
                ProofMark::Unknown,
            )),
            ProofMark::Unknown,
        );
        Term::J(
            Rc::new(turn),
            Rc::new(Term::Refl),
            Rc::new(at(fact)),
            ProofMark::Unknown,
        )
    };
    let mut proof = Term::J(
        Rc::new(motive),
        Rc::new(base),
        Rc::new(equation),
        ProofMark::Unknown,
    );
    for &d in &deps {
        proof = Term::app(proof, at(d));
    }
    Ok(Some(proof))
}

/// Whether the hypothesis at `level`, one the proof has (not a fact `cases`
/// added, nor a split's equation), is an equation between a variable and a
/// constructor form: what [`substitute`] may use as written.
fn written_fact(cx: &Ctx, level: usize) -> Result<bool> {
    if is_equation(cx, level) {
        return Ok(false);
    }
    let g = cx.g();
    let Value::Eq(_, l, r) = force(&g, cx.types[level].clone())? else {
        return Ok(false);
    };
    let (l, r) = (force(&g, (*l).clone())?, force(&g, (*r).clone())?);
    let var = |v: &Value| matches!(v, Value::Neutral(Head::Var(..), spine) if spine.is_empty());
    Ok(var(&l) && is_ctor_form(&r) || var(&r) && is_ctor_form(&l))
}

/// A hypothesis `h: P → Q` (`Q` not mentioning the proof of `P`, `P` an
/// equation) whose premise holds in this case adds `Q`, as `h byComputing` when
/// `P`'s sides compute to the same thing (`b = True → fact`, after `b` was
/// split, generalised to `True = True → fact`), or as `h e` for a
/// hypothesis `e: P`; and the case starts again with it (SW-948). `None` if
/// there's nothing to add: every such `Q` is already a hypothesis.
fn apply_guarded(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let levels = visible(cx);
    // Each fact: its type, the hypothesis it comes from, and the premise's
    // proof (`None` for `byComputing`, else a hypothesis's level).
    let mut facts: Vec<(Value, usize, Option<usize>)> = Vec::new();
    for &level in &levels {
        let Value::Pi(_, Icit::Explicit, dom, closure, _) = force(&g, cx.types[level].clone())?
        else {
            continue;
        };
        if closure.body.mentions(0) {
            continue;
        }
        let premise = force(&g, (*dom).clone())?;
        let Value::Eq(_, l, r) = &premise else {
            continue;
        };
        let given = if cx.conv_now(l, r)? {
            None
        } else {
            let mut found = None;
            for &k in &levels {
                if k != level && conv(&g, cx.level(), &cx.types[k], &premise)? {
                    found = Some(k);
                    break;
                }
            }
            match found {
                Some(k) => Some(k),
                None => continue,
            }
        };
        let fact = closure.apply(&g, Value::Refl)?;
        if !is_fact(cx, &fact) && !matches!(force(&g, fact.clone())?, Value::Pi(..)) {
            continue;
        }
        let known = levels
            .iter()
            .any(|&k| conv(&g, cx.level(), &cx.types[k], &fact).unwrap_or(false))
            || facts
                .iter()
                .any(|(f, ..)| conv(&g, cx.level(), f, &fact).unwrap_or(false));
        if known {
            continue;
        }
        facts.push((fact, level, given));
    }
    if facts.is_empty() {
        return Ok(None);
    }
    let mark = cx.mark();
    let mut lets = Vec::new();
    for (fact, level, given) in facts {
        let at = |l: usize| Term::Var(cx.level() - 1 - l);
        let premise = match given {
            None => Term::Refl,
            Some(k) => at(k),
        };
        let proof = Term::app(at(level), premise);
        let fact_term = cx.quote_or_written(&fact)?;
        run.facts.set(run.facts.get() + 1);
        let name = format!("{FACT}{}", run.facts.get());
        lets.push((Name::from(name.as_str()), fact_term.clone(), proof.clone()));
        cx.define(Some(&name), name.as_str().into(), fact, fact_term, proof)?;
    }
    let body = node(cx, run, goal);
    cx.reset(mark);
    let mut body = body?;
    for (name, ty, value) in lets.into_iter().rev() {
        body = Term::let_(name, ty, value, body);
    }
    Ok(Some(body))
}

/// A hypothesis `h: P → Q` (`Q` not mentioning the proof of `P`) applied
/// once to a proof of `P` in scope that [`apply_guarded`] doesn't use: a
/// hypothesis whose `P` isn't an equation (a plain proposition `a: Prop`
/// too), or a part of a hypothesis (a side of a conjunction, or what a test
/// fact reads as). While `Q` is again such an implication whose premise is
/// in scope, it is applied to that too: `f: a → b → c`, `x: a` and `y: b`
/// add `c`. Each such last `Q` is added, and the case is closed by the
/// closers that don't split or search (a contradiction, a hypothesis or a
/// part of one, a conjunction or record of those), or `None`, with nothing
/// added. One application per implication, never chained: `ended: trails =
/// True ∧ Token w` and `implies: trails = True → trails' = True` prove
/// `trails' = True ∧ Token w`, but a `Q` added isn't a premise for another.
fn apply_to_part(cx: &mut Ctx, run: &Rc<Run>, goal: &Value) -> Result<Option<Term>> {
    let g = cx.g();
    let levels = visible(cx);
    let mut parts: Option<Parts> = None;
    let mut facts: Vec<(Value, usize, Vec<Term>)> = Vec::new();
    for &level in &levels {
        let mut ty = cx.types[level].clone();
        let mut givens = Vec::new();
        // At most one premise per binder of the hypothesis as written.
        while let Value::Pi(_, Icit::Explicit, dom, closure, _) = force(&g, ty.clone())? {
            if closure.body.mentions(0) {
                break;
            }
            let premise = (*dom).clone();
            if !premise_kind(cx, &premise)? {
                break;
            }
            let Some(given) = proof_in_scope(cx, level, &levels, &mut parts, &premise)? else {
                break;
            };
            givens.push(given);
            ty = closure.apply(&g, Value::Refl)?;
        }
        if givens.is_empty() {
            continue;
        }
        let fact = ty;
        let known = levels
            .iter()
            .any(|&k| conv(&g, cx.level(), &cx.types[k], &fact).unwrap_or(false));
        if known {
            continue;
        }
        facts.push((fact, level, givens));
    }
    if facts.is_empty() {
        return Ok(None);
    }
    let mark = cx.mark();
    let facts_before = run.facts.get();
    let mut lets = Vec::new();
    for (fact, level, givens) in facts {
        // Each given was read back before any fact was defined: each fact
        // defined since is one more binder over it.
        let mut proof = Term::Var(cx.level() - 1 - level);
        for given in givens {
            proof = Term::app(proof, given.shift(&g, lets.len(), 0)?);
        }
        let fact_term = cx.quote_or_written(&fact)?;
        run.facts.set(run.facts.get() + 1);
        let name = format!("{FACT}{}", run.facts.get());
        lets.push((Name::from(name.as_str()), fact_term.clone(), proof.clone()));
        cx.define(Some(&name), name.as_str().into(), fact, fact_term, proof)?;
    }
    let closed = match by_contradiction(cx, goal, &visible(cx))? {
        Some(term) => Some(term),
        None => match by_hypothesis(cx, goal)? {
            Some(term) => Some(term),
            None => match by_hypothesis_part(cx, goal)? {
                Some(term) => Some(term),
                None => by_parts(cx, goal)?,
            },
        },
    };
    cx.reset(mark);
    let Some(mut body) = closed else {
        run.facts.set(facts_before);
        return Ok(None);
    };
    for (name, ty, value) in lets.into_iter().rev() {
        body = Term::let_(name, ty, value, body);
    }
    Ok(Some(body))
}

/// Whether [`apply_to_part`] looks for a proof of `premise`: a fact as
/// [`is_fact`] sees it cheaply, or a plain proposition, a variable of type
/// `Prop` or one applied to arguments (`a`, `p x` for `p: Nat → Prop`),
/// as `byFacts` sees it (`facts::is_fact`). Not data: `f: Nat → Nat` is
/// never applied.
fn premise_kind(cx: &Ctx, premise: &Value) -> Result<bool> {
    if is_fact(cx, premise) {
        return Ok(true);
    }
    match force(&cx.g(), premise.clone())? {
        Value::Neutral(Head::Var(..), _) => crate::facts::is_fact(cx, premise),
        _ => Ok(false),
    }
}

/// A proof of `premise` in scope for the hypothesis at `level`: another
/// hypothesis of that type, or a part of one (`parts`, taken apart once).
fn proof_in_scope(
    cx: &Ctx,
    level: usize,
    levels: &[usize],
    parts: &mut Option<Parts>,
    premise: &Value,
) -> Result<Option<Term>> {
    let g = cx.g();
    for &k in levels {
        if k != level && conv(&g, cx.level(), &cx.types[k], premise)? {
            return Ok(Some(Term::Var(cx.level() - 1 - k)));
        }
    }
    let parts = match parts {
        Some(parts) => parts,
        None => parts.insert(Parts::of(cx, levels)?),
    };
    parts.find(cx, premise)
}

/// Whether field type `ty` (in the context of the parameters and the
/// previous `i` fields) mentions a previous field.
pub(crate) fn mentions_fields(ty: &Term, i: usize) -> bool {
    ty.subterms().any(|(t, under)| {
        matches!(t, Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..)
            if *ix >= under && *ix - under < i)
    })
}

// Finding what to split on.

/// What to split on: a value the goal or a hypothesis is stuck on, of data
/// type `d`.
struct Atom {
    value: Value,
    d: DataId,
    /// Whether it is a whole side of the goal's equation (`f x = True`), not
    /// something a definition tests.
    side: bool,
    /// For a number a definition compares with numbers (a `NumCase`): those
    /// numbers, split into one case each and one for the rest. `None`: split
    /// into the constructors.
    numbers: Option<Vec<BigUint>>,
}

struct Finder<'a, 'e> {
    cx: &'a Ctx<'e>,
    run: &'a Run,
    /// The first one-constructor atom met, split only if nothing else is.
    single: Option<Atom>,
    /// What the last resort splits, when nothing else is left
    /// ([`Finder::last_resort_atom`]): the innermost such value on the first
    /// chain that has one, the goal's before the hypotheses'.
    last_resort: Option<Atom>,
    /// The innermost value the goal is stuck on that isn't splittable:
    /// why a case with nothing to split stopped.
    stuck: Option<Stuck>,
    /// The split equations' left sides, as types hold them: values known
    /// in this case, never split again.
    known: Vec<Term>,
    /// The ones too large to read back ([`READ_BACK_NODES`]), compared as
    /// values.
    known_big: Vec<Value>,
    /// Values visited, against runaway sharing.
    visits: usize,
    in_goal: bool,
    /// How many stuck calls' arguments the walk is inside: a record
    /// is split only outside them.
    under_stuck: usize,
    /// The variables met in the goal, by level: the fallback's candidates.
    mentioned: Vec<usize>,
    /// Set for the survey pass ([`Finder::shared`]): `chain` records each
    /// chain instead of choosing an atom.
    survey: Option<Survey>,
    /// Set for the second try's look at the goal's structure
    /// ([`Finder::find`]): `chain` records only the last resort's split,
    /// whether or not an atom is outside it, and chooses no atom.
    resort_only: bool,
}

/// What the survey pass found (SW-939): the chains of stuck calls whose
/// innermost value is of a recursive type, which `cases` doesn't otherwise
/// split.
#[derive(Default)]
struct Survey {
    /// Every value on a chain so far, quoted: a stuck call met again inside
    /// another's chain isn't a chain of its own.
    seen: Vec<Term>,
    /// For each chain with an atom outside its innermost value, when that
    /// value's type is recursive: the value, quoted and as it is, and its
    /// type.
    ends: Vec<(Term, Value, DataId)>,
}

/// The most values the search for an atom visits in one case.
const VISITS: usize = 100_000;

impl<'a, 'e> Finder<'a, 'e> {
    fn new(cx: &'a Ctx<'e>, run: &'a Run) -> Self {
        let mut known = Vec::new();
        let mut known_big = Vec::new();
        for level in 0..cx.level() {
            if !is_equation(cx, level) {
                continue;
            }
            if let Ok(Value::Eq(_, l, _)) = force(&cx.g(), cx.types[level].clone()) {
                match read_back(&cx.g(), cx.level(), &l) {
                    Ok(Some(t)) => known.push(t),
                    Ok(None) => known_big.push((*l).clone()),
                    Err(_) => {}
                }
            }
        }
        Finder {
            cx,
            run,
            single: None,
            last_resort: None,
            stuck: None,
            known,
            known_big,
            visits: 0,
            in_goal: false,
            under_stuck: 0,
            mentioned: Vec::new(),
            survey: None,
            resort_only: false,
        }
    }

    /// The atom to split on in this case, if any (§5.2, §5.3).
    fn find(&mut self, goal: &Value) -> Result<Option<Atom>> {
        let cx = self.cx;
        if let Some(atom) = self.shared(goal)? {
            return Ok(Some(atom));
        }
        // The second try splits the hypotheses first: most of their cases
        // contradict them at once, and the goal's splits are then made only
        // in the cases left, not again under each of their own. What a
        // hypothesis waits for is split whatever it is, a record or what
        // only the last resort splits otherwise: its cases are the ones
        // that refute it. Then what the goal's structure waits for, before
        // its tests: a `match group, rest` whose other arms compute once
        // `rest` is taken apart needs none of the tests on `group`'s parts
        // that both sides make alike.
        if self.run.thrifty {
            for (_, stuck_side) in stuck_sides(cx, self.run.thrifty)? {
                let found = self.walk(&stuck_side)?;
                if let Some(atom) = found.or_else(|| self.single.take()) {
                    return Ok(Some(atom));
                }
                if let Some(atom) = self.last_resort.take() {
                    return Ok(Some(atom));
                }
            }
            let mut structure = Finder::new(cx, self.run);
            structure.resort_only = true;
            structure.in_goal = true;
            structure.walk(goal)?;
            if let Some(atom) = structure.last_resort.take() {
                return Ok(Some(atom));
            }
        }
        self.in_goal = true;
        // The goal's whole side (`Nat.leq n 2 = True` on `Nat.leq n 2`) waits
        // for the hypotheses: what they are stuck on says more.
        let mut side = None;
        match self.walk(goal)? {
            Some(atom) if atom.side => side = Some(atom),
            Some(atom) => return Ok(Some(atom)),
            None => {}
        }
        self.in_goal = false;
        for (_, stuck_side) in stuck_sides(cx, self.run.thrifty)? {
            if let Some(atom) = self.walk(&stuck_side)? {
                return Ok(Some(atom));
            }
        }
        Ok(side.or_else(|| self.single.take()))
    }

    /// A value of a recursive type that two or more chains of stuck calls
    /// end at, each with an atom outside it (SW-939): `List.get t 0 =
    /// List.head t` splits `t`, not `List.get t 0` and then `List.head t`,
    /// which would make cases that can't happen (one `None`, the other
    /// `Some`) and lose what ties them together. Split once: a value that
    /// is itself a field of an earlier split of its type isn't split again,
    /// so `cases` never follows a list down by itself. `Nat` is left to
    /// `arithmetic`.
    fn shared(&self, goal: &Value) -> Result<Option<Atom>> {
        let cx = self.cx;
        let mut survey = Finder::new(cx, self.run);
        survey.survey = Some(Survey::default());
        survey.in_goal = true;
        survey.walk(goal)?;
        survey.in_goal = false;
        // The whole equation, so its stuck side counts as one that would be
        // split, as the goal's sides do.
        for (equation, _) in stuck_sides(cx, self.run.thrifty)? {
            survey.walk(&equation)?;
        }
        let Survey { ends, .. } = survey.survey.take().expect("set above");
        for (term, value, d) in &ends {
            let chains = ends
                .iter()
                .filter(|(other, _, _)| crate::matching::same(other, term))
                .count();
            if chains >= 2
                && !self.is_known(value)?
                && !has_meta(cx, value)?
                && !self.split_field(term, *d)?
            {
                return Ok(Some(Atom {
                    value: value.clone(),
                    d: *d,
                    side: false,
                    numbers: None,
                }));
            }
        }
        Ok(None)
    }

    /// [`Finder::chain`] in the survey pass: follows what `stuck` waits for
    /// inwards, as `chain` does, and records where it ends.
    fn survey_chain(&mut self, stuck: &Value, first: Option<(Value, DataId)>) -> Result<()> {
        let cx = self.cx;
        let g = cx.g();
        let Some(start) = read_back(&g, cx.level(), stuck)? else {
            return Ok(());
        };
        let survey = self.survey.as_ref().expect("in the survey pass");
        if survey.seen.iter().any(|t| crate::matching::same(t, &start)) {
            return Ok(());
        }
        let mut seen = vec![start];
        let mut atom_outside = false;
        // Whether everything after the last atom is of a recursive type: a
        // chain through a number (`Nat.leq (List.count xs p) k`) isn't decided
        // by taking one element off `xs`.
        let mut direct = false;
        let mut end = None;
        let mut current = stuck.clone();
        let mut first = first;
        loop {
            if int_arithmetic(&g, &current) {
                end = None;
                break;
            }
            let (raw, d, is_first) = match first.take() {
                Some((raw, d)) => (raw, d, true),
                None => match blocker(cx, &current, self.run.thrifty)? {
                    Some((raw, d, _)) => (raw, d, false),
                    None => break,
                },
            };
            if self.ctors(d).is_some_and(|n| n >= 2)
                && !self.is_known(&raw)?
                && !has_meta(cx, &raw)?
            {
                atom_outside = true;
                direct = true;
            } else if !recursive(cx, d) {
                direct = false;
            }
            if is_first {
                continue;
            }
            let Some(term) = read_back(&g, cx.level(), &raw)? else {
                return Ok(());
            };
            seen.push(term);
            end = Some((raw.clone(), d));
            let next = force(&g, raw)?;
            current = if is_folded(&g, &next) {
                match unfold_folded(&g, &next)? {
                    Some(u) => u,
                    // A field of a stuck call (`(Bool.decEq a b).holds`)
                    // waits for what the call waits for.
                    None if matches!(&next, Value::Neutral(Head::Def(_), spine) if stitchwort_core::value::is_call_field(spine)) => {
                        next
                    }
                    None => break,
                }
            } else {
                next
            };
            if !matches!(current, Value::Neutral(Head::Def(_), _)) {
                break;
            }
        }
        let end = match end {
            Some((raw, d)) if atom_outside && direct && recursive(cx, d) => {
                read_back(&g, cx.level(), &raw)?.map(|term| (term, raw, d))
            }
            _ => None,
        };
        let survey = self.survey.as_mut().expect("in the survey pass");
        survey.seen.extend(seen);
        survey.ends.extend(end);
        Ok(())
    }

    /// Whether `term`, of type `d`, is a field of a constructor of `d` that
    /// an earlier split in this case found (`xs` after `t = Cons x xs`).
    fn split_field(&self, term: &Term, d: DataId) -> Result<bool> {
        let cx = self.cx;
        let g = cx.g();
        for level in 0..cx.level() {
            if !is_equation(cx, level) {
                continue;
            }
            let Value::Eq(_, _, r) = force(&g, cx.types[level].clone())? else {
                continue;
            };
            let Value::Ctor(of, _, fields) = force(&g, (*r).clone())? else {
                continue;
            };
            if of != d {
                continue;
            }
            for field in fields.iter() {
                let Some(read) = read_back(&g, cx.level(), field)? else {
                    continue;
                };
                if crate::matching::same(&read, term) {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    fn walk(&mut self, value: &Value) -> Result<Option<Atom>> {
        let g = self.cx.g();
        self.visits += 1;
        if self.visits > VISITS {
            return Ok(None);
        }
        g.machine.budget.step()?;
        let forced = force(&g, value.clone())?;
        match &forced {
            Value::Neutral(Head::Def(_), spine) => {
                if is_folded(&g, &forced) {
                    match unfold_folded(&g, &forced)? {
                        Some(unfolded) => return self.walk(&unfolded),
                        // A field of a stuck call (`(f x).i`) is stuck where
                        // the call is.
                        None if stitchwort_core::value::is_call_field(spine) => {}
                        None => return Ok(None),
                    }
                }
                if let Some(atom) = self.chain(&forced, None)? {
                    return Ok(Some(atom));
                }
                self.walk_stuck_spine(spine)
            }
            Value::Neutral(Head::Var(level, _, _), spine) => {
                if self.in_goal && spine.is_empty() && !self.mentioned.contains(level) {
                    self.mentioned.push(*level);
                }
                self.walk_spine(spine)
            }
            Value::Ctor(_, _, fields) => {
                for f in fields.iter() {
                    if let Some(atom) = self.walk(f)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::Data(_, args) => {
                for a in args {
                    if let Some(atom) = self.walk(a)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::Eq(ty, l, r) => {
                // A side that is itself stuck, of a splittable type, is the
                // outermost candidate: `f x = True` splits on `f x` if
                // nothing inside it is splittable.
                let d = match force(&g, (**ty).clone())? {
                    Value::Data(d, _) => Some(d),
                    _ => None,
                };
                for side in [l, r] {
                    let forced = force(&g, (**side).clone())?;
                    if let (Some(d), Value::Neutral(Head::Def(_), spine)) = (d, &forced)
                        && !is_folded(&g, &forced)
                    {
                        if let Some(atom) = self.chain(&forced, Some(((**side).clone(), d)))? {
                            return Ok(Some(atom));
                        }
                        if let Some(atom) = self.walk_stuck_spine(spine)? {
                            return Ok(Some(atom));
                        }
                        continue;
                    }
                    if let Some(atom) = self.walk(side)? {
                        return Ok(Some(atom));
                    }
                }
                Ok(None)
            }
            Value::NatAdd(_, x) => self.walk(x),
            _ => Ok(None),
        }
    }

    fn walk_stuck_spine(&mut self, spine: &stitchwort_core::value::Spine) -> Result<Option<Atom>> {
        self.under_stuck += 1;
        let found = self.walk_spine(spine);
        self.under_stuck -= 1;
        found
    }

    fn walk_spine(&mut self, spine: &stitchwort_core::value::Spine) -> Result<Option<Atom>> {
        for elim in spine.iter() {
            if let Elim::App(a, _) = elim
                && let Some(atom) = self.walk(a)?
            {
                return Ok(Some(atom));
            }
        }
        Ok(None)
    }

    /// The innermost splittable value on the chain of what the stuck call
    /// `stuck` waits for.
    fn chain(&mut self, stuck: &Value, first: Option<(Value, DataId)>) -> Result<Option<Atom>> {
        if self.survey.is_some() {
            self.survey_chain(stuck, first)?;
            return Ok(None);
        }
        let g = self.cx.g();
        let mut best: Option<Atom> = None;
        // The innermost value on this chain that only the last resort
        // splits.
        let mut resort: Option<Atom> = None;
        let mut resplit: Option<Atom> = None;
        let mut current = stuck.clone();
        let mut last_unsplittable = None;
        let mut first = first;
        loop {
            // A call of `Int`'s own arithmetic is as far in as the chain
            // goes (SW-937): it is neither an atom itself, unless a
            // definition outside that arithmetic tests it (the previous
            // step, already taken), nor is what it waits for, which would
            // be `Int`'s internals (`Int.subNatNatFrom n (Succ m) …`).
            // `arithmetic` and `algebra` take the arithmetic as it is.
            if int_arithmetic(&g, &current) {
                if last_unsplittable.is_none()
                    && let Some(int) = g.env.registry().loaded_data(Builtin::Int)
                {
                    last_unsplittable = Some((current.clone(), int));
                }
                break;
            }
            // `stuck` itself first, if it's a candidate; then what it waits
            // for, and so on inwards.
            let (raw, d, numbers, is_first) = match first.take() {
                Some((raw, d)) => (raw, d, None, true),
                None => match blocker(self.cx, &current, self.run.thrifty)? {
                    Some((raw, d, numbers)) => (raw, d, numbers, false),
                    None => break,
                },
            };
            // A comparison of numbers that something outside tests (`if
            // x + 1 == y then …`) is one atom, true or false, which `omega`
            // reads in each case; what its decision waits for, the operands,
            // is `Int`'s insides.
            if best.is_some() && number_equality(&g, &current) {
                break;
            }
            match self.ctors(d) {
                Some(n) if !self.is_known(&raw)? && !has_meta(self.cx, &raw)? => {
                    let atom = Atom {
                        value: raw.clone(),
                        d,
                        side: is_first,
                        numbers: None,
                    };
                    if n >= 2 {
                        best = Some(atom);
                    } else if best.as_ref().is_some_and(|b| b.side)
                        && last_unsplittable.is_none()
                        && self.under_stuck == 0
                    {
                        // The call's own result (`eqbId x x = True` on
                        // `eqbId x x`) waits on a record (`x`): taking the
                        // record apart first is one case, and reaches the
                        // real obstacle, where splitting the result would
                        // report a case (`eqbId x x = False`) that reads as
                        // if the statement were false.
                        best = Some(Atom {
                            side: false,
                            ..atom
                        });
                    } else if self.single.is_none()
                        && last_unsplittable.is_none()
                        && self.under_stuck == 0
                    {
                        // A record is split only for what waits on it
                        // directly (`p.row`), never under a number
                        // (`Nat.leq x.bits y.bits` waits on `x.bits`): taking
                        // `x` apart doesn't decide that.
                        self.single = Some(atom);
                    }
                }
                Some(n) => {
                    // Split already in this case, yet still stuck here: an
                    // occurrence the split's generalisation couldn't see,
                    // because it only appeared once a later split computed
                    // (`if f x then …` out of a call stuck on a number).
                    // Splitting it again puts the constructor there; the
                    // other cases contradict the first split's equation.
                    // Once: a value split twice is left, so a generalisation
                    // that can't see it never loops.
                    if n >= 2 && !is_first && resplit.is_none() && self.known_times(&raw)? == 1 {
                        resplit = Some(Atom {
                            value: raw.clone(),
                            d,
                            side: false,
                            numbers: None,
                        });
                    }
                }
                None => {
                    // The innermost candidate decides: one inside that
                    // can't be split (a part of an earlier split) leaves
                    // nothing, not the stuck call around it, whose split
                    // would forget what it is (`tail ++ []`).
                    if !is_first && (numbers.is_some() || recursive(self.cx, d)) {
                        resort = self.last_resort_atom(&raw, d, numbers)?;
                    }
                    last_unsplittable = Some((raw.clone(), d));
                }
            }
            if is_first {
                continue;
            }
            let next = force(&g, raw)?;
            current = if is_folded(&g, &next) {
                match unfold_folded(&g, &next)? {
                    Some(u) => u,
                    // A field of a stuck call (`(Bool.decEq a b).holds`)
                    // waits for what the call waits for.
                    None if matches!(&next, Value::Neutral(Head::Def(_), spine) if stitchwort_core::value::is_call_field(spine)) => {
                        next
                    }
                    None => break,
                }
            } else {
                next
            };
            if !matches!(current, Value::Neutral(Head::Def(_), _)) {
                break;
            }
        }
        if best.is_none()
            && self.in_goal
            && self.stuck.is_none()
            && let Some((raw, d)) = last_unsplittable
        {
            self.stuck = Some(Stuck {
                what: self.cx.show(&raw),
                ty: g.data(d).name().to_string(),
                again: recursive(self.cx, d),
            });
        }
        if self.resort_only {
            if self.last_resort.is_none() {
                self.last_resort = resort;
            }
            return Ok(None);
        }
        if best.is_none() && self.last_resort.is_none() {
            self.last_resort = resplit.or(resort);
        }
        Ok(best)
    }

    /// `raw`, of type `d`, as the last resort's split (SW-3752), if it is
    /// one: a number that a definition compares with `numbers`, split into
    /// each of them and the rest; or a value of a recursive type other than
    /// `Nat`, split into its constructors, once (not a field of an earlier
    /// split of its type, so never induction).
    fn last_resort_atom(
        &self,
        raw: &Value,
        d: DataId,
        numbers: Option<Vec<BigUint>>,
    ) -> Result<Option<Atom>> {
        let cx = self.cx;
        let g = cx.g();
        if has_meta(cx, raw)? {
            return Ok(None);
        }
        if let Some(numbers) = numbers {
            // `k + x` isn't split: what it is apart from says nothing of
            // `x` here.
            if !matches!(force(&g, raw.clone())?, Value::Neutral(..)) {
                return Ok(None);
            }
            return Ok(Some(Atom {
                value: raw.clone(),
                d,
                side: false,
                numbers: Some(numbers),
            }));
        }
        if !recursive(cx, d) || self.is_known(raw)? {
            return Ok(None);
        }
        let Some(term) = read_back(&g, cx.level(), raw)? else {
            return Ok(None);
        };
        if self.split_field(&term, d)? {
            return Ok(None);
        }
        Ok(Some(Atom {
            value: raw.clone(),
            d,
            side: false,
            numbers: None,
        }))
    }

    /// The fallback's split, after [`Finder::find`] found nothing
    /// (docs/proposals/decide.md §6.1.3): of the variables the goal
    /// mentions, as computed, whose type is splittable and that aren't
    /// known in this case, the one whose split makes the fewest cases (its
    /// constructor count: a record's 1, `Bool`'s 2), ties to the latest
    /// bound.
    fn fallback(&self) -> Result<Option<Atom>> {
        let cx = self.cx;
        let mut best: Option<(usize, usize, DataId)> = None;
        for &level in &self.mentioned {
            if is_equation(cx, level) {
                continue;
            }
            let Value::Data(d, _) = force(&cx.g(), cx.types[level].clone())? else {
                continue;
            };
            let Some(count) = self.ctors(d) else {
                continue;
            };
            let value = Value::var(level);
            if self.is_known(&value)? {
                continue;
            }
            let better = match best {
                None => true,
                Some((c, l, _)) => count < c || (count == c && level > l),
            };
            if better {
                best = Some((count, level, d));
            }
        }
        Ok(best.map(|(_, level, d)| Atom {
            value: Value::var(level),
            d,
            side: false,
            numbers: None,
        }))
    }

    /// An atom inside what an earlier split's equation is stuck on, latest
    /// split first: the search takes a call it can't see into (a native
    /// comparison of numbers, `Nat.leq 5 (level tok)`) as a whole, so once
    /// that call is split its arguments may still wait for a value
    /// (`level tok` for `tok`). The equations are left out of every other
    /// search, as what they equate is known in the case.
    fn under_split(&mut self) -> Result<Option<Atom>> {
        let cx = self.cx;
        let g = cx.g();
        for level in (0..cx.level()).rev() {
            if !is_equation(cx, level) || stale(cx, level) {
                continue;
            }
            let Value::Eq(_, l, r) = force(&g, cx.types[level].clone())? else {
                continue;
            };
            for side in [l, r] {
                let side = force(&g, (*side).clone())?;
                if is_stuck(&side)
                    && let Some(atom) = self.walk(&side)?
                {
                    return Ok(Some(atom));
                }
            }
        }
        Ok(None)
    }

    /// How many splits in this case split `value`, as far as can be read
    /// back.
    fn known_times(&self, value: &Value) -> Result<usize> {
        let g = self.cx.g();
        Ok(match read_back(&g, self.cx.level(), value)? {
            Some(t) => self
                .known
                .iter()
                .filter(|k| crate::matching::same(k, &t))
                .count(),
            None => 0,
        })
    }

    fn is_known(&self, value: &Value) -> Result<bool> {
        if self.known.is_empty() && self.known_big.is_empty() {
            return Ok(false);
        }
        let g = self.cx.g();
        match read_back(&g, self.cx.level(), value)? {
            Some(t) => Ok(self.known.iter().any(|k| crate::matching::same(k, &t))),
            None => {
                for k in &self.known_big {
                    if conv(&g, self.cx.level(), k, value)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    /// The number of constructors of `d` if it's splittable.
    fn ctors(&self, d: DataId) -> Option<usize> {
        if let Some(known) = self.run.splittable.borrow().get(&d) {
            return *known;
        }
        let answer = splittable(self.cx, d);
        self.run.splittable.borrow_mut().insert(d, answer);
        answer
    }
}

fn has_meta(cx: &Ctx, value: &Value) -> Result<bool> {
    // Too large to read back: not split, as if it had one.
    let Some(t) = read_back(&cx.g(), cx.level(), value)? else {
        return Ok(true);
    };
    Ok(t.subterms().any(|(t, _)| matches!(t, Term::Meta(_))))
}

fn is_ctor_form(value: &Value) -> bool {
    matches!(value, Value::Ctor(..) | Value::Nat(_))
}

fn is_stuck(value: &Value) -> bool {
    matches!(value, Value::Neutral(..) | Value::NatAdd(..))
}

/// Whether `value` (forced) is a call of `Int`'s own arithmetic: the
/// definitions `arithmetic` reads (`-`, `+`, `-` between two, `*`, `/`, `%`,
/// `<=`, `<`, and the subtraction of naturals they compute through). Their
/// case trees test `OfNat`/`NegSucc`, which `cases` doesn't split for them
/// (SW-937), as it doesn't split `Float`'s bits for `Float.isNaN`.
fn int_arithmetic(g: &Ev, value: &Value) -> bool {
    let Value::Neutral(Head::Def(id), _) = value else {
        return false;
    };
    const ARITHMETIC: [Builtin; 8] = [
        Builtin::IntNeg,
        Builtin::IntAdd,
        Builtin::IntSub,
        Builtin::IntMul,
        Builtin::IntDiv,
        Builtin::IntMod,
        Builtin::IntLeq,
        Builtin::IntLess,
    ];
    ARITHMETIC
        .iter()
        .any(|b| g.env.registry().loaded_def(*b) == Some(*id))
        || matches!(
            &**g.def(*id).path(),
            "Std.Int.subNatNat" | "Std.Int.subNatNatFrom"
        )
}

/// The most nodes of a value's normal form that the search for an atom
/// reads back to compare. A scrutinee can unfold to a term that doubles with
/// every split, because the value shares its parts and a read-back copies
/// them: a mutated proof of `operatorStepComplete` reached 3.9 million nodes
/// in 15 cases, read back several times per case, and held 7 GB (SW-2576).
/// Folding the calls doesn't help; the term is large either way.
const READ_BACK_NODES: u64 = 100_000;

/// `value` as a term for comparing with others, or `None` if its normal
/// form has more than [`READ_BACK_NODES`] nodes.
fn read_back(g: &Ev, level: usize, value: &Value) -> Result<Option<Term>> {
    Ok(quote_at_most(g, level, value, READ_BACK_NODES)?)
}

/// Whether `value` (forced) is the test of a call of `Int.decEq`
/// (`(Int.decEq x y).holds`): what an `Int` `==` is.
fn number_equality(g: &Ev, value: &Value) -> bool {
    let Value::Neutral(Head::Def(id), _) = value else {
        return false;
    };
    g.env.registry().loaded_def(Builtin::DecEqInt) == Some(*id)
}

/// The hypotheses that `cases` follows (D1318), latest first: each equation
/// between a constructor and a stuck term, with the stuck term. With
/// `parts`, for the second try, those that are a part of a hypothesis too
/// (a side of a conjunction, what a test fact reads as:
/// `auto::hypothesis_parts`), after them.
fn stuck_sides(cx: &Ctx, parts: bool) -> Result<Vec<(Value, Value)>> {
    let g = cx.g();
    let mut sides = Vec::new();
    let levels: Vec<usize> = visible(cx)
        .into_iter()
        .filter(|&level| !is_equation(cx, level))
        .collect();
    let mut types: Vec<Value> = levels.iter().map(|&l| cx.types[l].clone()).collect();
    if parts {
        types.extend(
            crate::auto::hypothesis_parts(cx, &levels)?
                .into_iter()
                .map(|(_, ty)| ty),
        );
    }
    for ty in types {
        let equation = force(&g, ty)?;
        let Value::Eq(_, l, r) = &equation else {
            continue;
        };
        let (l, r) = (force(&g, (**l).clone())?, force(&g, (**r).clone())?);
        if is_ctor_form(&r) && is_stuck(&l) {
            sides.push((equation, l));
        } else if is_ctor_form(&l) && is_stuck(&r) {
            sides.push((equation, r));
        }
    }
    Ok(sides)
}

/// The constructor count of `d` if a value of it can be split: data that
/// isn't a proposition, an indexed family or recursive.
fn splittable(cx: &Ctx, d: DataId) -> Option<usize> {
    let data = cx.g().data(d);
    if data.sort() == Sort::Prop || !data.indices().is_empty() || data.ctors().is_empty() {
        return None;
    }
    (!is_recursive(data)).then_some(data.ctors().len())
}

/// Whether `d` is splittable but for being recursive, and isn't `Nat`
/// (which `arithmetic` reasons about instead): what [`Finder::shared`] may split
/// once, where several stuck calls wait for the same value of it.
fn recursive(cx: &Ctx, d: DataId) -> bool {
    let g = cx.g();
    let data = g.data(d);
    data.sort() != Sort::Prop
        && data.indices().is_empty()
        && data.ctors().len() >= 2
        && g.env.builtins().nat != Some(d)
        && is_recursive(data)
}

/// What a case with nothing to split was stuck on, as shown.
struct Stuck {
    what: String,
    ty: String,
    /// Its type is recursive, so it is a part of an earlier split of its
    /// type: the last resort splits such a value only once.
    again: bool,
}

/// What a stuck call waits for ([`blocker`]): the value, its type, and the
/// numbers a `NumCase` compares it with.
type Blocker = (Value, DataId, Option<Vec<BigUint>>);

fn is_recursive(data: &stitchwort_core::globals::Data) -> bool {
    data.ctors().iter().any(|c| {
        c.fields.iter().any(|(_, ty)| {
            ty.subterms()
                .any(|(t, _)| matches!(t, Term::Data(x, _) if data.group().contains(x)))
        })
    })
}

/// What the stuck call `value` (forced) waits for: the value its case tree
/// tests where it can't take a step, as the call's arguments hold it (a
/// folded call is kept as the call, for display), with its type, and for a
/// number compared with numbers (a `NumCase`), those numbers. With
/// `numbers_known`, for the second try, a `NumCase` on a known number goes
/// on into its arm; the first try stops there, as it always has, so its
/// proofs keep their terms.
fn blocker(cx: &Ctx, value: &Value, numbers_known: bool) -> Result<Option<Blocker>> {
    let g = cx.g();
    let Value::Neutral(Head::Def(id), spine) = value else {
        return Ok(None);
    };
    let def = g.def(*id);
    let Some(body) = body_seen(&g, *id) else {
        return Ok(None);
    };
    if def.arity() == 0 || spine.len() < def.arity() {
        return Ok(None);
    }
    let mut env = Vec::with_capacity(def.arity());
    for elim in spine.iter().take(def.arity()) {
        match elim {
            Elim::App(v, _) => env.push(v.clone()),
            Elim::J { .. } | Elim::Proj(..) => return Ok(None),
        }
    }
    let mut tree = Term::peel_lams_rc(body, def.arity());
    loop {
        g.machine.budget.step()?;
        let node = Term::strip_loc_rc(&tree);
        match &*node {
            Term::Case(ix, d, branches) => {
                let raw = env[env.len() - 1 - ix].clone();
                let mut scrutinee = force(&g, raw.clone())?;
                if is_folded(&g, &scrutinee)
                    && let Some(u) = unfold_folded(&g, &scrutinee)?
                {
                    scrutinee = u;
                }
                match scrutinee {
                    Value::Ctor(_, c, fields) => {
                        let Some(next) = branches[c].body.clone() else {
                            return Ok(None);
                        };
                        env.extend(fields.iter().cloned());
                        tree = next;
                    }
                    Value::Neutral(..) => return Ok(Some((raw, *d, None))),
                    _ => return Ok(None),
                }
            }
            Term::NumCase(ix, arms, default) => {
                let raw = env[env.len() - 1 - ix].clone();
                let nat = g.env.builtins().nat;
                match (force(&g, raw.clone())?, nat) {
                    // A known number takes its arm, or the default, as
                    // running would (`['-', ..tail]` goes on to `tail`).
                    (Value::Nat(k), _) if numbers_known => {
                        tree = match arms.iter().find(|arm| *arm.value == *k) {
                            Some(arm) => arm.body.clone(),
                            None => default.clone(),
                        };
                    }
                    (Value::Neutral(..), Some(nat)) => {
                        let numbers = arms.iter().map(|arm| (*arm.value).clone()).collect();
                        return Ok(Some((raw, nat, Some(numbers))));
                    }
                    _ => return Ok(None),
                }
            }
            _ => return Ok(None),
        }
    }
}

/// For `cases then t`, the condition of the first `if` the goal shows (read
/// back folded, calls as calls, in pre-order), when it is stuck and not
/// known in this case (SW-3530, D2542). `t` is written against the goal
/// as it is shown, so the split it is given is the one it can see: on
/// `(if fits then wide else narrow).words = …` that is `fits`, and each
/// case's goal keeps the branch's calls (`wide.words`), which `t` can
/// rewrite. What [`Finder::find`] would split instead is what the
/// condition's call is stuck on inside its definition, innermost first,
/// and each of those cases' goals is computed past the calls `t` names.
/// Only an `if` outside every binder of the goal is taken.
fn visible_condition(cx: &Ctx, run: &Run, goal: &Value) -> Result<Option<Atom>> {
    let ite = builtin_def(cx, Builtin::IfThenElse)?;
    let bool_data = builtin_data(cx, Builtin::Bool)?;
    // A goal too large to read back has no condition to show: the usual
    // search goes on, and the budget check before a split reports it.
    let written = match cx.quote_folded(goal) {
        Ok(written) => written,
        Err(e) if crate::undo::recoverable(cx, &e) => {
            crate::undo::recovered(cx);
            return Ok(None);
        }
        Err(e) => return Err(e),
    };
    let finder = Finder::new(cx, run);
    for (term, under) in written.subterms() {
        if under > 0 {
            continue;
        }
        let (head, args) = term.spine();
        if !matches!(head, Term::Def(id) if *id == ite) || args.len() != 4 {
            continue;
        }
        let condition = cx.eval(args[1])?;
        if !matches!(force(&cx.g(), condition.clone())?, Value::Neutral(..))
            || finder.is_known(&condition)?
            || has_meta(cx, &condition)?
        {
            continue;
        }
        return Ok(Some(Atom {
            value: condition,
            d: bool_data,
            side: false,
            numbers: None,
        }));
    }
    Ok(None)
}

/// Splits the case on `atom`: the generated `match` with one alternative
/// per constructor, each going on with this `cases`. `fallback`: the goal
/// isn't stuck on it (§6.1.3), which the diagnostics say.
fn split_on(cx: &mut Ctx, run: &Rc<Run>, atom: Atom, goal: &Value, fallback: bool) -> Result<Term> {
    let g = cx.g();
    let data = g.data(atom.d);
    let shown = cx.show(&atom.value);
    let first = !run.atoms.borrow().iter().any(|(a, _)| *a == shown);
    if first {
        run.atoms.borrow_mut().push((shown.clone(), fallback));
        let ty = match &atom.value {
            Value::Neutral(Head::Var(..), spine) if spine.is_empty() => {
                Some(atom_type(cx, &cx.quote_folded(&atom.value)?, atom.d)?)
            }
            _ => None,
        };
        run.atom_types.borrow_mut().push(ty);
        if g.env.registry().loaded_data(Builtin::Int) == Some(atom.d) {
            run.split_int.set(true);
        }
    }
    let count = match &atom.numbers {
        Some(numbers) => numbers.len() + 1,
        None => data.ctors().len(),
    };
    run.cases.set(run.cases.get() + count - 1);
    let too_many = run.cases.get() > run.limit();
    if too_many || too_large_to_split(cx, goal)? {
        run.over.set(true);
        run.over_size.set(!too_many);
        if too_many {
            *run.over_finite.borrow_mut() = finite_atoms(cx, run)?;
        }
        if fallback && too_many {
            let ty = atom_type(cx, &cx.quote_folded(&atom.value)?, atom.d)?;
            *run.over_fallback.borrow_mut() = Some(format!("{shown} : {}", cx.show(&ty)));
        }
        let path = path(cx);
        *run.open_at.borrow_mut() = Some(if path.is_empty() {
            "the first, before any split".to_string()
        } else {
            path.join(", ")
        });
        return Err(Diagnostic::error("E-CASES-BUDGET", "over budget"));
    }
    // A decision's test, `d.holds`, is split as what it computes to: that
    // is what an `if` on `d`, unfolded, is stuck on.
    let term = cx.quote_folded(&atom.value)?;
    let holds = g.env.registry().def(Builtin::Holds);
    let term = match term.spine().0 {
        Term::Def(id) if Some(*id) == holds => cx.quote_unfolded(&atom.value)?,
        Term::Proj(d, 0, _) if g.env.registry().data(Builtin::Decidable) == Some(*d) => {
            cx.quote_unfolded(&atom.value)?
        }
        _ => term,
    };
    let ty = atom_type(cx, &term, atom.d)?;
    let depth = (0..cx.level()).filter(|&l| is_equation(cx, l)).count();
    let name = ast::Name {
        text: if fallback {
            format!("{EQUATION}{}{FALLBACK}", depth + 1)
        } else {
            format!("{EQUATION}{}", depth + 1)
        },
        span: run.span,
    };
    let alt = |pattern: Pattern| Alt {
        guard: None,
        patterns: vec![pattern],
        body: Some(Expr::Cases {
            targets: run.targets.clone(),
            body: run.body.clone(),
            span: run.span,
        }),
        span: run.span,
    };
    let alts: Vec<Alt> = match &atom.numbers {
        // Each number, and then the rest, which the `match` knows to be none
        // of them, so the comparison takes its default there.
        Some(numbers) => numbers
            .iter()
            .map(|k| alt(Pattern::Num(k.clone(), run.span)))
            .chain([alt(Pattern::Wildcard(run.span))])
            .collect(),
        None => data
            .ctors()
            .iter()
            .enumerate()
            .map(|(c, ctor)| {
                let explicit = (0..ctor.fields.len())
                    .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                    .count();
                let fields = (0..explicit).map(|_| Pattern::Wildcard(run.span)).collect();
                alt(crate::internal_ctor_pattern(atom.d, c, fields, run.span))
            })
            .collect(),
    };
    crate::matching::generalised_named(
        cx,
        term,
        ty,
        run.span,
        Some(name),
        Some(stale),
        &alts,
        &[],
        run.span,
        goal,
    )
}

/// The latest hypothesis `A ∨ B` worth splitting in this case, for the first
/// try ([`Run::or_first`]): one not split on the way here, neither of whose
/// sides is already known (an equation whose sides compute to the same
/// thing, or a hypothesis), under a goal that is a proposition, which is
/// what a proof of `∨` may be taken apart into.
fn or_hypothesis(cx: &Ctx, run: &Run, goal: &Value) -> Result<Option<usize>> {
    let g = cx.g();
    let levels = visible(cx);
    let mut found = None;
    for &level in &levels {
        let Value::Data(d, args) = force(&g, cx.types[level].clone())? else {
            continue;
        };
        if !g.env.registry().is_data(Builtin::Or, d) || args.len() != 2 {
            continue;
        }
        if run.split_ors.borrow().contains(&cx.names[level]) {
            continue;
        }
        let mut known = false;
        for side in args.iter() {
            known = known
                || trivial(cx, side)
                || levels
                    .iter()
                    .any(|&k| conv(&g, cx.level(), &cx.types[k], side).unwrap_or(false));
        }
        if !known {
            found = Some(level);
            break;
        }
    }
    match found {
        Some(level) if is_proposition(cx, goal)? => Ok(Some(level)),
        _ => Ok(None),
    }
}

/// Splits the hypothesis at `level`, `A ∨ B`, into a case with `A` and one
/// with `B`, each a fact named as [`take_apart`]'s are (so [`substitute`]
/// may use an equation `x = t` among them), and each case is this `cases`
/// again. The split is the `match h with | Inl a | Inr b` a proof writes.
fn split_disjunction(
    cx: &mut Ctx,
    run: &Rc<Run>,
    level: usize,
    goal: &Value,
    root: Option<usize>,
) -> Result<Term> {
    let g = cx.g();
    let hypothesis = cx.names[level].clone();
    let shown = hypothesis_name(cx, level, &hypothesis);
    if !run.atoms.borrow().iter().any(|(a, _)| *a == shown) {
        run.atoms.borrow_mut().push((shown, false));
        run.atom_types.borrow_mut().push(None);
    }
    run.split_or.set(true);
    run.cases.set(run.cases.get() + 1);
    if run.cases.get() > run.limit() {
        run.over.set(true);
        let path = path(cx);
        *run.open_at.borrow_mut() = Some(if path.is_empty() {
            "the first, before any split".to_string()
        } else {
            path.join(", ")
        });
        return Err(Diagnostic::error("E-CASES-BUDGET", "over budget"));
    }
    let ty = cx.types[level].clone();
    let Value::Data(or, _) = force(&g, ty.clone())? else {
        unreachable!("an `∨`")
    };
    run.facts.set(run.facts.get() + 1);
    let name = Name::from(format!("{FACT}{}", run.facts.get()).as_str());
    run.injected.borrow_mut().push(name.clone());
    if let Some(root) = root {
        run.named_facts.borrow_mut().push((name.clone(), root));
    }
    let alts: Vec<Alt> = (0..2)
        .map(|c| Alt {
            guard: None,
            patterns: vec![crate::internal_ctor_pattern(
                or,
                c,
                vec![Pattern::Var(ast::Name {
                    text: name.to_string(),
                    span: run.span,
                })],
                run.span,
            )],
            body: Some(Expr::Cases {
                targets: run.targets.clone(),
                body: run.body.clone(),
                span: run.span,
            }),
            span: run.span,
        })
        .collect();
    run.split_ors.borrow_mut().push(hypothesis);
    let term = Term::Var(cx.level() - 1 - level);
    let result = crate::matching::generalised_named(
        cx,
        term,
        ty,
        run.span,
        None,
        Some(stale),
        &alts,
        &[],
        run.span,
        goal,
    );
    run.split_ors.borrow_mut().pop();
    result
}

/// The most nodes of a case's goal and hypotheses, read back unfolded, that
/// a split generalises. The generalisation (`matching::generalised_now`)
/// reads all of them back in full and builds its motive and the copied
/// hypotheses from them, several copies in all: a mutated proof of
/// `operatorStepComplete` reached a goal of 3.9 million nodes, and the
/// hypothesis repeating it, after 13 cases, and its split held 2 GB more
/// (SW-2606). Ordinary splits read back a few thousand. `E-CASES-BUDGET`
/// says "a million".
const SPLIT_READ_BACK_NODES: u64 = 1_000_000;

/// Whether the goal and the hypotheses a split would read back in this case
/// have more than [`SPLIT_READ_BACK_NODES`] nodes between them.
fn too_large_to_split(cx: &Ctx, goal: &Value) -> Result<bool> {
    let g = cx.g();
    let level = cx.level();
    let mut left = SPLIT_READ_BACK_NODES;
    let read = (0..level)
        .filter(|&l| !stale(cx, l))
        .map(|l| &cx.types[l])
        .chain([goal]);
    for value in read {
        let Some(term) = quote_at_most(&g, level, value, left)? else {
            return Ok(true);
        };
        left = left.saturating_sub(term.subterms().count() as u64);
    }
    Ok(false)
}

/// The variables split so far, `x : T`, if every atom split is a variable
/// whose type has a `Finite` instance: then `Finite.check` can check the
/// statement for every value of them (docs/proposals/decide.md §6.1.4).
fn finite_atoms(cx: &mut Ctx, run: &Run) -> Result<Option<Vec<String>>> {
    let Some(finite) = crate::interfaces::finite(cx.e) else {
        return Ok(None);
    };
    let atoms = run.atoms.borrow().clone();
    let types = run.atom_types.borrow().clone();
    let mut shown = Vec::new();
    for ((atom, _), ty) in atoms.iter().zip(&types) {
        let Some(ty) = ty else {
            return Ok(None);
        };
        let goal = Value::Data(finite, vec![ty.clone()].into());
        if crate::interfaces::findable(cx, &goal)?.is_some() {
            return Ok(None);
        }
        shown.push(format!("`{atom} : {}`", cx.show(ty)));
    }
    Ok(Some(shown))
}

/// The type of the atom `term`, of data `d`: `d` itself if it has no
/// parameters, and otherwise as the kernel infers it.
pub(crate) fn atom_type(cx: &Ctx, term: &Term, d: DataId) -> Result<Value> {
    let g = cx.g();
    if g.data(d).params().is_empty() {
        return Ok(Value::Data(d, Vec::new().into()));
    }
    let mut kcx = crate::rewrite::kernel_context(cx)?;
    let (_, ty) = crate::kernel::without_glue(&g, || crate::kernel::infer(&mut kcx, term))?;
    Ok(ty)
}
