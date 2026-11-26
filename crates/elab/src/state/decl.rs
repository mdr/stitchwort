//! [`Decl`]: the scratch state of the declaration (or group, or expression
//! typed in) being elaborated. It starts empty and is emptied again when
//! the declaration is done (`Elaborator::glued`), by `Decl::default()`, so
//! nothing is listed by hand and nothing one declaration leaves reaches the
//! next. It is empty at every rewind mark (but for the `failed_mentioned` and `stuck_on_goal` flags), and a rewind empties it.
//!
//! Unlike [`super::Attempt`], none of it is taken back when an attempt is
//! undone: what's here is either set and put back around one call (a
//! guard), or kept across the attempts at one declaration on purpose.
//! Some fields are emptied by hand inside a declaration too, between its
//! parts or its attempts (`local_helpers`, `preadmitted`, `owner`): those
//! clears are part of how the declaration is checked, not cleanup after it.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::{DefId, Term, Value};
use stitchwort_syntax::Span;
use stitchwort_syntax::ast;

use crate::{SidesCapture, decreasing, effects, equations, families, lift};

/// When `check::holes_by_arguments` elaborates a failed application again
/// ([`Decl::holes_retry`]).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum HolesRetry {
    /// As soon as it fails.
    #[default]
    Now,
    /// Not yet: inside an argument checked in place that is checked again
    /// if it fails.
    Deferred,
    /// As soon as it fails, also in the arguments checked in place inside:
    /// while an argument whose retries were put off is checked again
    /// because it won't be checked later.
    Always,
}

/// A lifted `match` whose scrutinee isn't a plain variable, recorded for a
/// termination error inside it to explain: what its patterns bind isn't seen
/// as a part of the variables the scrutinee was built from. `tuple` says the
/// scrutinee was a tuple of variables, which gets wording of its own.
pub(crate) struct ComputedMatch {
    pub(crate) span: Span,
    pub(crate) shown: String,
    pub(crate) names: Vec<String>,
    pub(crate) tuple: bool,
}

#[derive(Default)]
pub(crate) struct Decl {
    /// Whether an error message has shown a term that uses a failed
    /// definition since the component's check began: its errors are then
    /// fallout of that failure, not its own (`blame_failed_dependency`). The
    /// printer sets it through the elaborator's `Shown`. Unlike the
    /// rest, it outlives the `glued` call it is set in: the component's
    /// blame is decided after it. So [`Decl::reset`] keeps it, the
    /// component's start clears it, and a rewind empties it.
    pub(crate) failed_mentioned: Cell<bool>,
    /// The open goals' assumptions an error message has shown a term stuck
    /// on, once computed, since the component's check began (the first such
    /// message's): its errors then can't be decided until the goals are
    /// filled
    /// (`blame_failed_dependency`). Kept, cleared and emptied as
    /// [`Self::failed_mentioned`] is.
    pub(crate) stuck_on_goal: RefCell<Vec<stitchwort_core::DefId>>,
    /// While a test is checked: the comparisons in it whose sides are
    /// shown when it fails (`probe.rs`).
    pub(crate) sides_capture: RefCell<SidesCapture>,
    /// Arms of the definition being checked that a case on an indexed family
    /// dropped because their constructor can't be there, with a reason, and
    /// the arms that were reached: those dropped and never reached are
    /// `W-UNREACHABLE` (`families.rs`).
    pub(crate) arm_reach: RefCell<families::ArmReach>,
    /// Above zero while an application is elaborated again the old way
    /// after its expected result type was used first and failed: no
    /// application inside uses its expected type first
    /// (docs/proposals/syntax-conveniences.md §7.4).
    pub(crate) no_propagation: Cell<usize>,
    /// Above zero while an application whose result type depends on
    /// arguments written `_` is elaborated again after comparing that type
    /// with its expected type first failed: no application inside is
    /// compared that way (`check::propagate`, D2342).
    pub(crate) no_hole_propagation: Cell<usize>,
    /// Above zero while an application is elaborated again after its
    /// result type, compared with its expected type by the arguments of the
    /// two calls (the plain comparison having failed), was used first and
    /// the application then failed: no application inside is compared by
    /// arguments that way, so a failing chain of lemmas isn't tried twice at
    /// every level (`check::propagate`, SW-3281).
    pub(crate) no_argument_propagation: Cell<usize>,
    /// Above zero while an application whose lambdas were held for its
    /// expected type (`check::fallback_holding_lambdas`) is elaborated
    /// again the ordinary way after that failed: no application inside
    /// holds its lambdas, so a failing chain isn't tried both ways at
    /// every level.
    pub(crate) no_holding: Cell<usize>,
    /// While an application with an argument written `_` and an explicit
    /// argument after it is elaborated again, after it failed against its
    /// expected type (`check::holes_by_arguments`): the address of its last
    /// written argument, or 0. That application's later arguments then
    /// solve the `_`s their types mention from what they are as written.
    pub(crate) holes_by_arguments: Cell<usize>,
    /// The arguments written `_` of the applications `check::fallback_named`
    /// is elaborating, which `check::holes_by_arguments` would elaborate
    /// again after a failure: each one's address, and whether a later
    /// argument as written has a parameter type that mentions it (found
    /// when the `_` is reached). The retry can only change what such an
    /// argument makes of a `_`.
    pub(crate) holes_watched: RefCell<Vec<(usize, bool)>>,
    /// Whether `check::holes_by_arguments` elaborates a failed application
    /// again now: not while an argument is checked in place that is checked
    /// again after its application's expected type if it fails
    /// (`check::explicit_arg`, `check::lambda_arg`), where it would be tried
    /// again then with more known. Day 16 of 2020's `runsNotes` retried 816
    /// such calls, all failing again, at 326 million steps against the
    /// proof's 42 million. Nor, there, is a failing argument held
    /// ([`Decl::holds_put_off`]).
    pub(crate) holes_retry: Cell<HolesRetry>,
    /// Set when a retry or a held argument's check was put off
    /// ([`HolesRetry::Deferred`]), until the argument checked in place that
    /// put it off ends.
    pub(crate) holes_retry_skipped: Cell<bool>,
    /// Whether an argument that fails in place is not held for after its
    /// application's expected type but fails the argument around it, to be
    /// checked again with more known (`check::explicit_arg_failed`): set
    /// while an argument is checked in place that is checked again if it
    /// fails ([`HolesRetry::Deferred`]), and cleared again inside it while a
    /// held argument is checked after its own application's expected type
    /// (`check::finish_application`), where holding is what lets an
    /// argument that only that check fixes succeed. Held at every level,
    /// the nine nested `Parse.runsBind`s of 2020 day 16's `runsNotes` cost
    /// 40 million steps, the innermost elaborated 192 times; put off, 2.4
    /// million (SW-4582, SW-4595).
    pub(crate) holds_put_off: Cell<bool>,
    /// Above zero while a lambda is checked in place in an application
    /// elaborated again after a propagation by `_`s failed
    /// (`check::apply_args_postponing`): a lambda inside is not tried in
    /// place first, only after its application's expected type, so nested
    /// lambdas that fail aren't each checked twice per level (SW-2638).
    pub(crate) in_place_trial: Cell<usize>,
    /// Set while asking whether an expression in a pure context performs
    /// anything besides calls whose result is in a bare row (`{e} b`, as
    /// `List.map`'s): those are elaborated as plain calls first, and the row
    /// is settled by unification (`check::pure_first`).
    pub(crate) bare_rows_pure: Cell<bool>,
    /// The effects pre-pass's answers for the declaration
    /// (`crate::performs_memo`).
    pub(crate) performs_memo: RefCell<crate::performs_memo::Memo>,
    /// Above zero while an application is elaborated again after failing,
    /// with an argument that is a list of numbers checked after the
    /// arguments after it, so they can say its element type
    /// (`check::retrying`).
    pub(crate) late_literals: Cell<usize>,
    /// The address of the condition whose `Bool` reading `logic::condition`
    /// is trying, or 0: a proposition there isn't decided into a `Bool` by
    /// `check::decide_to_bool`, as the condition's proposition reading does
    /// that its own way.
    pub(crate) condition: Cell<usize>,
    /// The addresses of the expressions a `Bool` isn't read as a proposition
    /// at, though one is expected there (`check::bool_as_prop`): a side of
    /// an `=` between propositions, and the operands of the `∧`, `∨` and `¬`
    /// that side is made of, where coercing would turn a comparison of
    /// `Bool`s into an equation between propositions; and the results of an
    /// `if`, `let` or `match` checked against `Prop`, which is coerced whole
    /// instead (`check::whole_test`).
    pub(crate) not_coerced: RefCell<Vec<usize>>,
    /// The short names written where a type is wanted (a type's head and
    /// its bare arguments): one of them that means both a type and its
    /// constructor of the same name is the type (`check::type_names`).
    pub(crate) type_names: RefCell<Vec<String>>,
    /// While `logic::condition` tries the `Bool` reading of a condition `a
    /// && b`: the address of `a`, and the conjunction that reading decides
    /// with its decision, once `logic::as_bool` has found them. A guard.
    pub(crate) conjunction: RefCell<Option<Conjunction>>,
    /// While an application checked against a known type is inferred
    /// (`check::fallback`): the address of its last written argument and
    /// that type, so a lambda argument that fails where its type still has
    /// unknowns is checked again once the application's type has been
    /// compared with it (`check::apply_args_postponing`). The second type is
    /// the first before it was forced (a call such as `Parse.Runs p …`, not
    /// its unfolding), for `check::settle_from_expected`.
    pub(crate) app_expected: RefCell<Option<AppExpected>>,
    /// The type [`check_value`](crate::check::check_value) is checking
    /// against, as written, when that is a call of a definition (`Grid`):
    /// [`Ctx::mismatch`] shows it instead of the unfolding the arms compare
    /// with, if the two print alike.
    pub(crate) written_expected: RefCell<Option<Value>>,
    /// The calls `check::settle_from_expected` gave type arguments from
    /// their expected type, in the body attempt being elaborated, also in
    /// parts of it later undone (which can only cost a retry not needed).
    /// If the attempt fails, it is made once more with nothing settled
    /// (`Elaborator::settle_retried`), which reads them.
    pub(crate) settled: RefCell<Vec<Settled>>,
    /// Set while `check::settle_from_expected` may give type arguments: in
    /// a body's first attempt (`Elaborator::settle_retried`), which is
    /// retried without if it fails.
    pub(crate) settling: Cell<bool>,
    /// While the body of a definition with `decreasing` is elaborated: what
    /// its recursive calls stand for (`decreasing.rs`).
    pub(crate) decreasing: RefCell<Option<decreasing::Active>>,
    /// While the members of a partial recursive group are described: their
    /// private recursion signature (`partial.rs`).
    pub(crate) recursion: Option<effects::Recursion>,
    /// While lifting, the `let`s each draft's terms are folded back to
    /// (`lift::Arounds`); empty otherwise.
    pub(crate) arounds: RefCell<lift::Arounds>,
    /// Run bodies for lifted helpers that take a `let`'s value from their
    /// caller, set once the helper is final (`lift.rs`). A helper is final
    /// when its owner is, in the same declaration; one whose owner failed
    /// never is, and its entry is dropped with the declaration. (Before
    /// SW-1149 such entries stayed for the session, put back at each
    /// `set_run_bodies`, and did nothing.)
    pub(crate) pending_run_bodies: Vec<(DefId, Term)>,
    /// While a declaration is elaborated: its key, then the names of the
    /// local definitions being elaborated inside it, for their keys
    /// (`local.rs`).
    pub(crate) owner: RefCell<Vec<String>>,
    /// While a top-level declaration's body is elaborated: its declared type
    /// (and where it is), whose erasure decides whether `match reify` may be
    /// used in it (D1147, `reify.rs`). `None` elsewhere.
    pub(crate) body_type: RefCell<Option<(Value, Span)>>,
    /// Local definitions admitted after an attempt at their owner's body
    /// failed, by key, for the next attempt (`local.rs`).
    pub(crate) preadmitted: RefCell<HashMap<String, lift::Resolved>>,
    /// By declaration key: how many `match`es its type has, by the prefix
    /// they're numbered under, so that the body's are numbered after them
    /// (docs/proposals/syntax-conveniences.md §2.4). Written each time the
    /// type is elaborated and only read when the body's are lifted, so an
    /// attempt at the body that's undone or tried again numbers the same.
    /// A declaration's type and body are elaborated in the same
    /// declaration, and the row is written before it is read, so nothing
    /// later reads it: it isn't a table (SW-1149).
    pub(crate) signature_matches: HashMap<String, HashMap<String, usize>>,
    /// While the body of a declaration with an `unfolding` clause is
    /// elaborated: that clause, which each helper lifted from the body (a
    /// `match`, a local definition) gets too, opaque, so its body may use
    /// what the declaration's may (docs/proposals/opaque-definitions.md
    /// §6.4: a definition that unfolds others must be opaque). `None`
    /// elsewhere (`opaque.rs`).
    pub(crate) owner_unfolding: RefCell<Option<Rc<[DefId]>>>,
    /// The helpers [`Self::owner_unfolding`] made opaque that were admitted
    /// on their own, before their owner: the owner unfolds them.
    pub(crate) owner_helpers: RefCell<Vec<DefId>>,
    /// The local definitions lifted from the declaration (or group) being
    /// checked, bound in the module's scope once it's final.
    pub(crate) local_helpers: Vec<(String, DefId, Span)>,
    /// While a `rewrite` rule is elaborated (`rewrite.rs`), each `_` it
    /// makes: the metavariable, the number of variables in scope, and the
    /// type expected there, so `rewrite` can prove the premises left open.
    pub(crate) hole_log: RefCell<Option<Vec<(Term, usize, Value)>>>,
    /// While set, a signature's bare row variables get no divergence index:
    /// they stand for total rows only, as before stage 3 (D1215's re-check).
    pub(crate) total_rows_only: Cell<bool>,
    /// Whether an instance's signature is being elaborated: there, a data
    /// type's `auto` parameter must be written as a variable
    /// (docs/proposals/interfaces.md §7.5).
    pub(crate) in_instance_signature: Cell<bool>,
    /// Where each arm's leaves are in the case trees checked for the
    /// declaration being elaborated, for its generated equations
    /// (`equations.rs`, docs/proposals/function-equations.md §9 stage 1a).
    pub(crate) leaf_log: RefCell<equations::LeafLog>,
    /// What `equations.rs`'s probe saw: the context at an arm's leaf.
    pub(crate) arm_probe: RefCell<equations::ProbeState>,
    /// The local definitions elaborated in the declaration being checked,
    /// by key, for their equations once their owner is final.
    pub(crate) local_asts: RefCell<Vec<(String, ast::LocalDef)>>,
    /// Each lifted `match` whose scrutinee isn't a plain variable, such as
    /// `match (xs, n) with` or `match k + 0 with`: its span, how it was
    /// written, the variables it was built from, and whether it was a tuple,
    /// so a termination error inside it can say why (SW-941, SW-4803,
    /// `lift.rs`). A termination error's labels are at calls in the group
    /// being admitted, so only this declaration's matches can explain it.
    /// (Before SW-1149 it was a log that only grew, emptied only by a
    /// rewind.)
    pub(crate) computed_matches: RefCell<Vec<ComputedMatch>>,
    /// The calls of lifted `match` helpers the printer showed as
    /// `(match … with …)`, by that text, so `explain_lifted` finds which
    /// `match` a message means. Kept between declarations like
    /// [`Self::stuck_on_goal`] (the messages are explained after the
    /// declaration is done), and emptied as the next one starts.
    pub(crate) matches_shown: RefCell<Vec<(String, DefId)>>,
    /// The characters whose patterns became number patterns (by span), so
    /// a missing case can be reported as characters. Cleared with the rest of
    /// the declaration's state ([`Decl::reset`]). (Before SW-1149 it grew over the
    /// session, emptied only by a rewind.)
    pub(crate) char_patterns: RefCell<HashMap<Span, char>>,
    /// The spans of the patterns a text pattern was expanded to (its list
    /// cells and each of its characters), each to the text pattern's own
    /// span, so that a case left out among them is reported as a text one
    /// (docs/proposals/text-patterns.md §4.4). Cleared per declaration, like
    /// [`Self::char_patterns`].
    pub(crate) text_spans: RefCell<HashMap<Span, Span>>,
    /// The text patterns that fixed a column of a type not yet known to
    /// `Text`, so that a later mismatch of `Text` with something else can
    /// point at them (SW-3295). Cleared per declaration.
    pub(crate) text_fallbacks: RefCell<Vec<Span>>,
    /// The variables (by level) such a pattern fixed to `Text`, each with
    /// its pattern, and the uses of them noted so far (SW-3315): a mismatch
    /// at a use gets the pattern's label whichever side is the `Text`.
    pub(crate) text_fixed_vars: RefCell<Vec<(usize, Span)>>,
    pub(crate) text_fixed_uses: RefCell<Vec<(Span, Span)>>,
    /// The guarded rows' `else` trees made so far by the pattern match being
    /// compiled, which bound how much a guard may copy (`MAX_GUARD_NODES`).
    pub(crate) guard_nodes: Cell<usize>,
    /// How deep the checker is in a guard chain checked only for its arms'
    /// errors, its term thrown away (the chain's case is impossible): a
    /// case filled in at its end isn't lifted into a helper there.
    pub(crate) errors_only: Cell<usize>,
    /// How deep the checker is in a `match` checked again for its cases
    /// alone (`deletable`): an arm's body stands for itself unchecked.
    pub(crate) coverage_only: Cell<usize>,
    /// Above zero while `byComputing` is tried only to see whether it
    /// closes a goal, its error thrown away (`rewrite repeatedly`'s
    /// closers): a failure is a bare `E-REFL`, without the message's
    /// read-backs and printing, which cost more than the comparison.
    pub(crate) quiet_refl: Cell<usize>,
    /// The scrutinees (by span) of unnamed generalised `match`es whose
    /// arms met a comparison that the `match`'s equation would have
    /// carried a proof across: such a `match` checks its arms again with a
    /// hidden equation if they failed (`matching::in_arms_or_equation`,
    /// docs/proposals/match-refinement.md R2). Kept across attempts on
    /// purpose: the attempt that wanted the equation is undone before the
    /// `match` reads it.
    pub(crate) equation_wanted: RefCell<Vec<Span>>,
    /// The conditions (by span) of the guards whose refined arms are being
    /// checked (`matching::refined_guard`): a `rewrite` in them that finds
    /// nothing because the refinement already replaced the condition is a
    /// warning, not an error (`W-REWRITE-GUARD-REFINED`, D3701).
    pub(crate) guard_refined: RefCell<Vec<Span>>,
    /// Above 0 while a guarded proof arm whose refined split failed is
    /// checked again unrefined (`check::check_guard_if`): the guards inside
    /// don't refine either.
    pub(crate) unrefined_guards: Cell<usize>,
    /// Above 0 while a refined split is checked again for its errors, after
    /// the unrefined one failed too: the guards inside don't retry.
    pub(crate) guard_no_retry: Cell<usize>,
    /// The clauses of a `match reify` being checked. Each one is required
    /// whatever its case, so `W-UNREACHABLE` doesn't offer to delete them
    /// (`reify.rs`, `families.rs`).
    pub(crate) keep_arms: RefCell<Vec<Span>>,
    /// The arms a `W-UNREACHABLE` ("this case can't happen") isn't offered
    /// for, because some check of their `match` found the case possible or
    /// couldn't delete the arm. A `match` in an arm that is split further
    /// (`match z, xs` with an arm `z, [x, ..rest]`) is checked once for each
    /// case of the split, and an arm ruled out in one may not be in the
    /// next: offering each check's arms would delete them all.
    pub(crate) kept_by_a_check: RefCell<Vec<Span>>,
    /// Where the body being checked may build a test fact from a proof of
    /// its reading, what it built, and where it wrote `.read`
    /// (`build.rs`). Kept across the attempts at one body on purpose: a
    /// failed attempt is what adds a place.
    pub(crate) builds: RefCell<crate::build::Builds>,
    /// Where an `a != b` was written with the ASCII `!=` (not the Unicode
    /// `≠`): the `!=` note quotes the source, so it is given only where the
    /// source wrote `!=` (SW-3125). Unlike [`Self::builds`], a declaration's
    /// type keeps it visible while its body is checked.
    pub(crate) ne_ascii: RefCell<Vec<Span>>,
    /// The failed instance the last instance search reached, if any: a
    /// derive records it so a use waits for it (SW-3078).
    pub(crate) failed_instance: RefCell<Option<DefId>>,
}

/// [`Decl::conjunction`].
/// A call `check::settle_from_expected` gave a type argument from its
/// expected type (`Decl::settled`).
pub(crate) struct Settled {
    /// The call, or its arguments.
    pub(crate) span: Span,
    /// The first parameter given and the type it was given, for the note
    /// made if the call fails.
    pub(crate) param: stitchwort_core::Name,
    pub(crate) given: Value,
    /// `given` printed, set with `note`: to tell whether an error is about it.
    pub(crate) given_shown: Option<String>,
    /// What an error from the call is given if the body fails with it,
    /// made when the call fails, while its unknowns are still solved.
    pub(crate) note: Option<String>,
}

pub(crate) struct Conjunction {
    /// The address of the condition's left operand.
    pub(crate) lhs: usize,
    /// The conjunction of the operands and its decision.
    pub(crate) found: Option<(Term, Term)>,
}

impl Decl {
    /// Notes the `a != b` written `!=` at `span` (SW-3125).
    pub(crate) fn note_ne_ascii(&self, span: Span) {
        let mut spans = self.ne_ascii.borrow_mut();
        if !spans.contains(&span) {
            spans.push(span);
        }
    }

    /// Whether an `a != b` written `!=` (not `≠`) starts at `span`.
    pub(crate) fn wrote_ascii_ne_at(&self, span: &Span) -> bool {
        self.ne_ascii.borrow().contains(span)
    }

    /// Empties everything but [`Self::failed_mentioned`] and
    /// [`Self::stuck_on_goal`].
    pub(crate) fn reset(&mut self) {
        let failed_mentioned = self.failed_mentioned.get();
        let stuck_on_goal = self.stuck_on_goal.take();
        let matches_shown = self.matches_shown.take();
        *self = Decl {
            matches_shown: RefCell::new(matches_shown),
            failed_mentioned: Cell::new(failed_mentioned),
            stuck_on_goal: RefCell::new(stuck_on_goal),
            ..Decl::default()
        };
    }

    /// Empties everything, the flags too: a rewind.
    pub(crate) fn rewind(&mut self) {
        self.reset();
        self.failed_mentioned.set(false);
        self.stuck_on_goal.take();
        self.matches_shown.take();
    }

    /// The first field that isn't empty, if any: none should be between
    /// declarations, where a rewind mark is taken.
    pub(crate) fn leftover(&self) -> Option<&'static str> {
        let Decl {
            // Kept between declarations on purpose (see its doc).
            failed_mentioned: _,
            stuck_on_goal: _,
            matches_shown: _,
            sides_capture,
            arm_reach,
            no_propagation,
            no_hole_propagation,
            no_argument_propagation,
            no_holding,
            holes_by_arguments,
            holes_watched,
            holes_retry,
            holes_retry_skipped,
            holds_put_off,
            in_place_trial,
            bare_rows_pure,
            performs_memo,
            late_literals,
            condition,
            not_coerced,
            type_names,
            conjunction,
            app_expected,
            written_expected,
            settled,
            settling,
            decreasing,
            recursion,
            arounds,
            pending_run_bodies,
            owner,
            body_type,
            preadmitted,
            signature_matches,
            owner_unfolding,
            owner_helpers,
            local_helpers,
            hole_log,
            total_rows_only,
            in_instance_signature,
            leaf_log,
            arm_probe,
            local_asts,
            computed_matches,
            char_patterns,
            text_spans,
            text_fallbacks,
            text_fixed_vars,
            text_fixed_uses,
            guard_nodes,
            errors_only,
            coverage_only,
            quiet_refl,
            equation_wanted,
            guard_refined,
            unrefined_guards,
            guard_no_retry,
            keep_arms,
            kept_by_a_check,
            builds,
            ne_ascii,
            failed_instance,
        } = self;
        let fields = [
            ("sides_capture", sides_capture.borrow().is_empty()),
            ("arm_reach", arm_reach.borrow().is_empty()),
            ("no_propagation", no_propagation.get() == 0),
            ("no_hole_propagation", no_hole_propagation.get() == 0),
            (
                "no_argument_propagation",
                no_argument_propagation.get() == 0,
            ),
            ("no_holding", no_holding.get() == 0),
            ("holes_by_arguments", holes_by_arguments.get() == 0),
            ("holes_watched", holes_watched.borrow().is_empty()),
            ("holes_retry", holes_retry.get() == HolesRetry::Now),
            ("holes_retry_skipped", !holes_retry_skipped.get()),
            ("holds_put_off", !holds_put_off.get()),
            ("in_place_trial", in_place_trial.get() == 0),
            ("bare_rows_pure", !bare_rows_pure.get()),
            ("performs_memo", performs_memo.borrow().is_empty()),
            ("late_literals", late_literals.get() == 0),
            ("condition", condition.get() == 0),
            ("not_coerced", not_coerced.borrow().is_empty()),
            ("type_names", type_names.borrow().is_empty()),
            ("conjunction", conjunction.borrow().is_none()),
            ("app_expected", app_expected.borrow().is_none()),
            ("written_expected", written_expected.borrow().is_none()),
            ("settled", settled.borrow().is_empty()),
            ("settling", !settling.get()),
            ("decreasing", decreasing.borrow().is_none()),
            ("recursion", recursion.is_none()),
            ("arounds", arounds.borrow().is_empty()),
            ("pending_run_bodies", pending_run_bodies.is_empty()),
            ("owner", owner.borrow().is_empty()),
            ("body_type", body_type.borrow().is_none()),
            ("preadmitted", preadmitted.borrow().is_empty()),
            ("signature_matches", signature_matches.is_empty()),
            ("owner_unfolding", owner_unfolding.borrow().is_none()),
            ("owner_helpers", owner_helpers.borrow().is_empty()),
            ("local_helpers", local_helpers.is_empty()),
            ("hole_log", hole_log.borrow().is_none()),
            ("total_rows_only", !total_rows_only.get()),
            ("in_instance_signature", !in_instance_signature.get()),
            ("leaf_log", leaf_log.borrow().is_empty()),
            ("arm_probe", arm_probe.borrow().is_empty()),
            ("local_asts", local_asts.borrow().is_empty()),
            ("computed_matches", computed_matches.borrow().is_empty()),
            ("char_patterns", char_patterns.borrow().is_empty()),
            ("text_spans", text_spans.borrow().is_empty()),
            ("text_fallbacks", text_fallbacks.borrow().is_empty()),
            ("text_fixed_vars", text_fixed_vars.borrow().is_empty()),
            ("text_fixed_uses", text_fixed_uses.borrow().is_empty()),
            ("guard_nodes", guard_nodes.get() == 0),
            ("errors_only", errors_only.get() == 0),
            ("coverage_only", coverage_only.get() == 0),
            ("quiet_refl", quiet_refl.get() == 0),
            ("equation_wanted", equation_wanted.borrow().is_empty()),
            ("guard_refined", guard_refined.borrow().is_empty()),
            ("unrefined_guards", unrefined_guards.get() == 0),
            ("guard_no_retry", guard_no_retry.get() == 0),
            ("keep_arms", keep_arms.borrow().is_empty()),
            ("kept_by_a_check", kept_by_a_check.borrow().is_empty()),
            ("builds", builds.borrow().is_empty()),
            ("ne_ascii", ne_ascii.borrow().is_empty()),
            ("failed_instance", failed_instance.borrow().is_none()),
        ];
        fields
            .into_iter()
            .find(|(_, empty)| !empty)
            .map(|(name, _)| name)
    }
}

/// The application [`Decl::app_expected`] describes: the address of
/// its last written argument, the type expected of it, forced and as
/// written, and whether its lambdas wait for that type without a trial in
/// place (`check::infer_expecting`).
pub(crate) struct AppExpected {
    pub(crate) key: usize,
    pub(crate) expected: Value,
    pub(crate) named: Value,
    pub(crate) hold_lambdas: bool,
}
