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
    /// While `logic::condition` tries the `Bool` reading of a condition `a
    /// && b`: the address of `a`, and the conjunction that reading decides
    /// with its decision, once `logic::as_bool` has found them. A guard.
    pub(crate) conjunction: RefCell<Option<Conjunction>>,
    /// While an application checked against a known type is inferred
    /// (`check::fallback`): the address of its last written argument and
    /// that type, so a lambda argument that fails where its type still has
    /// unknowns is checked again once the application's type has been
    /// compared with it (`check::apply_args_postponing`).
    pub(crate) app_expected: RefCell<Option<(usize, Value)>>,
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
    /// Each `match` on a tuple of variables, `match (xs, n) with`: its span,
    /// the tuple as written, and the variables, so a termination error inside
    /// it can say why (SW-941, `lift.rs`). A termination error's labels are
    /// at calls in the group being admitted, so only this declaration's
    /// matches can explain it. (Before SW-1149 it was a log that only grew,
    /// emptied only by a rewind.)
    pub(crate) tuple_matches: RefCell<Vec<(Span, String, Vec<String>)>>,
    /// The calls of lifted `match` helpers the printer showed as
    /// `(match … with …)`, by that text, so `explain_lifted` finds which
    /// `match` a message means. Kept between declarations like
    /// [`Self::stuck_on_goal`] (the messages are explained after the
    /// declaration is done), and emptied as the next one starts.
    pub(crate) matches_shown: RefCell<Vec<(String, DefId)>>,
    /// The characters whose patterns became number patterns (by span), so
    /// a missing case can be reported as characters. Written and read while
    /// one pattern match is compiled. (Before SW-1149 it grew over the
    /// session, emptied only by a rewind.)
    pub(crate) char_patterns: RefCell<HashMap<Span, char>>,
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
    /// The clauses of a `match reify` being checked. Each one is required
    /// whatever its case, so `W-UNREACHABLE` doesn't offer to delete them
    /// (`reify.rs`, `families.rs`).
    pub(crate) keep_arms: RefCell<Vec<Span>>,
}

/// [`Decl::conjunction`].
pub(crate) struct Conjunction {
    /// The address of the condition's left operand.
    pub(crate) lhs: usize,
    /// The conjunction of the operands and its decision.
    pub(crate) found: Option<(Term, Term)>,
}

impl Decl {
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
            in_place_trial,
            bare_rows_pure,
            late_literals,
            condition,
            not_coerced,
            conjunction,
            app_expected,
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
            tuple_matches,
            char_patterns,
            guard_nodes,
            errors_only,
            coverage_only,
            keep_arms,
        } = self;
        let fields = [
            ("sides_capture", sides_capture.borrow().is_empty()),
            ("arm_reach", arm_reach.borrow().is_empty()),
            ("no_propagation", no_propagation.get() == 0),
            ("no_hole_propagation", no_hole_propagation.get() == 0),
            ("in_place_trial", in_place_trial.get() == 0),
            ("bare_rows_pure", !bare_rows_pure.get()),
            ("late_literals", late_literals.get() == 0),
            ("condition", condition.get() == 0),
            ("not_coerced", not_coerced.borrow().is_empty()),
            ("conjunction", conjunction.borrow().is_none()),
            ("app_expected", app_expected.borrow().is_none()),
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
            ("tuple_matches", tuple_matches.borrow().is_empty()),
            ("char_patterns", char_patterns.borrow().is_empty()),
            ("guard_nodes", guard_nodes.get() == 0),
            ("errors_only", errors_only.get() == 0),
            ("coverage_only", coverage_only.get() == 0),
            ("keep_arms", keep_arms.borrow().is_empty()),
        ];
        fields
            .into_iter()
            .find(|(_, empty)| !empty)
            .map(|(name, _)| name)
    }
}
