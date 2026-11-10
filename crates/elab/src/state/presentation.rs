//! [`Presentation`]: what the editor and `search` read back out of a session
//! rather than what elaboration reads: the navigation recorder, the goals
//! shown, and the counterexample searches' logs. Nothing here affects what a
//! later declaration checks as.
//!
//! Rules, one per field:
//!
//! - `nav`: only while navigation is on. Its maps are on the session's
//!   journal (put back by the journal's rewind, through [`Presentation::logged`]);
//!   its lists are cut back by length at a rewind (`Mark`); it is encoded in
//!   the check cache (`cache`) and dumped.
//! - `goal_snapshots`: the latest goals printed, as terms. Emptied by a
//!   rewind (their terms may name what is forgotten); not encoded or dumped.
//! - `counterexample_log`: only filled when `Options::log_counterexamples`
//!   is on (tests); then it only grows; a rewind leaves it; not encoded or
//!   dumped.
//! - `counterexample_memo`: the answers of searches by statement content;
//!   kept by a rewind, since a key is the content, not an id; bounded.

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_syntax::Span;

use crate::{Global, counterexample, goals, nav};

#[derive(Default)]
pub struct Presentation {
    /// What the code navigation index records, when it's on (`nav.rs`).
    pub(crate) nav: Option<RefCell<nav::Recorder>>,
    /// The latest goals printed, as terms, by where their `?` is: what
    /// `search --at` searches (SW-989).
    pub(crate) goal_snapshots: RefCell<Vec<(Span, Rc<goals::GoalSnapshot>)>>,
    /// What each counterexample search did, in this session. Only grows.
    /// Filled only when `Options::log_counterexamples` is on.
    pub counterexample_log: RefCell<Vec<counterexample::SearchLog>>,
    /// The note and log of a search, by statement (SW-1937).
    pub(crate) counterexample_memo: RefCell<
        stitchwort_core::collections::HashMap<
            counterexample::MemoKey,
            (Option<String>, counterexample::SearchLog),
        >,
    >,
}

/// What a rewind mark keeps of [`Presentation`]: where navigation's lists
/// were, if it was on.
pub(crate) struct Mark {
    nav: Option<nav::NavMark>,
}

impl Presentation {
    pub(crate) fn mark(&self) -> Mark {
        let Presentation {
            nav,
            // Emptied by a rewind, so nothing to keep.
            goal_snapshots: _,
            // Only grows.
            counterexample_log: _,
            counterexample_memo: _,
        } = self;
        Mark {
            nav: nav.as_ref().map(|n| n.borrow_mut().mark()),
        }
    }

    /// The part of the rewind that comes after the journal's: the journal
    /// has put navigation's maps back already ([`Presentation::logged`]).
    pub(crate) fn rewind(&mut self, mark: &Mark) {
        let Presentation {
            nav,
            goal_snapshots,
            // Kept: the log is for tests, the memo is by content.
            counterexample_log: _,
            counterexample_memo: _,
        } = self;
        // Their terms may name what is forgotten.
        goal_snapshots.get_mut().clear();
        if let (Some(nav), Some(at_mark)) = (nav.as_mut(), &mark.nav) {
            nav.get_mut().rewind(at_mark);
        }
    }

    /// How many statements' searches are remembered (for tests).
    pub fn remembered_searches(&self) -> usize {
        self.counterexample_memo.borrow().len()
    }

    /// Navigation's recorder, for the session's journal.
    pub(crate) fn logged(&mut self) -> Option<&mut nav::Recorder> {
        self.nav.as_mut().map(|n| n.get_mut())
    }

    /// What navigation recorded, which its index is made from.
    pub(crate) fn dump(&self, out: &mut String, now: &dyn Fn(&str) -> Option<Global>) {
        let Presentation {
            nav,
            goal_snapshots: _,
            counterexample_log: _,
            counterexample_memo: _,
        } = self;
        if let Some(nav) = nav {
            nav.borrow().dump(out, now);
        }
    }
}
