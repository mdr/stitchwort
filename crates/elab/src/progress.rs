//! "Still checking": what a declaration that checks for a long time is
//! computing, said while it runs (SW-2009, SW-1537).
//!
//! A host that wants the notes installs a sink once ([`report_to`]);
//! `stitchwort check` prints them to standard error. Then each declaration
//! (a component of mutually recursive ones) is checked with a
//! [`stitchwort_core::budget::ProgressSink`] installed in the budget, which
//! calls back after 250 million evaluation steps and each time the steps
//! double ([`stitchwort_core::budget::PROGRESS_FIRST`]): about 7 seconds,
//! then 14, 28, and so on, until the check finishes or runs out at its limit
//! of 10 billion. Counting steps rather than time, the notes are the same on
//! every run and need no thread or timer. Without a sink nothing is
//! installed, and checking is as it was.
//!
//! The note names the definition the evaluator last entered. Its name is
//! looked up in a copy of the environment's names taken when the
//! declaration's check began, since the sink can't reach the environment
//! while the kernel holds it; a definition made during the check (an inner
//! `match`'s function) isn't in it and isn't named.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};
use std::thread::ThreadId;

use stitchwort_core::budget::{Budget, PROGRESS_FIRST, Progress, with_commas};
use stitchwort_core::globals::Def;
use stitchwort_core::term::Name;

static SINK: OnceLock<fn(&str)> = OnceLock::new();

/// The declaration each thread is checking (a component's full names), for
/// a host that has to say where a check was when it stopped: a signal
/// handler (`stitchwort check`, SW-4032). By thread, so that when several
/// threads check at once (`check --jobs N`) one finishing a declaration
/// doesn't erase another's. A thread has no entry between declarations.
static CURRENT: Mutex<Vec<(ThreadId, String)>> = Mutex::new(Vec::new());

/// A declaration being checked, as [`begin`] set it: when several threads
/// check at once, the one begun longest ago. `None` if none is
/// (or the checks have just finished one, or haven't started one).
pub fn current() -> Option<String> {
    current_map().first().map(|(_, label)| label.clone())
}

fn current_map() -> std::sync::MutexGuard<'static, Vec<(ThreadId, String)>> {
    CURRENT
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn set_current(label: Option<String>) {
    let thread = std::thread::current().id();
    let mut current = current_map();
    current.retain(|(t, _)| *t != thread);
    if let Some(label) = label {
        current.push((thread, label));
    }
}

/// Sends "still checking" notes to `sink`, for the whole program. The first
/// sink installed stays.
pub fn report_to(sink: fn(&str)) {
    let _ = SINK.set(sink);
}

thread_local! {
    /// Every definition's name, by index, as of the last [`begin`] on this
    /// thread.
    static NAMES: Rc<RefCell<Vec<Name>>> = Rc::default();
}

/// Brings `names` up to date with `defs`. Definitions are only added, or
/// taken off the end when a failed check is undone, so only the end can
/// differ; a different environment (another session on this thread) shows
/// at the end too, and is copied afresh.
fn refresh(names: &mut Vec<Name>, defs: &[Def]) {
    names.truncate(defs.len());
    if let Some(last) = names.last()
        && **last != **defs[names.len() - 1].name()
    {
        names.clear();
    }
    names.extend(defs[names.len()..].iter().map(|d| d.name().clone()));
}

/// The note for `label`, which has taken more than `steps` of the `limit` it
/// may, last unfolding definition `name`.
pub fn message(label: &str, steps: u64, limit: u64, name: Option<&str>) -> String {
    let unfolding = name
        .and_then(crate::module::unfolding)
        .map_or(String::new(), |u| format!(", {u}"));
    format!(
        "still checking `{label}`: over {} evaluation steps so far{unfolding} (it stops at {})",
        with_commas(steps),
        with_commas(limit),
    )
}

/// Starts reporting on the check of `label` (one declaration, or a group
/// checked together), whose budget is `limit` steps, first after `after`
/// steps if given. Returns what [`end`] needs to put back: `None` if no
/// sink is installed.
pub(crate) fn begin(
    budget: &Budget,
    defs: &[Def],
    label: impl FnOnce() -> String,
    limit: u64,
    after: Option<u64>,
) -> Option<Option<Progress>> {
    let sink = *SINK.get()?;
    let names = NAMES.with(Rc::clone);
    refresh(&mut names.borrow_mut(), defs);
    let label = label();
    set_current(Some(label.clone()));
    let note = move |steps: u64, entered: Option<usize>| {
        let names = names.borrow();
        let name = entered.and_then(|i| names.get(i)).map(|n| &**n);
        sink(&message(&label, steps, limit, name));
    };
    Some(budget.set_progress(Some(Rc::new(note)), after.unwrap_or(PROGRESS_FIRST)))
}

/// Stops reporting on the check [`begin`] started, putting back the report
/// on the check it was part of, if any.
pub(crate) fn end(budget: &Budget, previous: Option<Option<Progress>>) {
    set_current(None);
    if let Some(previous) = previous {
        budget.restore_progress(previous);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_progress_note_names_the_declaration_and_what_it_unfolds() {
        assert_eq!(
            message("Main.t", 250_000_000, 10_000_000_000, Some("countdown")),
            "still checking `Main.t`: over 250,000,000 evaluation steps so far, unfolding \
             `countdown` (it stops at 10,000,000,000)"
        );
        assert_eq!(
            message("Main.t", 500_000_000, 10_000_000_000, None),
            "still checking `Main.t`: over 500,000,000 evaluation steps so far (it stops \
             at 10,000,000,000)"
        );
    }
}
