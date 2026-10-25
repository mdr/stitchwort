//! The recording half of [`super`], compiled only with `alloc-trace`.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Alloc,
    Reuse,
    Inc,
    Dec,
    Free,
}

/// One event, with its identity normalised.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Event {
    pub(super) kind: Kind,
    pub id: u32,
    /// For `alloc` and `reuse`.
    pub tag: u32,
    pub arity: usize,
}

impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Event {
            kind,
            id,
            tag,
            arity,
        } = *self;
        match kind {
            Kind::Alloc => write!(f, "alloc #{id} tag={tag} arity={arity}"),
            Kind::Reuse => write!(f, "reuse #{id} tag={tag} arity={arity}"),
            Kind::Inc => write!(f, "inc #{id}"),
            Kind::Dec => write!(f, "dec #{id}"),
            Kind::Free => write!(f, "free #{id}"),
        }
    }
}

/// A finished recording.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Trace {
    pub events: Vec<Event>,
}

impl Trace {
    /// One event per line.
    pub fn render(&self) -> String {
        let mut out = String::new();
        for e in &self.events {
            out.push_str(&e.to_string());
            out.push('\n');
        }
        out
    }

    /// The identities allocated but never freed, in allocation order.
    pub fn leaks(&self) -> Vec<u32> {
        let mut live = BTreeMap::new();
        for e in &self.events {
            match e.kind {
                Kind::Alloc => {
                    live.insert(e.id, ());
                }
                Kind::Free => {
                    live.remove(&e.id);
                }
                _ => {}
            }
        }
        live.into_keys().collect()
    }

    /// How many events are of this kind, by name (`"alloc"`, `"reuse"`,
    /// `"inc"`, `"dec"`, `"free"`).
    pub fn count(&self, name: &str) -> usize {
        self.events
            .iter()
            .filter(|e| e.to_string().starts_with(name))
            .count()
    }
}

#[derive(Default)]
struct State {
    /// The address of each live cell, and its identity.
    live: BTreeMap<usize, u32>,
    next: u32,
    events: Vec<Event>,
}

thread_local! {
    static TRACE: RefCell<Option<State>> = const { RefCell::new(None) };
}

/// Starts recording on this thread, forgetting any recording in progress.
/// Start it before the program's values exist, so that every cell is seen
/// from its allocation.
pub fn start() {
    TRACE.with(|t| *t.borrow_mut() = Some(State::default()));
}

/// Stops recording and returns the trace (empty if none was started).
pub fn finish() -> Trace {
    let state = TRACE.with(|t| t.borrow_mut().take());
    Trace {
        events: state.map(|s| s.events).unwrap_or_default(),
    }
}

pub(super) fn record(kind: Kind, address: *const u8, tag: u32, arity: usize) {
    let _ = TRACE.try_with(|t| {
        let mut t = t.borrow_mut();
        let Some(state) = t.as_mut() else { return };
        let address = address as usize;
        // Identities are numbered by first appearance, and an address
        // that's freed is a new cell if it's used again.
        let known = if kind == Kind::Alloc {
            None
        } else {
            state.live.get(&address).copied()
        };
        let id = known.unwrap_or_else(|| {
            state.next += 1;
            state.live.insert(address, state.next - 1);
            state.next - 1
        });
        if kind == Kind::Free {
            state.live.remove(&address);
        }
        state.events.push(Event {
            kind,
            id,
            tag,
            arity,
        });
    });
}
