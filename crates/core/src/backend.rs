//! What the extraction backends (`crates/js`) read of a session: its
//! declarations ([`Ev`]) and the elaborator's facts about them that
//! aren't declarations, handed over by the session as a [`View`]
//! (docs/proposals/globals-split.md §2.1, D2292). The backend reads the
//! facts here and never edits the kernel's types.

use std::ops::Deref;
use std::rc::Rc;

use crate::ev::Ev;
use crate::globals::FieldDefaults;
use crate::js_repr::JsRepr;
use crate::term::DataId;

/// The elaborator's facts about data types that the backend reads. The
/// session implements it over its tables.
pub trait DataFacts {
    /// How the type crosses the JS boundary, when `js.*` attributes on it
    /// say (docs/proposals/attributes.md §4.6): resolved and checked by the
    /// elaborator once the type is final. `None` for a type without them,
    /// whose default the backend resolves when an export reaches it. Not
    /// hashed (D598); the kernel never sees it.
    fn js(&self, d: DataId) -> Option<&Rc<JsRepr>>;

    /// A type's fields' default values (docs/proposals/named-arguments.md
    /// §5.1, §5.2): for each constructor and field, the generated helper
    /// that computes the default, if the field has one. `None` for a type
    /// without defaults. Never hashed (D1099) and never seen by the kernel;
    /// the backend reads it for decoders that fill absent properties (§5.3).
    fn defaults(&self, d: DataId) -> Option<&Rc<FieldDefaults>>;
}

/// A session's declarations with its [`DataFacts`]. It derefs to the
/// [`Ev`], so the backend reads declarations through it as before.
#[derive(Clone, Copy)]
pub struct View<'a> {
    ev: Ev<'a>,
    facts: &'a dyn DataFacts,
}

impl<'a> View<'a> {
    pub fn new(ev: Ev<'a>, facts: &'a dyn DataFacts) -> View<'a> {
        View { ev, facts }
    }

    /// See [`DataFacts::js`].
    pub fn js(&self, d: DataId) -> Option<&'a Rc<JsRepr>> {
        self.facts.js(d)
    }

    /// See [`DataFacts::defaults`].
    pub fn defaults(&self, d: DataId) -> Option<&'a Rc<FieldDefaults>> {
        self.facts.defaults(d)
    }
}

impl<'a> Deref for View<'a> {
    type Target = Ev<'a>;
    fn deref(&self) -> &Ev<'a> {
        &self.ev
    }
}
