//! [`Unit`]: the state of the unit being elaborated (a standard library
//! file, a project namespace, a file on its own, or what is typed in after
//! one). A library file loaded in the middle of another unit is elaborated
//! as a unit of its own: the outer one is set aside whole
//! ([`Unit::nested`], [`Unit::leave`]), so a new field can't be forgotten
//! there.
//!
//! Unlike [`super::Decl`], a unit's state outlives a rewind mark: what the
//! last unit elaborated leaves (its module, its namespace) is what names
//! typed in afterwards are read in (`eval`, the REPL, `search --at`), so a
//! mark keeps a copy of those fields ([`Unit::mark`]).

use std::cell::RefCell;

use stitchwort_syntax::Diagnostic;

use crate::{cache, module, project};

#[derive(Default)]
pub(crate) struct Unit {
    /// The module being elaborated, and what's being checked in it. Kept
    /// after the module is elaborated (`use_file_scope`, `eval`).
    pub(crate) module: module::ModuleState,
    /// The current module's key prefix: `Day05.` in namespace `Day05`, empty
    /// for a file without a namespace line. Kept after the module is
    /// elaborated, so names typed in afterwards (`eval`, the REPL, `main`)
    /// are read as in the file.
    pub(crate) namespace_root: String,
    /// While a single file from inside a project is loaded: what to say
    /// when it uses the project (`E-FILE-MODE`). Set by the host.
    pub(crate) file_mode: Option<project::FileModeContext>,
    /// Where in the include root the next file loaded on its own is: set by
    /// the host, and taken by it when it adds the file
    /// (`take_next_include_location`).
    pub(crate) next_include_location: Option<String>,
    /// While the prelude is loaded, its built-in types and natively
    /// implemented definitions are registered with the kernel by name. Set
    /// for every library file, and by hosts and tests that load core-like
    /// source.
    pub(crate) loading_prelude: bool,
    /// Warnings found while elaborating the current declaration. Only
    /// declaration-level code (`&mut self`) adds them, so an attempt undone
    /// by `undo.rs` can't have added any.
    pub(crate) warnings: Vec<Diagnostic>,
    /// While a project namespace that may be cached is elaborated: what it
    /// is compared against at the end (`cache`).
    pub(crate) namespace_capture: Option<cache::Capture>,
    /// The namespace's files were already walked for navigation by a
    /// replay that failed part way (`cache`): don't walk them again.
    pub(crate) skip_navigation_walk: bool,
    /// Whether the module being elaborated loads `omega`'s library, so
    /// `auto` may prove what it can't decide by `omega` (`auto.rs`). Set by
    /// each module after its library files load.
    ///
    /// Not set aside by a nested load, unlike the rest: a library file
    /// loaded inside a unit leaves its own value behind, and equations made
    /// on demand in a library file's scope see the outer unit's. A module
    /// sets it after its own loads, so only what is elaborated after a load
    /// and before the next module sees a library file's value (`eval` after
    /// `prepare_expr`). Nor is it rewound. Both as before SW-1149, kept so
    /// that the move changed nothing.
    pub(crate) omega_for_auto: bool,
    /// The files `include` read in the namespace being elaborated, with a
    /// hash of their text, for its cache entry.
    pub(crate) include_trace: RefCell<Vec<(String, cache::Key)>>,
}

/// What a rewind mark keeps of a [`Unit`]: the fields that outlive a unit.
pub(crate) struct Mark {
    module: module::ModuleState,
    namespace_root: String,
    file_mode: Option<project::FileModeContext>,
    next_include_location: Option<String>,
    loading_prelude: bool,
    warnings: Vec<Diagnostic>,
}

impl Unit {
    /// The unit a library file loaded inside this one starts with.
    pub(crate) fn nested(&self) -> Unit {
        let Unit {
            module: _,
            namespace_root: _,
            file_mode: _,
            next_include_location: _,
            loading_prelude: _,
            warnings: _,
            namespace_capture: _,
            skip_navigation_walk: _,
            omega_for_auto,
            include_trace: _,
        } = self;
        Unit {
            module: module::ModuleState::default(),
            namespace_root: String::new(),
            file_mode: None,
            next_include_location: None,
            loading_prelude: true,
            warnings: Vec::new(),
            namespace_capture: None,
            skip_navigation_walk: false,
            // Carried in and out (see the field).
            omega_for_auto: *omega_for_auto,
            include_trace: RefCell::default(),
        }
    }

    /// Back to `outer` once the nested unit is done (`self` is the nested
    /// unit [`Unit::nested`] started).
    pub(crate) fn leave(&mut self, outer: Unit) {
        let Unit {
            // Dropped with the library file: what it reported was returned
            // by its load.
            module: _,
            namespace_root: _,
            file_mode: _,
            next_include_location: _,
            loading_prelude: _,
            warnings: _,
            namespace_capture: _,
            skip_navigation_walk: _,
            include_trace: _,
            // Carried out (see the field).
            omega_for_auto,
        } = std::mem::replace(self, outer);
        self.omega_for_auto = omega_for_auto;
    }

    /// What a rewind mark keeps. Only between units: no namespace is being
    /// captured for the cache.
    pub(crate) fn mark(&self) -> Mark {
        let Unit {
            module,
            namespace_root,
            file_mode,
            next_include_location,
            loading_prelude,
            warnings,
            namespace_capture,
            skip_navigation_walk,
            // Not rewound (see the field).
            omega_for_auto: _,
            // Emptied by a rewind: a namespace empties it before it's read.
            include_trace: _,
        } = self;
        assert!(
            namespace_capture.is_none() && !skip_navigation_walk,
            "a mark in the middle of a unit"
        );
        Mark {
            module: module.clone(),
            namespace_root: namespace_root.clone(),
            file_mode: file_mode.clone(),
            next_include_location: next_include_location.clone(),
            loading_prelude: *loading_prelude,
            warnings: warnings.clone(),
        }
    }

    /// Back to `mark`.
    pub(crate) fn rewind(&mut self, mark: &Mark) {
        let Unit {
            module,
            namespace_root,
            file_mode,
            next_include_location,
            loading_prelude,
            warnings,
            namespace_capture,
            skip_navigation_walk,
            omega_for_auto: _,
            include_trace,
        } = self;
        *module = mark.module.clone();
        *namespace_root = mark.namespace_root.clone();
        *file_mode = mark.file_mode.clone();
        *next_include_location = mark.next_include_location.clone();
        *loading_prelude = mark.loading_prelude;
        *warnings = mark.warnings.clone();
        *namespace_capture = None;
        *skip_navigation_walk = false;
        include_trace.get_mut().clear();
    }
}
