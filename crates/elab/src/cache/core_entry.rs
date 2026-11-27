//! The core's entry (SW-4814, D3746): the always-loaded core (`std/core/`)
//! kept in the check cache as a library file is, so a session that starts
//! with a cache replays it instead of elaborating and checking its
//! declarations again. Trusted on an exact key match, as library files are
//! (D1660); `--no-cache` and the tests check it from source.
//!
//! - **The key** covers the core's text as the session elaborates it, the
//!   entry format, the kernel switches and options that change results
//!   (natives, compact text, `Options::cache_key`), what navigation records,
//!   and the library's index of names, which the core's doc links are
//!   checked against ([`CoreKey`]). The stamp must be this build's, exact,
//!   against the same core and index ([`Elaborator::library_interface`],
//!   worked out before either is in the session): no carried-over hit.
//! - **What it holds** is what a library file's entry holds, plus what only
//!   the core has: its primitives (`partial::Primitive`), and the core
//!   built-ins it binds, natives included. Replay makes the same calls
//!   elaborating makes for both (`define_primitive`, `bind_builtin_*`), so
//!   the registry, the natives, the pins' checks and the slots are worked
//!   out again, not read. The warnings the core keeps
//!   (`library_warnings`) are in its head.
//! - **What it doesn't hold** is redone by the host after either path:
//!   `finish_core` and the registry's checks (docs/reviews/
//!   SW-4814-core-from-cache.md lists every piece of state).
//! - **A replay that fails once it has changed anything** is never undone
//!   in place: the host starts again with a fresh elaborator and
//!   elaborates the core ([`CoreReplay::Failed`]).

use super::*;
use crate::library::LibraryIndex;

/// The core's key and the stamp its entry must have.
pub struct CoreKey {
    key: Key,
    interface: Key,
    unit: String,
}

/// What the core's elaboration is compared against when its entry is
/// written ([`Elaborator::core_capture`]).
pub struct CoreCapture {
    transaction: Transaction,
    before: Before,
}

/// How a replay of the core went.
pub enum CoreReplay {
    /// Loaded from its entry; the warnings it keeps for `library_warnings`.
    Hit(Vec<Diagnostic>),
    /// No entry that fits, found before anything changed: elaborate it.
    Miss(String),
    /// Refused part way: what was added isn't undone, so the session
    /// must start again with a fresh elaborator.
    Failed(String),
}

/// The name entries give the core's file.
const CORE_FILE: &str = "std:core";

impl Elaborator {
    /// The key of the core whose text is `core`, elaborated in this
    /// session as it is now (its options, switches and navigation, before
    /// anything loads) against the library `index`.
    pub fn core_cache_key(&self, core: &str, index: &LibraryIndex) -> CoreKey {
        let g = &self.ev();
        let builtins = g.env.builtins();
        // Not `modes`: the compact text it reads is registered by the core.
        let modes = format!(
            "natives {} compact {} {} nav {:?}",
            !builtins.disable_natives,
            !builtins.disable_compact_text,
            self.options.cache_key(),
            self.nav_tag(),
        );
        let interface =
            library_interface_of(Some(blake3::hash(core.as_bytes()).as_bytes()), Some(index));
        let mut h = blake3::Hasher::new();
        let mut part = |bytes: &[u8]| {
            h.update(&(bytes.len() as u64).to_le_bytes());
            h.update(bytes);
        };
        part(b"stitchwort check cache: the core");
        part(&FORMAT.to_le_bytes());
        part(modes.as_bytes());
        part(core.as_bytes());
        part(&interface);
        CoreKey {
            key: *h.finalize().as_bytes(),
            interface,
            unit: format!("core{}", self.nav_tag()),
        }
    }

    /// Before the core elaborates, in a session that may write its entry:
    /// begins its transaction and starts noting the names it declares.
    pub fn core_capture(&mut self) -> CoreCapture {
        self.scope.log = Some(Vec::new());
        CoreCapture {
            transaction: self.with_journal(|journal, logs| journal.begin(logs)),
            before: self.snapshot(),
        }
    }

    /// After the core, file `file`, elaborated with no error and with
    /// `warnings` its only diagnostics: writes its entry to `store`. Ends
    /// the transaction either way. Whether it was written, or why not.
    pub fn write_core_entry(
        &mut self,
        capture: CoreCapture,
        store: &dyn Store,
        key: &CoreKey,
        file: FileId,
        warnings: &[Diagnostic],
    ) -> Result<(), String> {
        let log = self.scope.log.take().unwrap_or_default();
        let entry = if self.kernel.machine.budget.cancelled() {
            Err("cancelled".to_string())
        } else {
            self.encode_core(&capture, &log, store, key, file, warnings)
        };
        self.commit(capture.transaction);
        match entry {
            Ok(entry) => {
                store.write(&key.unit, &key.key, &entry);
                self.session.cache_stats.core_written += 1;
                Ok(())
            }
            Err(why) => {
                debug(&format!("the core can't be cached: {why}"));
                Err(why)
            }
        }
    }

    /// After the core elaborated with something that keeps its entry from
    /// being written: ends the transaction.
    pub fn abandon_core_capture(&mut self, capture: CoreCapture) {
        self.scope.log = None;
        self.commit(capture.transaction);
    }

    fn encode_core(
        &self,
        capture: &CoreCapture,
        log: &[ScopeOp],
        store: &dyn Store,
        key: &CoreKey,
        file: FileId,
        warnings: &[Diagnostic],
    ) -> Result<Vec<u8>, String> {
        let writes = self.write_set(&capture.transaction, |_| true);
        let mut changed = Vec::new();
        for &(k, old) in &writes.scope.entries {
            match (old, self.scope.stored(k)) {
                (Some(old), Some(now)) if now != old => changed.push(k.clone()),
                (Some(_), None) => return Err(format!("`{k}` was removed")),
                _ => {}
            }
        }
        changed.sort();
        let names = NamesOut {
            changed,
            early: Vec::new(),
            late: log
                .iter()
                .filter_map(|op| match op {
                    ScopeOp::New(k, follower) => Some((k.clone(), *follower)),
                    ScopeOp::Member(_) => None,
                })
                .collect(),
            members: log
                .iter()
                .filter_map(|op| match op {
                    ScopeOp::Member(k) => Some(k.clone()),
                    ScopeOp::New(..) => None,
                })
                .collect(),
        };
        let unit = UnitOut {
            file_names: HashMap::from_iter([(file, CORE_FILE.to_string())]),
            own_files: HashSet::from_iter([file]),
            library: true,
            interface: false,
            core: true,
        };
        self.encode_stamped(
            &unit,
            &capture.before,
            &writes,
            &names,
            &PreOut::default(),
            warnings,
            &key.key,
            store.salt(),
            Some((store, key.interface)),
        )
        .map(|(entry, _, _)| entry)
    }

    /// Loads the core, file `file`, from its entry in `store`, into this
    /// session, which has loaded nothing yet: through the kernel's checking
    /// calls with `recheck`, its trusted admission otherwise. Only this
    /// build's own exact entry for `key` is used.
    pub fn replay_core(
        &mut self,
        store: &dyn Store,
        key: &CoreKey,
        file: FileId,
        recheck: bool,
    ) -> CoreReplay {
        let frame = crate::timings::enabled().then(|| crate::timings::begin(&self.ev()));
        let replay = self.replay_core_untimed(store, key, file, recheck);
        if let Some(frame) = frame {
            let label = match &replay {
                CoreReplay::Hit(_) => "core (cached)",
                _ => "core (cache miss)",
            };
            crate::timings::end(frame, &self.ev(), label.to_string());
        }
        match &replay {
            CoreReplay::Hit(_) => {
                debug("the core: loaded from its entry");
                self.session.cache_stats.core_hits += 1;
                if recheck {
                    self.session.cache_stats.core_rechecked += 1;
                }
            }
            CoreReplay::Miss(why) => {
                debug(&format!("the core: a miss: {why}"));
                self.session.cache_stats.core_misses += 1;
            }
            CoreReplay::Failed(why) => debug(&format!("the core: refused: {why}")),
        }
        replay
    }

    fn replay_core_untimed(
        &mut self,
        store: &dyn Store,
        key: &CoreKey,
        file: FileId,
        recheck: bool,
    ) -> CoreReplay {
        assert!(
            self.kernel.env.defs().is_empty() && self.session.library.is_none(),
            "the core replays into a session that has loaded nothing"
        );
        let Some(bytes) = store.read(&key.unit, &key.key) else {
            return CoreReplay::Miss("no entry".to_string());
        };
        // Everything up to admission reads and changes nothing.
        let read = || -> Read<(Decoded, Vec<Diagnostic>)> {
            let (stamp, deps, body) = open(&bytes, &key.key, store.salt())?;
            if !stamp.exact
                || stamp.compiler != store.compiler()
                || stamp.interface != key.interface
            {
                return bad("written by another build, or against another core or library");
            }
            if !deps.is_empty() {
                return bad("the core's entry with dependencies");
            }
            let files = HashMap::from_iter([(CORE_FILE.to_string(), file)]);
            let mut head = self.read_head(body, &files)?;
            let warnings = std::mem::take(&mut head.pre.warnings);
            if !head.pre.is_empty() || !head.foreign.is_empty() {
                return bad("the core's entry with a namespace's parts");
            }
            let d = self.decode(&deps, head, &[], true)?;
            if !d.rest.tables.tests.is_empty() {
                return bad("the core's entry with tests");
            }
            Ok((d, warnings))
        };
        let (d, warnings) = match read() {
            Ok(read) => read,
            Err(Bad(why)) => return CoreReplay::Miss(why),
        };
        // As elaborating the core does (`elaborate_namespace_untimed`): a
        // unit of its own, and the module it leaves the session in.
        self.session.owners.begin(self.ids());
        self.unit_changed();
        self.unit.namespace_root = String::new();
        self.unit.module_path = "Std".into();
        self.unit.omega_for_auto = false;
        let hit = Hit {
            exact: true,
            recheck,
            interface: false,
        };
        if let Err(Bad(why)) =
            self.admit_replayed(&d.defs, &d.datas, &d.bound, &d.rest.tables, true, hit)
        {
            return CoreReplay::Failed(why);
        }
        self.replay_tables(d.rest, &[]);
        CoreReplay::Hit(warnings)
    }

    /// A replay of the core in a session that was then abandoned
    /// ([`CoreReplay::Failed`]) refused `recheck` or not: counted in the
    /// session started again, as a refused entry is.
    pub fn note_core_refused(&mut self, recheck: bool) {
        if recheck {
            self.session.cache_stats.refused_on_recheck += 1;
        } else {
            self.session.cache_stats.refused += 1;
        }
    }

    /// Admits primitive `def` as elaborating does: declared by its
    /// signature (checked with `check`), then defined by the kernel's own
    /// rule for it, which checks its type, and bound with its shape
    /// checked. In the core's entry (`core`) it must be one of the core's
    /// primitives (`partial::define_primitive`); in a library file's, a
    /// float primitive (`float::define_primitive`), as `std/Float`
    /// declares.
    pub(super) fn admit_primitive(
        &mut self,
        def: &DefEntry,
        expected: DefId,
        check: bool,
        core: bool,
    ) -> Result<(), Diagnostic> {
        enum Rule {
            Core(stitchwort_core::partial::Primitive),
            Float(stitchwort_core::float::FloatOp),
        }
        let rule = if core {
            stitchwort_core::partial::Primitive::named(&def.name).map(Rule::Core)
        } else {
            stitchwort_core::float::FloatOp::named(&def.name).map(Rule::Float)
        };
        let Some(rule) = rule else {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                format!("`{}` isn't a primitive", def.path),
            ));
        };
        if def.theorem
            || def.instance
            || def.fold
            || def.opaque
            || def.tailrec
            || !def.unfolding.is_empty()
            || def.run_body.is_some()
        {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                format!("the primitive `{}` carries more than its type", def.path),
            ));
        }
        module_of(&def.name, &def.path)
            .map_err(|Bad(why)| Diagnostic::error("E-MALFORMED", why))?;
        let id = self.kernel_op(|g| {
            let admit = if check {
                kernel::recheck_def
            } else {
                kernel::admit_trusted_def
            };
            admit(g, &def.name, &def.path, &def.ty, false, def.span)
        })?;
        if id != expected || *self.kernel.def(id).path() != def.path {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                "a primitive came out differently",
            ));
        }
        match rule {
            Rule::Core(prim) => {
                stitchwort_core::partial::define_primitive(&mut self.kernel, id, prim)?
            }
            Rule::Float(op) => stitchwort_core::float::define_primitive(&mut self.kernel, id, op)?,
        }
        if let Some(b) = stitchwort_core::registry::bind_def(&mut self.kernel, id) {
            stitchwort_core::registry::check_shape(&mut self.kernel, id, b)?;
        }
        Ok(())
    }
}
