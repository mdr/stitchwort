//! The check cache (docs/proposals/check-cache.md): the elaborated result
//! of a standard library file (stage 1) or of a project namespace (stage
//! 2), kept between runs, so a later run loads it instead of elaborating it
//! again.
//!
//! - **What an entry holds** (§5.1): everything loading the unit adds that
//!   later code reads. That is the kernel's new definitions and data types,
//!   with every flag, and the elaborator's side tables: the names it
//!   declares, records, interfaces, instances, abilities, the data types'
//!   owners, why `==`/`show`/`compare` aren't derived, lifted helpers,
//!   local definitions' keys, tests, warnings, and what code navigation
//!   recorded. Declarations are referred to by full path and the content
//!   hash they are expected to have, never by load-order ids, and spans as
//!   (file, byte range). A navigation target in another unit's file is kept
//!   by the name of its declaration (§4.3).
//! - **Loading is replay** (§5.2): the declarations go to the kernel in the
//!   order elaborating made them, through its trusted admission
//!   (`check::admit_trusted_*`), which installs what it checked when the
//!   entry was written without checking it again (stage 3, D1660, which
//!   reverses D277). So both elaboration and the kernel's checks are
//!   skipped, and an entry that is loaded is trusted: `--no-cache` is the
//!   full check. `Elaborator::admit_replayed` is the one place that submits
//!   them.
//! - **The key** (§4.2) is computed before anything is elaborated: the
//!   compiler build (Rust only: the library's text is not in it), the
//!   format, the modes and limits that change results, the core's text and
//!   the library's index of names ([`Elaborator::library_interface`]), and
//!   the unit's text. For a library file: its path and text, and the keys
//!   of the library files it needs. For a project namespace: the hash of
//!   its sources the host gives ([`Elaborator::set_namespace_sources`]: its
//!   files' names and text, the project's namespaces and `stitchwort.yaml`)
//!   and the keys of the namespaces it depends on (a Merkle chain). Which
//!   library files a namespace loads is only known once it is elaborated,
//!   so its entry lists them with the key each had, and replay (and a plain
//!   `check` deciding to leave the namespace out) first compares them
//!   with the keys now. The files it `include`s are listed in its entry
//!   with a hash of their text, and read again to check them.
//! - **An entry that doesn't fit is a miss**: a corrupt one (checksum), one
//!   for another key or cache directory (salt), one whose dependencies don't
//!   have the expected hashes. The unit is then elaborated, and the entry
//!   rewritten. Only units without errors are written (D284). An entry the
//!   kernel refuses partway through its replay is undone to where it began
//!   (`Kernel::forget_since`) and is a miss too, but it is never expected:
//!   it means a key that misses an input or an encoder that is wrong, so
//!   it is counted (`Stats::refused`) and the differential tests check
//!   there are none (docs/proposals/check-cache-trust.md).
//!
//! This module only encodes and replays. Where entries are kept is the
//! [`Store`] a host gives the elaborator (the CLI's is a directory).

mod codec;
mod dump;
mod rows;

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::Kernel;
use stitchwort_core::collections::{HashMap, HashSet};
use stitchwort_core::globals::HashKey;
use stitchwort_core::globals::{Ctor, State};
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::native::Native;
use stitchwort_core::registry::{Builtin, Home, Kind};
use stitchwort_core::{DataId, DefId, Ev, Name, Sort, Term};
use stitchwort_syntax::{FileId, Span};

use crate::library::{Needs, PendingKind};
use crate::nav::{LocalUse, NamedUse, Noted, ParamBinder};
use crate::project::SourceUnit;
use crate::scope::ScopeOp;
use crate::state::{self, Transaction, UnitId};
use crate::{Elaborator, Global};
pub(crate) use codec::Read;
use codec::{Bad, ReadRefs, Reader, Refs, TermWriter, Terms, Writer, bad};
use stitchwort_syntax::{Diagnostic, Label, Severity};

/// The version of the entry format, part of every key: a change to what an
/// entry holds or how it is written bumps it, and old entries are misses.
pub const FORMAT: u32 = 33;

const MAGIC: &[u8; 8] = b"SWCHECK\0";

/// A dependency in an entry's header: kind (0 a definition, 1 a data
/// type), full path, and the content hash it must have.
type Dep = (u8, String, ContentHash);

/// A key: a BLAKE3 hash.
pub type Key = [u8; 32];

/// Where entries are kept, by unit (a library file) and key.
pub trait Store {
    /// The compiler build, part of every key: its version and a
    /// fingerprint of its source.
    fn compiler(&self) -> &str;
    /// The cache directory's random salt (§3.1): an entry written with
    /// another is a miss.
    fn salt(&self) -> [u8; 16];
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>>;
    /// Best effort: a cache that can't be written just means elaborating
    /// again next time.
    fn write(&self, unit: &str, key: &Key, entry: &[u8]);
}

/// What the cache did in a session.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Library files loaded from an entry.
    pub hits: usize,
    /// Library files elaborated: no entry, or one that didn't fit.
    pub misses: usize,
    /// Library files' entries written.
    pub written: usize,
    /// Library files elaborated that can't be cached (see
    /// `Elaborator::encode`).
    pub uncacheable: usize,
    /// The same four for project namespaces.
    pub namespace_hits: usize,
    pub namespace_misses: usize,
    pub namespace_written: usize,
    pub namespace_uncacheable: usize,
    /// Namespaces checked without an error but not written because one they
    /// use failed (SW-2951). Their entry would be valid; writing it under
    /// the broken dependency's key would evict the one a fixed source finds
    /// again. Unlike `namespace_uncacheable`, this clears when that error
    /// is fixed.
    pub namespace_waiting_on_error: usize,
    /// Namespace entries found not to fit after their replay had begun
    /// (loading the library files they need): the namespace is then
    /// elaborated in what the replay left. Never expected; the differential
    /// test checks there are none.
    pub late_misses: usize,
    /// Entries, of library files or namespaces, whose declarations the
    /// kernel refused partway through their replay, or that bound other
    /// built-ins than they say: what they added is undone, and the unit
    /// elaborated. With a complete key and a correct encoder this never
    /// happens (docs/proposals/check-cache-trust.md, D2800), so the
    /// differential tests check there are none. Not counted when the
    /// operation was cancelled meanwhile (the editor's next keystroke),
    /// which also ends the kernel's calls.
    pub refused: usize,
    /// Namespaces a plain `check` reported from their entries without
    /// loading them, because nothing it checked needed them (SW-1193).
    /// Not counted in `namespace_hits`.
    pub namespace_skipped: usize,
}

/// Why a namespace's entry wasn't used: found before anything changed, or
/// after the replay had begun.
enum Miss {
    Early(String),
    Late(String),
}

/// While a project namespace that may be cached is elaborated: what its
/// entry is worked out against (`elaborate_namespace_cached`).
pub(crate) struct Capture {
    /// Begun before anything, with the namespace's unit: its entry is the
    /// write-set of the unit's own segments since (§4.8.3), which leaves
    /// out the library files loaded inside it.
    transaction: Transaction,
    unit: UnitId,
    /// The names the namespace declared before its library files loaded
    /// (`collect`), and what it needs from the library.
    early: Option<Vec<String>>,
    needs: Option<Needs>,
    /// Once its library files have loaded: what it is compared against,
    /// how many library files had loaded, and how many segments the
    /// journal had.
    before: Option<Before>,
    library_loaded: usize,
    segments: usize,
}

/// While a library file that may be cached loads: its transaction, begun
/// before it, and what it is compared against. Its entry is the write-set
/// of the units begun since (`after`): the file's, and any nested in it.
pub(crate) struct LibraryCapture {
    transaction: Transaction,
    after: UnitId,
    before: Before,
}

/// What a unit's load is compared against, to see what it added: where the
/// tables that only grow were. (What it did to the logged tables is its
/// write-set, [`WriteSet`].)
pub(crate) struct Before {
    defs: usize,
    datas: usize,
    tables: state::TablesMark,
    /// How many locals, binders, outline items, parameters and named
    /// arguments navigation held.
    nav: Option<(usize, usize, usize, usize, usize)>,
}

/// A unit's write-set (docs/proposals/elaborator-state.md §4.8.3): the keys
/// the journal's segments of the unit logged since its transaction began,
/// each with its row before, in the logged tables an entry holds rows of.
struct WriteSet<'a> {
    scope: crate::scope::Writes<'a>,
    tables: state::TablesWrites<'a>,
}

impl Elaborator {
    /// Keeps library files' results in `store` between runs, and loads them
    /// from it (see [`crate::cache`]).
    pub fn set_check_cache(&mut self, store: Rc<dyn Store>) {
        self.options.check_cache = Some(store);
    }

    /// Stops using a check cache: files are checked, not replayed, until
    /// [`Elaborator::set_check_cache`] is called again. (A rewind keeps the
    /// cache, which is not part of what it restores.)
    pub fn clear_check_cache(&mut self) {
        self.options.check_cache = None;
    }

    /// What the cache has done so far.
    pub fn check_cache_stats(&self) -> Stats {
        self.session.cache_stats
    }

    /// For tests: every namespace replay from now on fails where a
    /// dependency that isn't what the entry was made with would make it
    /// fail (a late miss), so the namespace is elaborated after all.
    #[doc(hidden)]
    pub fn fail_namespace_replays_late(&mut self) {
        self.options.fail_replays_late = true;
    }

    /// For tests: from now on, the replay of an entry (a library file's or
    /// a namespace's) that declares `path` (a full path, `Std.Float.add`)
    /// is refused, as the kernel would refuse it, right after the group
    /// with that declaration is admitted and its built-ins bound. So the
    /// undo is reached with something to take back.
    #[doc(hidden)]
    pub fn refuse_replays_after(&mut self, path: &str) {
        self.options.refuse_replays_after = Some(path.to_string());
    }

    /// Whether library files may be loaded from, and written to, the cache
    /// now. Not for the library test target, whose tests are part of the
    /// result. (A session whose core isn't the index's finds its entries'
    /// dependencies have other hashes: misses.)
    fn cache_usable(&self) -> bool {
        self.options.check_cache.is_some() && !self.options.library_tests
    }

    /// The name of the unit an entry is for: the library file, and whether
    /// navigation is recorded (an entry made without it can't give it).
    fn cache_unit(&self, f: usize) -> String {
        let index = self.library_index().expect("a library is installed");
        let path = index.files[f]
            .path
            .trim_end_matches(".sw")
            .replace('/', ".");
        let nav = self.nav_tag();
        format!("std.{path}{nav}")
    }

    /// The key of library file `f` (§4.2), and of the files it needs.
    pub(crate) fn library_key(&self, f: usize) -> Key {
        self.library_keys(&BTreeSet::from([f]))[&f]
    }

    /// The keys of the library files `roots` and every file they need: each
    /// covers the file's own text and the keys of the files it needs, so a
    /// change to a file's text changes the key of every file that reaches it.
    fn library_keys(&self, roots: &BTreeSet<usize>) -> HashMap<usize, Key> {
        let index = self.library_index().expect("a library is installed");
        let store = self.options.check_cache.as_ref().expect("a cache is set");
        let interface = self.library_interface();
        let mut keys: HashMap<usize, Key> = HashMap::default();
        // Dependencies first: the edges never form a cycle (the index is
        // checked), so a work list in post-order ends.
        let mut stack: Vec<(usize, bool)> = roots.iter().map(|&f| (f, false)).collect();
        while let Some((file, ready)) = stack.pop() {
            if keys.contains_key(&file) {
                continue;
            }
            if !ready {
                stack.push((file, true));
                stack.extend(index.files[file].edges.iter().map(|&e| (e, false)));
                continue;
            }
            let mut h = blake3::Hasher::new();
            let mut part = |bytes: &[u8]| {
                h.update(&(bytes.len() as u64).to_le_bytes());
                h.update(bytes);
            };
            part(b"stitchwort check cache");
            part(&FORMAT.to_le_bytes());
            part(store.compiler().as_bytes());
            part(self.modes().as_bytes());
            part(&interface);
            part(index.files[file].path.as_bytes());
            part(index.files[file].text.as_bytes());
            for e in &index.files[file].edges {
                part(&keys[e]);
            }
            keys.insert(file, *h.finalize().as_bytes());
        }
        keys
    }

    /// Everything else that changes what elaborating a library file gives.
    fn modes(&self) -> String {
        let g = &self.ev();
        format!(
            "natives {} compact {} {} nav {:?}",
            !g.env.builtins().disable_natives,
            g.env.builtins().compact_literals().is_some(),
            self.options.cache_key(),
            self.nav_tag(),
        )
    }

    /// What navigation records, as part of a cache key: entries made with
    /// less aren't used.
    fn nav_tag(&self) -> &'static str {
        match &self.present.nav {
            None => "",
            Some(nav) if nav.borrow().exprs => "+nav+ty",
            Some(_) => "+nav",
        }
    }

    /// Before library file `f` loads: whether to try the cache, and if
    /// so, its unit and key.
    pub(crate) fn cache_lookup(&self, f: usize) -> Option<(String, Key)> {
        if !self.cache_usable() {
            return None;
        }
        Some((self.cache_unit(f), self.library_key(f)))
    }

    /// Loads library file `f` from the entry for `key`, if there is one and
    /// it fits; `false` if it has to be elaborated instead (and then
    /// nothing has changed).
    pub(crate) fn load_from_cache(&mut self, f: usize, unit: &str, key: &Key) -> bool {
        let store = self.options.check_cache.clone().expect("a cache is set");
        let Some(bytes) = store.read(unit, key) else {
            self.session.cache_stats.misses += 1;
            return false;
        };
        match self.replay(&bytes, key, store.salt()) {
            Ok(()) => {
                self.session.cache_stats.hits += 1;
                true
            }
            Err(Bad(why)) => {
                debug(&format!("std file {f}: a miss: {why}"));
                self.session.cache_stats.misses += 1;
                false
            }
        }
    }

    /// Before library file `f` loads, to see what it added once it has:
    /// begins its transaction, and starts noting the names it declares.
    pub(crate) fn cache_before(&mut self) -> LibraryCapture {
        self.scope.log = Some(Vec::new());
        LibraryCapture {
            transaction: self.with_journal(|journal, logs| journal.begin(logs)),
            after: self.session.owners.last(),
            before: self.snapshot(),
        }
    }

    /// The write-set of the units `own` picks since `t` began.
    fn write_set(&self, t: &Transaction, own: impl Fn(UnitId) -> bool) -> WriteSet<'_> {
        let segments = self.session.journal.segments_since(t, own);
        WriteSet {
            scope: self.scope.writes(|pick| {
                (segments.iter())
                    .map(|(at, end)| (pick(at.scope()), end.map(|end| pick(end.scope()))))
                    .collect()
            }),
            tables: self.tables.writes(|pick| {
                (segments.iter())
                    .map(|(at, end)| (pick(at.tables()), end.map(|end| pick(end.tables()))))
                    .collect()
            }),
        }
    }

    /// Ends a unit's transaction: what it did stays.
    fn commit(&mut self, t: Transaction) {
        self.with_journal(|journal, logs| journal.commit(t, logs));
    }

    /// What a unit's load is compared against.
    fn snapshot(&self) -> Before {
        Before {
            defs: self.kernel.env.defs().len(),
            datas: self.kernel.env.datas().len(),
            tables: self.tables.mark(self.ids()),
            nav: self.present.nav.as_ref().map(|nav| {
                let nav = nav.borrow();
                (
                    nav.locals.len(),
                    nav.binders.len(),
                    nav.outline.len(),
                    nav.params.len(),
                    nav.named.len(),
                )
            }),
        }
    }

    /// After library file `f` loaded: writes its entry, if it checked and
    /// can be cached.
    pub(crate) fn cache_after(
        &mut self,
        f: usize,
        capture: LibraryCapture,
        ok: bool,
        unit: &str,
        key: &Key,
    ) {
        let log = self.scope.log.take().unwrap_or_default();
        // A cancelled check isn't a result, even where it reported nothing.
        if ok && !self.kernel.machine.budget.cancelled() {
            let store = self.options.check_cache.clone().expect("a cache is set");
            let entry = self.encode_library_file(f, &capture, &log, key, store.salt());
            match entry {
                Ok(entry) => {
                    store.write(unit, key, &entry);
                    self.session.cache_stats.written += 1;
                }
                Err(why) => {
                    debug(&format!("std file {f} can't be cached: {why}"));
                    self.session.cache_stats.uncacheable += 1;
                }
            }
        }
        self.commit(capture.transaction);
    }
}

// ---- Project namespaces (stage 2) ------------------------------------------

impl Elaborator {
    /// Says what each project namespace's sources are, for the keys of
    /// their entries: for each namespace, a hash the host makes of its
    /// name, its files' names and text, the project's namespaces and its
    /// configuration (§4.2 items 3 and 5). A namespace without one isn't
    /// cached.
    pub fn set_namespace_sources(&mut self, sources: HashMap<String, Key>) {
        self.session.namespace_sources = std::sync::Arc::new(sources);
    }

    /// For a plain `check` that may leave out namespaces nothing it checks
    /// needs (SW-1193): whether project namespace `ns`, with the namespaces
    /// `closure` before it, has an entry that its replay would accept as far
    /// as can be told without loading anything, and if so the warnings
    /// replaying it would report (doc links aside: they are never cached).
    /// Records `ns`'s key either way, for the namespaces after it. Runs the
    /// checks the replay runs before it changes anything: the entry's seal
    /// and key, its files and library files exist, and the files it
    /// included are as they were.
    pub fn plan_namespace(&mut self, ns: &str, closure: &[String]) -> Option<Vec<Diagnostic>> {
        let (unit, key) = self.namespace_cache_key(Some(ns), Some(closure))?;
        self.session.namespace_keys.insert(ns.to_string(), key);
        if self.options.fail_replays_late
            || stitchwort_core::registry::check_complete_core(&self.ev()).is_err()
        {
            return None;
        }
        let store = self.options.check_cache.clone()?;
        let bytes = store.read(&unit, &key)?;
        let why = match self.plan_entry(&bytes, &key, store.salt()) {
            Ok(warnings) => return Some(warnings),
            Err(Bad(why)) => why,
        };
        debug(&format!("{ns}: not skipped: {why}"));
        None
    }

    fn plan_entry(&self, bytes: &[u8], key: &Key, salt: [u8; 16]) -> Read<Vec<Diagnostic>> {
        let (_, body) = open(bytes, key, salt)?;
        let file_ids: HashMap<String, FileId> = self
            .namespace_file_names()
            .into_iter()
            .map(|(id, name)| (name, id))
            .collect();
        let head = self.read_head(body, &file_ids)?;
        self.includes_unchanged(&head.pre)?;
        self.library_unchanged(&head.pre)?;
        let mut warnings = head.pre.warnings;
        warnings.retain(|d| d.code != crate::doc_links::CODE);
        Ok(warnings)
    }

    /// Whether the library files a namespace's entry says it loaded have
    /// the keys they had: the text of each, and of every file it needs.
    fn library_unchanged(&self, pre: &Pre) -> Read<()> {
        let roots: BTreeSet<usize> = pre.library.iter().map(|&(f, _)| f).collect();
        let keys = self.library_keys(&roots);
        let index = self.library_index().expect("a library is installed");
        for &(f, key) in &pre.library {
            if keys[&f] != key {
                return bad(format!(
                    "the library file `{}` changed",
                    index.files[f].path
                ));
            }
        }
        Ok(())
    }

    /// Whether the files a namespace's entry says it included are as they
    /// were.
    fn includes_unchanged(&self, pre: &Pre) -> Read<()> {
        for (path, hash) in &pre.includes {
            let same = self
                .session
                .include_files
                .as_ref()
                .and_then(|files| files.read(path).ok())
                .is_some_and(|text| blake3::hash(text.as_bytes()).as_bytes() == hash);
            if !same {
                return bad(format!("the included `{path}` changed"));
            }
        }
        Ok(())
    }

    /// Counts namespace `ns` as one a plain `check` reported from its entry
    /// without loading it ([`Self::plan_namespace`]).
    pub fn count_skipped_namespace(&mut self, ns: &str) {
        debug(&format!("{ns}: reported from its entry, not loaded"));
        self.session.cache_stats.namespace_skipped += 1;
    }

    /// Says, under `STITCHWORT_CACHE_DEBUG`, that a plain `check` that
    /// left namespaces out is checking everything again, loading them.
    pub fn note_skipping_undone(&self) {
        debug("a namespace after one left out has an error or a goal: loading everything");
    }

    /// Whether this elaborator keeps results in a check cache.
    pub fn uses_check_cache(&self) -> bool {
        self.cache_usable()
    }

    /// What every unit's elaboration reads of the library whether or not it
    /// loads any file: the core's text (always loaded) and the index of
    /// names (path, key, kind and flags of each), which resolution, imports,
    /// ambiguity and dot notation read. A new or removed name can make a
    /// short name ambiguous, or an unqualified one resolve elsewhere, in a
    /// unit that never mentions it; so it is part of every key. A change
    /// to a file's text that leaves its names alone is not: that reaches
    /// only the units that load the file (their keys cover the text of the
    /// files they need, [`Self::library_keys`]). Computed once.
    fn library_interface(&self) -> Key {
        *self.session.library_interface_digest.get_or_init(|| {
            let mut h = blake3::Hasher::new();
            let mut part = |bytes: &[u8]| {
                h.update(&(bytes.len() as u64).to_le_bytes());
                h.update(bytes);
            };
            if let Some(index) = self.library_index() {
                part(index.files[0].text.as_bytes());
                for file in &index.files {
                    part(file.path.as_bytes());
                    for n in &file.names {
                        part(n.key.as_bytes());
                        part(&[
                            n.kind as u8,
                            u8::from(n.follower),
                            u8::from(n.function),
                            u8::from(n.candidate),
                        ]);
                    }
                }
            }
            *h.finalize().as_bytes()
        })
    }

    /// The library files that `needs` names, as the roots of the files a
    /// unit loads: every file it names, every target of each of its dot
    /// calls (whether or not the dot call's type will have loaded it), and
    /// the file of each definition whose equations it names. The core is
    /// part of every key already.
    fn needed_roots(&self, needs: &Needs) -> BTreeSet<usize> {
        let index = self.library_index().expect("a library is installed");
        let mut roots = needs.files.clone();
        for field in &needs.dots {
            roots.extend(index.dot_targets(field).iter().map(|t| t.file));
        }
        roots.extend(needs.equations.iter().filter_map(|k| index.owner(k)));
        roots.remove(&0);
        roots
    }

    /// The unit and key of project namespace `namespace`, about to be
    /// elaborated with the namespaces `closure` before it, if it may come
    /// from the cache: every namespace it depends on has a key.
    pub(crate) fn namespace_cache_key(
        &self,
        namespace: Option<&str>,
        closure: Option<&[String]>,
    ) -> Option<(String, Key)> {
        if !self.cache_usable() || self.unit.loading_prelude || !self.library_stack_is_empty() {
            return None;
        }
        let (Some(ns), Some(closure)) = (namespace, closure) else {
            return None;
        };
        // An entry says every theorem was checked.
        if self.options.skip_theorems.contains_key(ns) {
            return None;
        }
        let source = self.session.namespace_sources.get(ns)?;
        let store = self.options.check_cache.as_ref()?;
        let library = self.library_interface();
        let mut h = blake3::Hasher::new();
        let mut part = |bytes: &[u8]| {
            h.update(&(bytes.len() as u64).to_le_bytes());
            h.update(bytes);
        };
        part(b"stitchwort check cache: namespace");
        part(&FORMAT.to_le_bytes());
        part(store.compiler().as_bytes());
        part(self.modes().as_bytes());
        part(&library);
        part(ns.as_bytes());
        part(source);
        for dependency in closure {
            part(dependency.as_bytes());
            part(self.session.namespace_keys.get(dependency)?);
        }
        let nav = self.nav_tag();
        Some((format!("ns.{ns}{nav}"), *h.finalize().as_bytes()))
    }

    /// Elaborates project namespace `ns`, or loads it from its entry for
    /// `key`, and writes the entry if it was elaborated without errors. Its
    /// diagnostics, and whether it came from the cache.
    pub(crate) fn elaborate_namespace_cached(
        &mut self,
        ns: &str,
        files: &[SourceUnit],
        closure: &[String],
        unit: &str,
        key: &Key,
    ) -> (Vec<Diagnostic>, bool) {
        self.session.namespace_keys.insert(ns.to_string(), *key);
        let store = self.options.check_cache.clone().expect("a cache is set");
        // Before the replay, so that if it fails part way, the namespace's
        // write-set holds what it did as well as what elaborating does.
        let transaction = self.with_journal(|journal, logs| journal.begin(logs));
        // A namespace with the probed position in it is checked, not
        // replayed: only checking notes the context.
        if !self.probes_one_of(files)
            && stitchwort_core::registry::check_complete_core(&self.ev()).is_ok()
            && let Some(bytes) = store.read(unit, key)
        {
            match self.replay_namespace(ns, files, closure, &bytes, key, store.salt()) {
                Ok(mut warnings) => {
                    self.session.replayed_names.clear();
                    self.session.cache_stats.namespace_hits += 1;
                    // Doc links aren't cached: they may point into other
                    // namespaces, which can change without this one's key
                    // changing (SW-1045). Entries written before that held
                    // them, so they are dropped here too.
                    warnings.retain(|d| d.code != crate::doc_links::CODE);
                    warnings.extend(self.doc_link_warnings(files));
                    self.commit(transaction);
                    return (warnings, true);
                }
                Err(Miss::Early(why)) => debug(&format!("{ns}: a miss: {why}")),
                Err(Miss::Late(why)) => {
                    debug(&format!("{ns}: a miss after the replay began: {why}"));
                    self.session.cache_stats.late_misses += 1;
                    // Its files were walked already.
                    self.unit.skip_navigation_walk = true;
                }
            }
        }
        self.session.cache_stats.namespace_misses += 1;
        self.unit.include_trace.borrow_mut().clear();
        self.unit.namespace_capture = Some(Capture {
            transaction,
            unit: self.session.owners.current(),
            early: None,
            needs: None,
            before: None,
            library_loaded: 0,
            segments: 0,
        });
        let unfinished = self.tables.unfinished_count();
        let diagnostics = self.elaborate_namespace_untimed(Some(ns), files, Some(closure));
        let capture = self
            .unit
            .namespace_capture
            .take()
            .expect("the namespace's capture is there until it ends");
        self.unit.skip_navigation_walk = false;
        if diagnostics.iter().any(|d| d.severity == Severity::Error) {
            self.session.failed_namespaces.insert(ns.to_string(), ());
        }
        // A namespace with open goals is unfinished, like one with errors:
        // checked again each time, so its goals are always fresh. So is one
        // with a declaration that uses an unfinished one (which reports
        // nothing), even with no goal of its own.
        let ok = !diagnostics
            .iter()
            .any(|d| matches!(d.severity, Severity::Error | Severity::Goal))
            && self.tables.unfinished_count() == unfinished
            && !self.kernel.machine.budget.cancelled();
        // An importer of a namespace that failed is checked, but its entry
        // would be keyed to the broken source: storing it would delete the
        // healthy entry, which is the one the fixed source finds again.
        let broken_dependency = closure.iter().find(|dependency| {
            self.session
                .failed_namespaces
                .contains_key(dependency.as_str())
        });
        if ok && let Some(dependency) = broken_dependency {
            debug(&format!(
                "{ns} can't be cached: it uses {dependency}, which has an error"
            ));
            self.session.cache_stats.namespace_waiting_on_error += 1;
        } else if ok {
            let cached: Vec<Diagnostic> = (diagnostics.iter())
                .filter(|d| d.code != crate::doc_links::CODE)
                .cloned()
                .collect();
            match self.encode_namespace(ns, files, &capture, &cached, key, store.salt()) {
                Ok(entry) => {
                    store.write(unit, key, &entry);
                    self.session.cache_stats.namespace_written += 1;
                }
                Err(why) => {
                    debug(&format!("{ns} can't be cached: {why}"));
                    self.session.cache_stats.namespace_uncacheable += 1;
                }
            }
        }
        self.commit(capture.transaction);
        (diagnostics, false)
    }

    /// While a namespace that may be cached is elaborated: the names it has
    /// collected, before its library files load, and what it needs.
    pub(crate) fn capture_before_needs(&mut self, needs: &Needs) {
        if self.unit.loading_prelude {
            return;
        }
        let Some(c) = &self.unit.namespace_capture else {
            return;
        };
        if c.early.is_some() {
            return;
        }
        // The names new in its write-set so far.
        let early: Vec<String> = (self.write_set(&c.transaction, |u| u == c.unit))
            .scope
            .entries
            .into_iter()
            .filter(|(k, old)| old.is_none() && self.scope.has(k))
            .map(|(k, _)| k.clone())
            .collect();
        let c = self.unit.namespace_capture.as_mut().expect("checked above");
        c.early = Some(early);
        c.needs = Some(needs.clone());
    }

    /// Then, once its library files have loaded: what its entry is worked
    /// out against.
    pub(crate) fn capture_after_needs(&mut self) {
        if self.unit.loading_prelude
            || self
                .unit
                .namespace_capture
                .as_ref()
                .is_none_or(|c| c.before.is_some())
        {
            return;
        }
        let before = self.snapshot();
        let loaded = self.loaded_library_files().len();
        let segments = self.session.journal.segments();
        let c = self.unit.namespace_capture.as_mut().expect("checked above");
        c.before = Some(before);
        c.library_loaded = loaded;
        c.segments = segments;
    }

    /// The names entries give the files a namespace's entry may refer to:
    /// the library's and the project's.
    fn namespace_file_names(&self) -> HashMap<FileId, String> {
        let mut names = self.std_file_names();
        for (id, path) in self.session.include_locations.iter() {
            names.insert(*id, project_file_name(path));
        }
        names
    }

    /// The entry for the namespace just elaborated without errors from
    /// `files`, or why it can't be cached (see [`Self::encode`]).
    fn encode_namespace(
        &self,
        ns: &str,
        files: &[SourceUnit],
        capture: &Capture,
        warnings: &[Diagnostic],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let (Some(before), Some(early), Some(needs)) =
            (&capture.before, &capture.early, &capture.needs)
        else {
            return Err("checking stopped early".to_string());
        };
        if self.loaded_library_files().len() != capture.library_loaded {
            return Err("a library file loaded part way through".to_string());
        }
        // Nor anything else nested (equations made on demand): its
        // declarations would be the entry's, and its names not.
        if (self.session.journal.units_from(capture.segments)).any(|u| u != capture.unit) {
            return Err("a nested unit ran part way through".to_string());
        }
        let writes = self.write_set(&capture.transaction, |u| u == capture.unit);
        // The names: each new one is added after those of its short name
        // that were added before it (the followers' order).
        let early_keys: HashSet<&str> = early.iter().map(String::as_str).collect();
        let mut changed = Vec::new();
        let mut late = Vec::new();
        for &(k, old) in &writes.scope.entries {
            if early_keys.contains(k.as_str()) {
                continue;
            }
            match (old, self.scope.stored(k)) {
                (None, Some(_)) => late.push(k.clone()),
                // Declared and withdrawn.
                (None, None) => {}
                (Some(old), Some(now)) if now == old => {}
                (Some(_), Some(_)) => changed.push(k.clone()),
                (Some(_), None) => return Err(format!("`{k}` was removed")),
            }
        }
        changed.sort();
        let order = |k: &String| (self.scope.follower_position(k).unwrap_or(0), k.clone());
        let with_follower = |keys: Vec<String>| -> Vec<(String, bool)> {
            keys.into_iter()
                .map(|k| {
                    let follower = self.scope.follower_position(&k).is_some();
                    (k, follower)
                })
                .collect()
        };
        let mut early = early.clone();
        early.sort_by_key(order);
        late.sort_by_key(order);
        // The members it marked: not those of the library files loaded
        // inside it, which are theirs.
        let mut members: Vec<String> = (writes.scope.members.iter())
            .filter(|(k, old)| old.is_none() && self.scope.is_member(k))
            .map(|(k, _)| (*k).clone())
            .collect();
        members.sort();
        let names = NamesOut {
            changed,
            early: with_follower(early),
            late: with_follower(late),
            members,
        };
        let index = self.library_index().expect("a library is installed");
        let pre = PreOut {
            needs_files: needs
                .files
                .iter()
                .map(|&f| index.files[f].path.clone())
                .collect(),
            dots: needs.dots.iter().cloned().collect(),
            equations: needs.equations.iter().cloned().collect(),
            library: {
                // And the files of the namespaces it depends on: `auto`'s
                // candidates come from the module's reach, theirs included
                // (their entries' keys don't change when such a file does).
                let mut roots = self.needed_roots(needs);
                if let Some(reach) = self.session.library_reach.get(ns) {
                    roots.extend(reach.iter().copied().filter(|&f| f != 0));
                }
                let keys = self.library_keys(&roots);
                roots
                    .iter()
                    .map(|&f| (index.files[f].path.clone(), keys[&f]))
                    .collect()
            },
            includes: self.unit.include_trace.borrow().clone(),
        };
        let unit = UnitOut {
            file_names: self.namespace_file_names(),
            own_files: files.iter().filter_map(|f| f.file).collect(),
            library: false,
        };
        if unit.own_files.len() != files.len() {
            return Err("a file without an id".to_string());
        }
        self.encode(&unit, before, &writes, &names, &pre, warnings, key, salt)
    }

    /// Loads project namespace `ns`, whose files are `files`, from its
    /// entry: its warnings. Replay does what elaborating it does, in the
    /// same order: the syntax is walked for navigation, the names are
    /// declared, the library files it needs load, then its declarations go
    /// to the kernel and its tables are filled in. A problem found before
    /// that begins is an early miss, after which nothing has changed; one
    /// found after it a late one.
    fn replay_namespace(
        &mut self,
        ns: &str,
        files: &[SourceUnit],
        closure: &[String],
        bytes: &[u8],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<Diagnostic>, Miss> {
        let early = |Bad(why)| Miss::Early(why);
        let late = |Bad(why)| Miss::Late(why);
        let (deps, body) = open(bytes, key, salt).map_err(early)?;
        let file_ids: HashMap<String, FileId> = self
            .namespace_file_names()
            .into_iter()
            .map(|(id, name)| (name, id))
            .collect();
        let mut head = self.read_head(body, &file_ids).map_err(early)?;
        self.includes_unchanged(&head.pre).map_err(early)?;
        self.library_unchanged(&head.pre).map_err(early)?;

        // From here on, as `elaborate_namespace_untimed` does.
        self.unit.namespace_root = format!("{ns}.");
        self.unit.module_path = "".into();
        self.unit.module = crate::module::ModuleState {
            files: files
                .iter()
                .map(|f| crate::module::FileInfo {
                    id: f.file,
                    name: f.name.to_string(),
                })
                .collect(),
            namespace: Some(ns.to_string()),
            closure: Some(closure.to_vec()),
            first_def: self.kernel.env.defs().len(),
            first_test: self.tables.tests.len(),
            ..crate::module::ModuleState::default()
        };
        self.scope.clear_imports();
        self.walk_for_navigation(&files.iter().map(|f| f.module).collect::<Vec<_>>());
        let mut pre = std::mem::take(&mut head.pre);
        // For the namespaces that depend on it.
        self.set_library_reach(&pre.needs);
        for (k, span, follower) in &pre.early {
            self.scope.insert(k, Global::Failed, *span, *follower);
        }
        // If replay fails from here on, elaborating the namespace declares
        // these again where they are (`taken`).
        self.session.replayed_names = pre.early.iter().map(|(k, _, _)| k.clone()).collect();
        if !pre.needs.files.is_empty()
            || !pre.needs.dots.is_empty()
            || !pre.needs.equations.is_empty()
        {
            self.load_needs(&pre.needs).map_err(|ds| {
                Miss::Late(format!(
                    "its library files don't load: {}",
                    ds.first().map_or("", |d| d.message.as_str())
                ))
            })?;
        }
        if self.options.fail_replays_late {
            return Err(Miss::Late("a test made it fail".to_string()));
        }
        let d = self.decode(&deps, head, &pre.early).map_err(late)?;
        let warnings = std::mem::take(&mut pre.warnings);
        let base_defs = self.kernel.env.defs().len();
        self.admit_replayed(&d.defs, &d.datas, &d.bound, &d.rest.tables, false)
            .map_err(late)?;
        self.replay_tables(d.rest, &pre.early);
        self.tables
            .namespace_defs
            .insert(ns.to_string(), base_defs..self.kernel.env.defs().len());
        Ok(warnings)
    }
}

// ---- Writing --------------------------------------------------------------

/// How an entry refers to declarations and files while it is written.
struct Out<'g> {
    g: &'g Ev<'g>,
    base_defs: usize,
    base_datas: usize,
    /// Declarations outside the entry, by their place in `deps`.
    ext_defs: HashMap<DefId, usize>,
    ext_datas: HashMap<DataId, usize>,
    /// What the entry depends on: kind (0 a definition, 1 a data type),
    /// full path, and content hash.
    deps: Vec<Dep>,
    /// How many final definitions and data types have each path: only a
    /// path that names one declaration can be a reference.
    paths: std::cell::Ref<'g, crate::state::paths::DeclPaths>,
    /// The files a span may be in, by id, with their names in an entry
    /// (`file_names`); the ones used so far, in the entry's file table.
    names: HashMap<FileId, String>,
    files: Vec<String>,
    file_ids: HashMap<FileId, usize>,
    /// Why this can't be cached, once something can't be written.
    problem: Option<String>,
}

impl Out<'_> {
    fn fail(&mut self, why: String) {
        if self.problem.is_none() {
            self.problem = Some(why);
        }
    }
}

impl Refs for Out<'_> {
    fn def(&mut self, w: &mut Writer, id: DefId) {
        if id.0 >= self.base_defs {
            w.uint(((id.0 - self.base_defs) as u64) << 1);
            return;
        }
        if let Some(&i) = self.ext_defs.get(&id) {
            w.uint(((i as u64) << 1) | 1);
            return;
        }
        let def = self.g.def(id);
        let hash = match def_hash(self.g, id) {
            Ok(Some(hash)) => hash,
            _ => {
                self.fail(format!("`{}` has no content hash", def.path()));
                ContentHash([0; 32])
            }
        };
        if self.paths.unique_def(def.path()).is_none() {
            self.fail(format!("`{}` names more than one definition", def.path()));
        }
        let i = self.deps.len();
        self.deps.push((0, def.path().to_string(), hash));
        self.ext_defs.insert(id, i);
        w.uint(((i as u64) << 1) | 1);
    }

    fn data(&mut self, w: &mut Writer, id: DataId) {
        if id.0 >= self.base_datas {
            w.uint(((id.0 - self.base_datas) as u64) << 1);
            return;
        }
        if let Some(&i) = self.ext_datas.get(&id) {
            w.uint(((i as u64) << 1) | 1);
            return;
        }
        let data = self.g.data(id);
        let hash = match data_hash(self.g, id) {
            Ok(Some(hash)) => hash,
            _ => {
                self.fail(format!("`{}` has no content hash", data.path()));
                ContentHash([0; 32])
            }
        };
        if self.paths.unique_data(data.path()).is_none() {
            self.fail(format!("`{}` names more than one data type", data.path()));
        }
        let i = self.deps.len();
        self.deps.push((1, data.path().to_string(), hash));
        self.ext_datas.insert(id, i);
        w.uint(((i as u64) << 1) | 1);
    }

    fn span(&mut self, w: &mut Writer, span: Span) {
        let file = self.file_index(span);
        w.usize(file);
        w.uint(u64::from(span.start));
        w.uint(u64::from(span.end.saturating_sub(span.start)));
    }

    fn span_after(&mut self, w: &mut Writer, span: Span, prev: &mut u32) {
        let file = self.file_index(span);
        w.usize(file);
        w.uint(codec::zigzag(i64::from(span.start) - i64::from(*prev)));
        w.uint(u64::from(span.end.saturating_sub(span.start)));
        *prev = span.start;
    }
}

impl Out<'_> {
    /// The number `span`'s file has in the entry's list of files.
    fn file_index(&mut self, span: Span) -> usize {
        let file = match self.file_ids.get(&span.file) {
            Some(&i) => i,
            None => match self.names.get(&span.file) {
                Some(name) => {
                    self.files.push(name.clone());
                    self.file_ids.insert(span.file, self.files.len() - 1);
                    self.files.len() - 1
                }
                None => {
                    self.fail("a span outside the files an entry can name".to_string());
                    0
                }
            },
        };
        if span.end < span.start {
            self.fail("a span that ends before it starts".to_string());
        }
        file
    }
}

/// An entry's parts while it is written: the terms and strings, and the
/// rest.
pub(crate) struct Encoding<'g> {
    out: Out<'g>,
    terms: TermWriter,
    w: Writer,
}

impl Encoding<'_> {
    /// How many rows follow.
    pub(crate) fn count(&mut self, n: usize) {
        self.w.usize(n);
    }

    /// A declaration's content hash, if it has one.
    fn hash(&mut self, hash: stitchwort_core::budget::Result<Option<ContentHash>>) {
        match hash {
            Ok(Some(h)) => {
                self.w.bool(true);
                self.w.raw(&h.0);
            }
            _ => self.w.bool(false),
        }
    }

    pub(crate) fn str(&mut self, s: &str) {
        let i = self.terms.string(s);
        self.w.uint(u64::from(i));
    }

    pub(crate) fn term(&mut self, t: &Term) {
        match self.terms.term(&mut self.out, t) {
            Ok(id) => self.w.uint(u64::from(id)),
            Err(_) => self.out.fail("a term with a metavariable".to_string()),
        }
    }

    /// A test's probe (D601).
    pub(crate) fn probe(&mut self, p: &crate::Probe) {
        self.span(p.span);
        match &p.truth {
            None => self.w.bool(false),
            Some(t) => {
                self.w.bool(true);
                self.term(t);
            }
        }
        self.w.bool(p.whole);
        match &p.kind {
            crate::ProbeKind::Other => self.w.u8(0),
            crate::ProbeKind::Compare { op, left, right } => {
                self.w.u8(1);
                self.str(op);
                self.term(left);
                self.term(right);
            }
            crate::ProbeKind::And(a, b) => {
                self.w.u8(2);
                self.probe(a);
                self.probe(b);
            }
        }
    }

    pub(crate) fn def(&mut self, id: DefId) {
        self.out.def(&mut self.w, id);
    }

    pub(crate) fn data(&mut self, id: DataId) {
        self.out.data(&mut self.w, id);
    }

    pub(crate) fn span(&mut self, span: Span) {
        self.out.span(&mut self.w, span);
    }

    fn span_after(&mut self, span: Span, prev: &mut u32) {
        self.out.span_after(&mut self.w, span, prev);
    }

    fn global(&mut self, e: &Elaborator, global: Global) {
        match global {
            Global::Def(id) => {
                self.w.u8(0);
                self.def(id);
            }
            Global::Data(d) => {
                self.w.u8(1);
                self.data(d);
            }
            Global::Ctor(d, c) => {
                self.w.u8(2);
                self.data(d);
                self.w.usize(c);
            }
            Global::Ability(i) => {
                self.w.u8(3);
                self.data(e.tables.abilities[i].op_data);
            }
            Global::Op(i, j) => {
                self.w.u8(4);
                self.data(e.tables.abilities[i].op_data);
                self.w.usize(j);
            }
            Global::Pending(f, kind) => {
                self.w.u8(5);
                self.w.usize(f);
                self.w.u8(pending_tag(kind));
            }
            Global::Unchecked(_) | Global::Failed => {
                self.out.fail("a name that failed".to_string());
                self.w.u8(6);
            }
        }
    }
}

/// The built-ins bound to definitions from `defs` on and data types from
/// `datas` on: kind (0 a definition, 1 a data type), the declaration's
/// place after those, and the built-in. A data type's constructors are
/// bound with it.
fn bound_builtins(g: &Ev, defs: usize, datas: usize) -> Vec<(u8, usize, Builtin)> {
    let missing = g.env.registry().missing();
    let mut out: Vec<(u8, usize, Builtin)> = Builtin::ALL
        .iter()
        .copied()
        .filter(|b| !missing.contains(b))
        .filter_map(|b| match b.kind() {
            Kind::Def => g
                .env
                .registry()
                .def(b)
                .filter(|id| id.0 >= defs)
                .map(|id| (0, id.0 - defs, b)),
            Kind::Data => g
                .env
                .registry()
                .data(b)
                .filter(|d| d.0 >= datas)
                .map(|d| (1, d.0 - datas, b)),
            Kind::Ctor(_) => None,
        })
        .collect();
    out.sort();
    out
}

/// The built-in definition (kind 0) or data type (kind 1) named `name`.
fn builtin_named(kind: u8, name: &str) -> Option<Builtin> {
    Builtin::ALL.iter().copied().find(|b| {
        b.name() == name
            && match kind {
                0 => b.kind() == Kind::Def,
                1 => b.kind() == Kind::Data,
                _ => false,
            }
    })
}

fn pending_tag(kind: PendingKind) -> u8 {
    match kind {
        PendingKind::Def => 0,
        PendingKind::Data => 1,
        PendingKind::Ctor => 2,
        PendingKind::Op => 3,
        PendingKind::Other => 4,
    }
}

fn pending_kind(tag: u8) -> Read<PendingKind> {
    Ok(match tag {
        0 => PendingKind::Def,
        1 => PendingKind::Data,
        2 => PendingKind::Ctor,
        3 => PendingKind::Op,
        4 => PendingKind::Other,
        _ => return bad("an unknown kind of pending name"),
    })
}

/// The unit an entry is written for.
struct UnitOut {
    /// The files a span may be in, by their names in entries.
    file_names: HashMap<FileId, String>,
    /// The unit's own files: what navigation recorded in them is the
    /// unit's.
    own_files: HashSet<FileId>,
    /// A library file (whose navigation entry holds what the walk over its
    /// syntax found) rather than a project namespace (whose syntax is
    /// walked again when it is replayed).
    library: bool,
}

/// The names a unit declared: those that existed and changed; those new
/// before its library files loaded (a namespace's, with whether each is a
/// follower) and after, each in the order they were added; and the
/// members marked.
#[derive(Default)]
struct NamesOut {
    changed: Vec<String>,
    early: Vec<(String, bool)>,
    late: Vec<(String, bool)>,
    members: Vec<String>,
}

/// What a namespace's replay needs before it reads the rest: the library
/// files it needs (by path) and the fields of its dot calls, the files it
/// `include`d with a hash of their text, and the names it declares before
/// its library files load.
#[derive(Default)]
struct PreOut {
    needs_files: Vec<String>,
    dots: Vec<String>,
    equations: Vec<String>,
    /// The library files the namespace loads (roots, by path) with the key
    /// each had: replay checks them before it changes anything.
    library: Vec<(String, Key)>,
    includes: Vec<(String, Key)>,
}

/// The name an entry gives the file at index `i` of the library index.
fn std_file_name(path: &str) -> String {
    format!("std:{path}")
}

/// The name an entry gives a project's file at `path` in it.
fn project_file_name(path: &str) -> String {
    format!("project:{path}")
}

/// The operators a test's comparison can have (`ProbeKind::Compare::op`).
const TEST_OPS: [&str; 7] = ["==", "!=", "=", "<", "<=", ">", ">="];

/// A diagnostic's code, as the `'static` text `Diagnostic` holds: the
/// codes read from entries are kept once each.
fn static_code(code: &str) -> &'static str {
    use std::sync::{Mutex, OnceLock};
    static CODES: OnceLock<Mutex<HashSet<&'static str>>> = OnceLock::new();
    let mut codes = CODES
        .get_or_init(|| Mutex::new(HashSet::default()))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(&c) = codes.get(code) {
        return c;
    }
    let c: &'static str = Box::leak(code.to_string().into_boxed_str());
    codes.insert(c);
    c
}

/// The first line where `a` and `b` differ, both ways, for a message.
fn first_line_differing(a: &str, b: &str) -> String {
    let (mut la, mut lb) = (a.lines(), b.lines());
    loop {
        match (la.next(), lb.next()) {
            (Some(x), Some(y)) if x == y => continue,
            (None, None) => return "no line differs".to_string(),
            (x, y) => {
                return format!(
                    "at the mark `{}`, after the undo `{}`",
                    x.unwrap_or("(end)"),
                    y.unwrap_or("(end)")
                );
            }
        }
    }
}

/// With `STITCHWORT_CACHE_DEBUG` set, says why an entry wasn't used or
/// written, on stderr.
fn debug(what: &str) {
    if std::env::var_os("STITCHWORT_CACHE_DEBUG").is_some() {
        eprintln!("check cache: {what}");
    }
}

impl Elaborator {
    /// The names entries give the files a library entry may refer to.
    fn std_file_names(&self) -> HashMap<FileId, String> {
        let index = self.library_index().expect("a library is installed");
        index
            .files
            .iter()
            .map(|f| (f.id, std_file_name(&f.path)))
            .collect()
    }

    /// The entry for library file `f`, which has just loaded without
    /// errors, or why it can't be cached (see [`Self::encode`]).
    fn encode_library_file(
        &self,
        f: usize,
        capture: &LibraryCapture,
        log: &[ScopeOp],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let index = self.library_index().expect("a library is installed");
        let writes = self.write_set(&capture.transaction, |u| u > capture.after);
        // The names: those that changed, then the new ones in the order
        // they were declared, then the members marked. (The journal's log
        // doesn't keep that order: `ScopeOp`.)
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
            file_names: self.std_file_names(),
            own_files: HashSet::from_iter([index.files[f].id]),
            library: true,
        };
        let before = &capture.before;
        self.encode(
            &unit,
            before,
            &writes,
            &names,
            &PreOut::default(),
            &[],
            key,
            salt,
        )
    }

    /// The entry for a unit that has just loaded without errors, or why it
    /// can't be cached: a declaration the kernel didn't admit, a primitive
    /// or core built-in bound, an export made, a library test kept, a name
    /// that failed, or a reference that can't be written by path. Library
    /// built-ins are encoded.
    #[allow(clippy::too_many_arguments)]
    fn encode(
        &self,
        unit: &UnitOut,
        before: &Before,
        writes: &WriteSet<'_>,
        names: &NamesOut,
        pre: &PreOut,
        warnings: &[Diagnostic],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let g = &self.ev();
        let _op = g.machine.budget.operation(self.options.limits);
        let (defs, datas) = (
            before.defs..g.env.defs().len(),
            before.datas..g.env.datas().len(),
        );
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            if def.state() != State::Final || def.body().is_none() {
                return Err(format!("`{}` isn't admitted with a body", def.path()));
            }
            if def.export() || !def.validators().is_empty() {
                return Err(format!("`{}` is exported", def.path()));
            }
            if g.env.builtins().primitive(id).is_some() {
                return Err(format!("`{}` is a primitive", def.path()));
            }
            // Replay declares it again under its module.
            module_of(def.name(), def.path()).map_err(|Bad(why)| why)?;
        }
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            if data.state() != State::Final || !data.validators().is_empty() {
                return Err(format!("`{}` isn't admitted plainly", data.path()));
            }
            module_of(data.name(), data.path()).map_err(|Bad(why)| why)?;
        }
        // The built-ins the file binds: only library ones, which are just
        // registry entries (a core built-in may also tell the evaluator
        // about a native, which replay couldn't take back).
        let bound = bound_builtins(g, before.defs, before.datas);
        for &(_, _, b) in &bound {
            if b.home() != Home::Library || Native::ALL.iter().any(|n| n.builtin() == b) {
                return Err(format!("`{}` is a core built-in", b.name()));
            }
        }
        let tests = self.tables.tests.since(before.tables.tests());
        if tests.iter().any(|t| t.library) || (unit.library && !tests.is_empty()) {
            return Err("a library test was kept".to_string());
        }

        self.session.paths.borrow_mut().sync(g.env);
        let paths = self.session.paths.borrow();
        // Each `unfolding` entry is written as a reference term. The term
        // writer knows a term by its address, so these live as long as the
        // encoding: a temporary would share its address with the next.
        let unfolding_refs: Vec<Box<[Term]>> = g.env.defs()[before.defs..]
            .iter()
            .map(|def| def.unfolding().iter().map(|&id| Term::Def(id)).collect())
            .collect();
        let mut e = Encoding {
            out: Out {
                g,
                base_defs: before.defs,
                base_datas: before.datas,
                ext_defs: HashMap::default(),
                ext_datas: HashMap::default(),
                deps: Vec::new(),
                paths,
                names: unit.file_names.clone(),
                files: Vec::new(),
                file_ids: HashMap::default(),
                problem: None,
            },
            terms: TermWriter::default(),
            w: Writer::default(),
        };

        // What a namespace's replay reads before the rest (empty for a
        // library file): the library it needs, the files it included, and
        // the names it declared before the library files loaded.
        e.w.usize(pre.needs_files.len());
        for path in &pre.needs_files {
            e.str(path);
        }
        e.w.usize(pre.dots.len());
        for field in &pre.dots {
            e.str(field);
        }
        e.w.usize(pre.equations.len());
        for key in &pre.equations {
            e.str(key);
        }
        e.w.usize(pre.library.len());
        for (path, key) in &pre.library {
            e.str(path);
            e.w.raw(key);
        }
        e.w.usize(pre.includes.len());
        for (path, hash) in &pre.includes {
            e.str(path);
            e.w.raw(hash);
        }
        e.w.usize(names.early.len());
        for (k, follower) in &names.early {
            let Some((_, span)) = self.scope.stored(k) else {
                return Err(format!("`{k}` was declared and is gone"));
            };
            e.str(k);
            e.span(*span);
            e.w.bool(*follower);
        }
        // The warnings, in the order they are reported: here, so that a
        // plain `check` can report a namespace it doesn't load from its
        // head alone (SW-1193).
        e.w.usize(warnings.len());
        for d in warnings {
            if d.severity != Severity::Warning {
                return Err("an error".to_string());
            }
            e.str(d.code);
            e.str(&d.message);
            e.w.usize(d.labels.len());
            for label in &d.labels {
                e.span(label.span);
                e.str(&label.message);
            }
            e.w.usize(d.notes.len());
            for note in &d.notes {
                e.str(note);
            }
        }
        let pre_bytes = std::mem::take(&mut e.w.bytes);

        // The kernel's declarations.
        e.w.usize(defs.len());
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            e.str(def.name());
            e.str(def.path());
            e.w.bool(def.theorem());
            e.w.bool(def.instance());
            e.w.bool(def.fold());
            // Opacity, and the `unfolding` list as written, each name as a
            // reference (docs/proposals/opaque-definitions.md §6.4).
            e.w.bool(def.opaque());
            e.w.bool(def.tailrec());
            let refs = &unfolding_refs[id.0 - before.defs];
            e.w.usize(refs.len());
            for reference in refs.iter() {
                e.term(reference);
            }
            e.span(def.span());
            e.term(def.ty());
            e.term(def.body().expect("checked above"));
            let group = def
                .group()
                .as_ref()
                .expect("a final definition has a group");
            e.w.usize(group.len());
            for m in group.iter() {
                if m.0 < before.defs {
                    return Err(format!("`{}`'s group is older", def.path()));
                }
                e.w.usize(m.0 - before.defs);
            }
            // What the runtimes run instead, for a definition with `decreasing`.
            e.w.bool(def.own_run_body().is_some());
            if let Some(run) = def.own_run_body() {
                e.term(run);
            }
            e.hash(def_hash(g, id));
        }
        e.w.usize(datas.len());
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            e.str(data.name());
            e.str(data.path());
            e.w.usize(data.params().len());
            for (x, ty) in data.params() {
                e.str(x);
                e.term(ty);
            }
            e.w.usize(data.auto_params().len());
            for a in data.auto_params() {
                e.w.bool(*a);
            }
            e.w.usize(data.indices().len());
            for (x, ty) in data.indices() {
                e.str(x);
                e.term(ty);
            }
            codec::sort(&mut e.w, data.sort());
            e.w.usize(data.ctors().len());
            for ctor in data.ctors() {
                e.str(&ctor.name);
                e.w.usize(ctor.fields.len());
                for (x, ty) in &ctor.fields {
                    e.str(x);
                    e.term(ty);
                }
                e.w.usize(ctor.implicit.len());
                for i in &ctor.implicit {
                    e.w.bool(*i);
                }
                // What checking the fields found, which a trusted replay
                // installs as it is (stage 3, D1660).
                e.w.usize(ctor.field_sorts.len());
                for s in &ctor.field_sorts {
                    codec::sort(&mut e.w, *s);
                }
                e.w.usize(ctor.field_erased.len());
                for x in &ctor.field_erased {
                    e.w.bool(*x);
                }
                e.w.usize(ctor.result.len());
                for r in &ctor.result {
                    e.term(r);
                }
                e.w.bool(ctor.braced);
            }
            e.w.bool(data.record());
            // The elaborator's mark, which the kernel can't recompute
            // (interface dictionaries, D2502); `eta` itself is recomputed.
            e.w.bool(data.no_eta());
            e.w.usize(data.group().len());
            for m in data.group().iter() {
                if m.0 < before.datas {
                    return Err(format!("`{}`'s group is older", data.path()));
                }
                e.w.usize(m.0 - before.datas);
            }
            if data.defs_before() < before.defs || data.datas_before() < before.datas {
                return Err(format!("`{}` is declared before the file", data.path()));
            }
            e.w.usize(data.defs_before() - before.defs);
            e.w.usize(data.datas_before() - before.datas);
            e.span(data.span());
            e.hash(data_hash(g, d));
        }
        // The built-ins bound: replay binds them again the same way, and
        // checks it got these.
        e.w.usize(bound.len());
        for (kind, offset, b) in bound {
            e.w.u8(kind);
            e.w.usize(offset);
            e.str(b.name());
        }

        // The names: those that changed, then the new ones in the order
        // they were declared (what the early ones finally name), then the
        // members marked.
        let entry = |k: &str| {
            self.scope
                .stored(k)
                .copied()
                .ok_or_else(|| format!("`{k}` was declared and is gone"))
        };
        e.w.usize(names.changed.len());
        for k in &names.changed {
            let (global, span) = entry(k)?;
            e.str(k);
            e.global(self, global);
            e.span(span);
        }
        e.w.usize(names.late.len());
        for (k, follower) in &names.late {
            let (global, span) = entry(k)?;
            e.str(k);
            e.global(self, global);
            e.span(span);
            e.w.bool(*follower);
        }
        for (k, _) in &names.early {
            let (global, _) = entry(k)?;
            e.global(self, global);
        }
        e.w.usize(names.members.len());
        for k in &names.members {
            e.str(k);
        }

        // The elaborator's tables, and the part the format puts between
        // them.
        self.tables
            .encode_since(&before.tables, &writes.tables, &mut e, |e| {
                self.encode_extensions(e, unit)
            })?;

        // What code navigation recorded in the unit's files.
        let own = |file: &FileId| unit.own_files.contains(file);
        match (&self.present.nav, before.nav) {
            (Some(nav), Some((locals, binders, outline, params, named))) => {
                let nav = nav.borrow();
                if !nav.pending.is_empty() || nav.outline.len() != outline {
                    return Err("navigation left something unfinished".to_string());
                }
                e.w.bool(true);
                let mut refs: Vec<(&Span, &Noted)> =
                    nav.refs.iter().filter(|(at, _)| own(&at.file)).collect();
                refs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
                e.w.usize(refs.len());
                let mut prev = 0;
                for (at, noted) in refs {
                    e.span_after(*at, &mut prev);
                    e.str(&noted.key);
                    // A target in another unit's file is kept by the name
                    // of its declaration, where it is found when the entry
                    // is replayed (§4.3).
                    let by_name = !own(&noted.target.file)
                        && self.scope.get(&noted.key).map(|(_, s)| s) == Some(noted.target);
                    e.w.bool(by_name);
                    if !by_name {
                        e.span_after(noted.target, &mut at.start.clone());
                    }
                    e.global(self, noted.global);
                    e.w.bool(noted.dot.is_some());
                    if let Some(dot) = &noted.dot {
                        e.str(dot);
                    }
                }
                let mut exprs: Vec<(&Span, &String)> = nav
                    .expr_types
                    .iter()
                    .filter(|(at, _)| own(&at.file))
                    .collect();
                exprs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
                e.w.usize(exprs.len());
                let mut prev = 0;
                for (at, ty) in exprs {
                    e.span_after(*at, &mut prev);
                    e.str(ty);
                }
                let mut exprs: Vec<(&Span, &String)> = nav
                    .expr_unfolded
                    .iter()
                    .filter(|(at, _)| own(&at.file))
                    .collect();
                exprs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
                e.w.usize(exprs.len());
                let mut prev = 0;
                for (at, ty) in exprs {
                    e.span_after(*at, &mut prev);
                    e.str(ty);
                }
                let mut used: Vec<(&Span, &String)> = nav
                    .call_defaults
                    .iter()
                    .filter(|(at, _)| own(&at.file))
                    .collect();
                used.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
                e.w.usize(used.len());
                let mut prev = 0;
                for (at, text) in used {
                    e.span_after(*at, &mut prev);
                    e.str(text);
                }
                let mut types: Vec<(&(FileId, u32), &String)> = nav
                    .local_types
                    .iter()
                    .filter(|((file, _), _)| own(file))
                    .collect();
                types.sort_by_key(|((file, at), _)| (file.index(), *at));
                e.w.usize(types.len());
                let mut prev = 0;
                for ((file, at), ty) in types {
                    e.span_after(Span::new(*file, *at, *at), &mut prev);
                    e.str(ty);
                }
                let mut types: Vec<(&(FileId, u32), &String)> = nav
                    .local_unfolded
                    .iter()
                    .filter(|((file, _), _)| own(file))
                    .collect();
                types.sort_by_key(|((file, at), _)| (file.index(), *at));
                e.w.usize(types.len());
                let mut prev = 0;
                for ((file, at), ty) in types {
                    e.span_after(Span::new(*file, *at, *at), &mut prev);
                    e.str(ty);
                }
                for uses in [&nav.locals[locals..], &nav.binders[binders..]] {
                    e.w.usize(uses.len());
                    let mut prev = 0;
                    for u in uses {
                        e.span_after(u.span, &mut prev);
                        e.str(&u.name);
                        e.span_after(u.binder, &mut u.span.start.clone());
                    }
                }
                // A library file's parameters and named arguments, which
                // link the second to the first in the index, are not found
                // again when it loads from the entry (it isn't walked).
                let (params, named): (Vec<&ParamBinder>, Vec<&NamedUse>) = if unit.library {
                    (
                        (nav.params[params..].iter())
                            .filter(|p| own(&p.owner.file))
                            .collect(),
                        (nav.named[named..].iter())
                            .filter(|u| own(&u.span.file))
                            .collect(),
                    )
                } else {
                    (Vec::new(), Vec::new())
                };
                e.w.usize(params.len());
                let mut prev = 0;
                for p in &params {
                    e.span_after(p.owner, &mut prev);
                    e.str(&p.name);
                    e.span_after(p.binder, &mut p.owner.start.clone());
                }
                e.w.usize(named.len());
                let mut prev = 0;
                for u in &named {
                    e.span_after(u.span, &mut prev);
                    e.str(&u.name);
                    for at in u.head {
                        e.span_after(at, &mut u.span.start.clone());
                    }
                }
                // A namespace's are found again by walking its syntax.
                let mut fields: Vec<(&(Span, String), &Span)> = nav
                    .field_spans
                    .iter()
                    .filter(|((at, _), _)| unit.library && own(&at.file))
                    .collect();
                fields.sort_by_key(|((at, name), _)| {
                    (at.file.index(), at.start, at.end, name.as_str())
                });
                e.w.usize(fields.len());
                let mut prev = 0;
                for ((at, name), span) in fields {
                    e.span_after(*at, &mut prev);
                    e.str(name);
                    e.span_after(*span, &mut at.start.clone());
                }
            }
            (None, None) => e.w.bool(false),
            _ => return Err("navigation was turned on while loading".to_string()),
        }
        if let Some(problem) = e.out.problem {
            return Err(problem);
        }
        // The body: strings, files, what replay reads first, terms, then
        // the rest.
        let mut body = Writer::default();
        body.usize(e.terms.strings.len());
        for s in &e.terms.strings {
            body.str(s);
        }
        body.usize(e.out.files.len());
        for file in &e.out.files {
            body.str(file);
        }
        body.blob(&pre_bytes);
        body.usize(e.terms.node_count());
        body.raw(&e.terms.nodes.bytes);
        body.raw(&e.w.bytes);
        Ok(seal(key, salt, &e.out.deps, &body.bytes))
    }

    fn encode_extensions(&self, e: &mut Encoding, unit: &UnitOut) {
        // The extensions the namespace declares (a library file has none).
        let own = self.current_namespace().filter(|_| !unit.library);
        let mut extensions: Vec<(&String, &String)> = self
            .scope
            .all_extended()
            .filter(|(k, _)| own.is_some() && self.longest_namespace(k, false).as_deref() == own)
            .collect();
        extensions.sort();
        e.w.usize(extensions.len());
        for (k, target) in extensions {
            e.str(k);
            e.str(target);
        }
    }
}

/// The whole entry: the header, the body and a checksum (§5.3).
fn seal(key: &Key, salt: [u8; 16], deps: &[Dep], body: &[u8]) -> Vec<u8> {
    let mut w = Writer::default();
    w.raw(MAGIC);
    w.raw(&FORMAT.to_le_bytes());
    w.raw(key);
    w.raw(&salt);
    w.usize(deps.len());
    for (kind, path, hash) in deps {
        w.u8(*kind);
        w.str(path);
        w.raw(&hash.0);
    }
    w.blob(body);
    let sum = blake3::hash(&w.bytes);
    w.raw(sum.as_bytes());
    w.bytes
}

/// The header's dependencies and the body, if `bytes` is a whole entry for
/// `key` written with `salt`.
fn open<'a>(bytes: &'a [u8], key: &Key, salt: [u8; 16]) -> Read<(Vec<Dep>, &'a [u8])> {
    if bytes.len() < 32 {
        return bad("too short");
    }
    let (content, sum) = bytes.split_at(bytes.len() - 32);
    if blake3::hash(content).as_bytes() != sum {
        return bad("the checksum doesn't match");
    }
    let mut r = Reader::new(content);
    if r.raw(MAGIC.len())? != MAGIC {
        return bad("not an entry");
    }
    if r.array::<4>()? != FORMAT.to_le_bytes() {
        return bad("another format");
    }
    if &r.array::<32>()? != key {
        return bad("another key");
    }
    if r.array::<16>()? != salt {
        return bad("another cache's entry");
    }
    let n = r.count(34)?;
    let mut deps = Vec::with_capacity(n);
    for _ in 0..n {
        let kind = r.u8()?;
        let path = r.string()?;
        deps.push((kind, path, ContentHash(r.array::<32>()?)));
    }
    let body = r.blob()?;
    if !r.done() {
        return bad("bytes after the body");
    }
    Ok((deps, body))
}

// ---- Reading --------------------------------------------------------------

/// How an entry's references are read back in this session.
struct In {
    base_defs: usize,
    base_datas: usize,
    n_defs: usize,
    n_datas: usize,
    ext_defs: Vec<DefId>,
    ext_datas: Vec<DataId>,
    files: Vec<FileId>,
}

impl ReadRefs for In {
    fn def(&self, r: &mut Reader) -> Read<DefId> {
        let v = r.usize()?;
        let i = v >> 1;
        if v & 1 == 0 {
            if i >= self.n_defs {
                return bad("a definition out of range");
            }
            return Ok(DefId(self.base_defs + i));
        }
        self.ext_defs
            .get(i)
            .copied()
            .ok_or_else(|| Bad("a dependency out of range".to_string()))
    }

    fn data(&self, r: &mut Reader) -> Read<DataId> {
        let v = r.usize()?;
        let i = v >> 1;
        if v & 1 == 0 {
            if i >= self.n_datas {
                return bad("a data type out of range");
            }
            return Ok(DataId(self.base_datas + i));
        }
        self.ext_datas
            .get(i)
            .copied()
            .ok_or_else(|| Bad("a dependency out of range".to_string()))
    }

    fn span(&self, r: &mut Reader) -> Read<Span> {
        let Some(&file) = self.files.get(r.usize()?) else {
            return bad("a file out of range");
        };
        let start = r.u32()?;
        let len = r.u32()?;
        let Some(end) = start.checked_add(len) else {
            return bad("a span out of range");
        };
        Ok(Span::new(file, start, end))
    }

    fn span_after(&self, r: &mut Reader, prev: &mut u32) -> Read<Span> {
        let Some(&file) = self.files.get(r.usize()?) else {
            return bad("a file out of range");
        };
        let start = i64::from(*prev) + codec::unzigzag(r.uint()?);
        let len = r.u32()?;
        let Some(start) = u32::try_from(start).ok() else {
            return bad("a span out of range");
        };
        let Some(end) = start.checked_add(len) else {
            return bad("a span out of range");
        };
        *prev = start;
        Ok(Span::new(file, start, end))
    }
}

/// A definition, read.
struct DefEntry {
    name: Name,
    path: Name,
    theorem: bool,
    instance: bool,
    fold: bool,
    opaque: bool,
    tailrec: bool,
    /// Its `unfolding` list as written.
    unfolding: Vec<DefId>,
    span: Span,
    ty: Term,
    body: Term,
    group: Vec<usize>,
    run_body: Option<Term>,
    /// Its content hash when the entry was written.
    hash: Option<ContentHash>,
}

/// A constructor, read.
struct CtorEntry {
    name: Name,
    fields: Vec<(Name, Term)>,
    field_sorts: Vec<Sort>,
    field_erased: Vec<bool>,
    implicit: Vec<bool>,
    result: Vec<Term>,
    braced: bool,
}

/// A data type, read.
struct DataEntry {
    name: Name,
    path: Name,
    params: Vec<(Name, Term)>,
    auto_params: Vec<bool>,
    indices: Vec<(Name, Term)>,
    sort: Sort,
    ctors: Vec<CtorEntry>,
    record: bool,
    no_eta: bool,
    group: Vec<usize>,
    defs_before: usize,
    datas_before: usize,
    span: Span,
    /// Its content hash when the entry was written.
    hash: Option<ContentHash>,
}

/// A global, read: an ability by its operations' data type, which is
/// found once the abilities are replayed.
#[derive(Clone, Copy)]
enum GlobalEntry {
    Plain(Global),
    Ability(DataId),
    Op(DataId, usize),
}

/// Everything an entry holds besides the kernel's declarations.
struct Rest {
    changed: Vec<(String, GlobalEntry, Span)>,
    new: Vec<(String, GlobalEntry, Span, bool)>,
    /// What each name declared before the library files loaded names
    /// ([`Pre::early`]), in the same order.
    early: Vec<GlobalEntry>,
    members: Vec<String>,
    /// What `state::Tables` holds.
    tables: state::TablesDelta,
    /// Extensions, and the keys they stand for.
    extensions: Vec<(String, String)>,
    nav: Option<NavEntry>,
}

/// Where a reference leads: a span, or the declaration with that key.
enum Target {
    Span(Span),
    Key,
}

struct NavEntry {
    refs: Vec<(Span, String, Target, GlobalEntry, Option<String>)>,
    exprs: Vec<(Span, String)>,
    expr_unfolded: Vec<(Span, String)>,
    call_defaults: Vec<(Span, String)>,
    local_types: Vec<(Span, String)>,
    local_unfolded: Vec<(Span, String)>,
    locals: Vec<(Span, String, Span)>,
    binders: Vec<(Span, String, Span)>,
    params: Vec<ParamBinder>,
    named: Vec<NamedUse>,
    fields: Vec<(Span, String, Span)>,
}

/// An entry's body being read.
pub(crate) struct Body<'a> {
    r: Reader<'a>,
    terms: Terms,
    refs: In,
}

impl Body<'_> {
    /// A declaration's content hash, if it was written with one.
    fn hash(&mut self) -> Read<Option<ContentHash>> {
        Ok(if self.r.bool()? {
            Some(ContentHash(self.r.array::<32>()?))
        } else {
            None
        })
    }

    pub(crate) fn str(&mut self) -> Read<Name> {
        self.terms.name(&mut self.r)
    }

    pub(crate) fn string(&mut self) -> Read<String> {
        Ok(self.str()?.to_string())
    }

    pub(crate) fn term(&mut self) -> Read<Term> {
        self.terms.term(&mut self.r)
    }

    /// A test's probe, `depth` `&&`s down.
    pub(crate) fn probe(&mut self, depth: usize) -> Read<crate::Probe> {
        if depth > 64 {
            return bad("a probe nested too deep".to_string());
        }
        let span = self.span()?;
        let truth = if self.r.bool()? {
            Some(self.term()?)
        } else {
            None
        };
        let whole = self.r.bool()?;
        let kind = match self.r.u8()? {
            0 => crate::ProbeKind::Other,
            1 => {
                let op = self.string()?;
                let Some(op) = TEST_OPS.iter().find(|o| **o == op) else {
                    return bad(format!("no operator `{op}`"));
                };
                crate::ProbeKind::Compare {
                    op,
                    left: self.term()?,
                    right: self.term()?,
                }
            }
            2 => crate::ProbeKind::And(
                Box::new(self.probe(depth + 1)?),
                Box::new(self.probe(depth + 1)?),
            ),
            _ => return bad("an unknown kind of probe".to_string()),
        };
        Ok(crate::Probe {
            span,
            truth,
            whole,
            kind,
        })
    }

    pub(crate) fn def(&mut self) -> Read<DefId> {
        self.refs.def(&mut self.r)
    }

    pub(crate) fn data(&mut self) -> Read<DataId> {
        self.refs.data(&mut self.r)
    }

    pub(crate) fn span(&mut self) -> Read<Span> {
        self.refs.span(&mut self.r)
    }

    fn span_after(&mut self, prev: &mut u32) -> Read<Span> {
        self.refs.span_after(&mut self.r, prev)
    }

    pub(crate) fn count(&mut self) -> Read<usize> {
        self.r.count(1)
    }

    fn global(&mut self, files: usize) -> Read<GlobalEntry> {
        Ok(match self.r.u8()? {
            0 => GlobalEntry::Plain(Global::Def(self.def()?)),
            1 => GlobalEntry::Plain(Global::Data(self.data()?)),
            2 => GlobalEntry::Plain(Global::Ctor(self.data()?, self.r.usize()?)),
            3 => GlobalEntry::Ability(self.data()?),
            4 => GlobalEntry::Op(self.data()?, self.r.usize()?),
            5 => {
                let f = self.r.usize()?;
                if f >= files {
                    return bad("a library file out of range");
                }
                GlobalEntry::Plain(Global::Pending(f, pending_kind(self.r.u8()?)?))
            }
            _ => return bad("an unknown kind of name"),
        })
    }

    fn named_terms(&mut self) -> Read<Vec<(Name, Term)>> {
        let n = self.count()?;
        (0..n).map(|_| Ok((self.str()?, self.term()?))).collect()
    }

    fn bools(&mut self) -> Read<Vec<bool>> {
        let n = self.count()?;
        (0..n).map(|_| self.r.bool()).collect()
    }

    fn offsets(&mut self, below: usize) -> Read<Vec<usize>> {
        let n = self.count()?;
        (0..n)
            .map(|_| {
                let i = self.r.usize()?;
                if i < below {
                    Ok(i)
                } else {
                    bad("a group member out of range")
                }
            })
            .collect()
    }
}

/// What a namespace's replay reads before the rest of its entry (empty for
/// a library file): see [`PreOut`].
#[derive(Default)]
struct Pre {
    needs: Needs,
    library: Vec<(usize, Key)>,
    includes: Vec<(String, Key)>,
    early: Vec<(String, Span, bool)>,
    warnings: Vec<Diagnostic>,
}

impl Pre {
    fn is_empty(&self) -> bool {
        self.needs.files.is_empty()
            && self.needs.dots.is_empty()
            && self.needs.equations.is_empty()
            && self.library.is_empty()
            && self.includes.is_empty()
            && self.early.is_empty()
            && self.warnings.is_empty()
    }
}

/// An entry's body up to its terms: its strings, its files, and what a
/// namespace's replay reads first; the reader is at the terms.
struct Head<'a> {
    r: Reader<'a>,
    strings: Vec<Name>,
    files: Vec<FileId>,
    pre: Pre,
}

/// Everything an entry holds, read and checked.
struct Decoded {
    defs: Vec<DefEntry>,
    datas: Vec<DataEntry>,
    bound: Vec<(u8, usize, Builtin)>,
    rest: Rest,
}

impl Elaborator {
    /// The files a library file's entry may refer to, by their names in
    /// entries.
    fn std_file_ids(&self) -> HashMap<String, FileId> {
        self.std_file_names()
            .into_iter()
            .map(|(id, name)| (name, id))
            .collect()
    }

    /// Reads an entry's body up to its terms. Changes nothing.
    fn read_head<'a>(&self, body: &'a [u8], file_ids: &HashMap<String, FileId>) -> Read<Head<'a>> {
        let index = self.library_index().expect("a library is installed");
        let mut r = Reader::new(body);
        let strings = Terms::read_strings(&mut r)?;
        let n = r.count(1)?;
        let mut files = Vec::with_capacity(n);
        for _ in 0..n {
            let name = r.string()?;
            match file_ids.get(&name) {
                Some(&id) => files.push(id),
                None => return bad(format!("no file `{name}`")),
            }
        }
        let pre_bytes = r.blob()?;
        let mut body = Body {
            r: Reader::new(pre_bytes),
            terms: Terms {
                nodes: Vec::new(),
                strings,
            },
            refs: In {
                base_defs: 0,
                base_datas: 0,
                n_defs: 0,
                n_datas: 0,
                ext_defs: Vec::new(),
                ext_datas: Vec::new(),
                files,
            },
        };
        let mut pre = Pre::default();
        let n = body.count()?;
        for _ in 0..n {
            let path = body.string()?;
            match index.files.iter().position(|f| f.path == path) {
                Some(f) => {
                    pre.needs.files.insert(f);
                }
                None => return bad(format!("no library file `{path}`")),
            }
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.needs.dots.insert(body.string()?);
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.needs.equations.insert(body.string()?);
        }
        let n = body.count()?;
        for _ in 0..n {
            let path = body.string()?;
            match index.files.iter().position(|f| f.path == path) {
                Some(f) => pre.library.push((f, body.r.array::<32>()?)),
                None => return bad(format!("no library file `{path}`")),
            }
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.includes.push((body.string()?, body.r.array::<32>()?));
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.early
                .push((body.string()?, body.span()?, body.r.bool()?));
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.warnings.push(read_warning(&mut body)?);
        }
        if !body.r.done() {
            return bad("bytes after what replay reads first");
        }
        Ok(Head {
            r,
            strings: body.terms.strings,
            files: body.refs.files,
            pre,
        })
    }

    /// Reads the rest of an entry, in this session: its dependencies must
    /// be here, with the hashes it was made with. Changes nothing.
    fn decode(&self, deps: &[Dep], head: Head, early: &[(String, Span, bool)]) -> Read<Decoded> {
        let index = self.library_index().expect("a library is installed");
        let g = &self.ev();
        let _op = g.machine.budget.operation(self.options.limits);

        // The dependencies: each path names one final declaration, with the
        // hash it had when the entry was written.
        self.session.paths.borrow_mut().sync(g.env);
        let paths = self.session.paths.borrow();
        let mut ext_defs = vec![DefId(usize::MAX); deps.len()];
        let mut ext_datas = vec![DataId(usize::MAX); deps.len()];
        for (i, (kind, path, hash)) in deps.iter().enumerate() {
            let found = match kind {
                0 => paths.unique_def(path).map(DefId).and_then(|id| {
                    ext_defs[i] = id;
                    def_hash(g, id).ok().flatten()
                }),
                1 => paths.unique_data(path).map(DataId).and_then(|id| {
                    ext_datas[i] = id;
                    data_hash(g, id).ok().flatten()
                }),
                _ => return bad("an unknown kind of dependency"),
            };
            if found != Some(*hash) {
                return bad(format!("`{path}` isn't what the entry was made with"));
            }
        }

        // The counts of the entry's own declarations come after the terms,
        // which may refer to them: read the terms with room for any, and
        // check the references once the counts are known.
        let Head {
            mut r,
            strings,
            files,
            ..
        } = head;
        let node_count = r.count(1)?;
        let mut body = Body {
            r,
            terms: Terms {
                nodes: Vec::new(),
                strings,
            },
            refs: In {
                base_defs: g.env.defs().len(),
                base_datas: g.env.datas().len(),
                n_defs: usize::MAX >> 2,
                n_datas: usize::MAX >> 2,
                ext_defs,
                ext_datas,
                files,
            },
        };
        let Body { r, terms, refs } = &mut body;
        terms.read_nodes(r, refs, node_count)?;

        let n = body.count()?;
        let mut defs = Vec::with_capacity(n);
        for _ in 0..n {
            defs.push(DefEntry {
                name: body.str()?,
                path: body.str()?,
                theorem: body.r.bool()?,
                instance: body.r.bool()?,
                fold: body.r.bool()?,
                opaque: body.r.bool()?,
                tailrec: body.r.bool()?,
                unfolding: {
                    let k = body.count()?;
                    let mut unfolding = Vec::with_capacity(k);
                    for _ in 0..k {
                        match body.term()? {
                            Term::Def(id) => unfolding.push(id),
                            _ => return bad("an `unfolding` entry that isn't a definition"),
                        }
                    }
                    unfolding
                },
                span: body.span()?,
                ty: body.term()?,
                body: body.term()?,
                group: body.offsets(n)?,
                run_body: if body.r.bool()? {
                    Some(body.term()?)
                } else {
                    None
                },
                hash: body.hash()?,
            });
        }
        let n_defs = defs.len();
        let n = body.count()?;
        let mut datas = Vec::with_capacity(n);
        for _ in 0..n {
            let name = body.str()?;
            let path = body.str()?;
            let params = body.named_terms()?;
            let auto_params = body.bools()?;
            let indices = body.named_terms()?;
            let sort = codec::read_sort(&mut body.r)?;
            let k = body.count()?;
            let mut ctors = Vec::with_capacity(k);
            for _ in 0..k {
                let name = body.str()?;
                let fields = body.named_terms()?;
                let implicit = body.bools()?;
                let m = body.count()?;
                let field_sorts = (0..m)
                    .map(|_| codec::read_sort(&mut body.r))
                    .collect::<Read<_>>()?;
                let field_erased = body.bools()?;
                let m = body.count()?;
                let result = (0..m).map(|_| body.term()).collect::<Read<_>>()?;
                let braced = body.r.bool()?;
                ctors.push(CtorEntry {
                    name,
                    fields,
                    field_sorts,
                    field_erased,
                    implicit,
                    result,
                    braced,
                });
            }
            datas.push(DataEntry {
                name,
                path,
                params,
                auto_params,
                indices,
                sort,
                ctors,
                record: body.r.bool()?,
                no_eta: body.r.bool()?,
                group: body.offsets(n)?,
                defs_before: body.r.usize()?,
                datas_before: body.r.usize()?,
                span: body.span()?,
                hash: body.hash()?,
            });
        }
        let n_datas = datas.len();
        let n = body.count()?;
        let mut bound = Vec::with_capacity(n);
        for _ in 0..n {
            let kind = body.r.u8()?;
            let offset = body.r.usize()?;
            let name = body.str()?;
            let Some(b) = builtin_named(kind, &name) else {
                return bad(format!("no built-in `{name}`"));
            };
            if offset >= if kind == 0 { n_defs } else { n_datas } {
                return bad("a built-in bound to a declaration the entry doesn't have");
            }
            bound.push((kind, offset, b));
        }
        bound.sort();
        body.refs.n_defs = n_defs;
        body.refs.n_datas = n_datas;
        // Every reference the terms make to the entry's own declarations is
        // to one it has.
        let (base_defs, base_datas) = (body.refs.base_defs, body.refs.base_datas);
        for t in &body.terms.nodes {
            let mut ok = true;
            match t.as_ref() {
                Term::Def(id) => ok = id.0 < base_defs + n_defs,
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _) => {
                    ok = d.0 < base_datas + n_datas;
                }
                _ => {}
            }
            if !ok {
                return bad("a term refers to a declaration the entry doesn't have");
            }
        }

        let rest = read_tables(&mut body, index.files.len(), early.len())?;
        if !body.r.done() {
            return bad("bytes after the tables");
        }
        if rest.nav.is_some() != self.present.nav.is_some() {
            return bad("navigation recorded or not");
        }
        // Every ability a name refers to is one there will be.
        let abilities: HashSet<DataId> = self
            .tables
            .abilities
            .iter()
            .chain(&rest.tables.abilities)
            .map(|a| a.op_data)
            .collect();
        let globals = rest.changed.iter().map(|(_, g, _)| g);
        let globals = globals.chain(rest.new.iter().map(|(_, g, _, _)| g));
        let globals = globals.chain(&rest.early);
        let globals = globals.chain(rest.nav.iter().flat_map(|n| n.refs.iter().map(|r| &r.3)));
        for g in globals {
            if let GlobalEntry::Ability(d) | GlobalEntry::Op(d, _) = g
                && !abilities.contains(d)
            {
                return bad("a name refers to an ability there isn't");
            }
        }
        // Every target kept by name is one there will be.
        if let Some(nav) = &rest.nav {
            let own: HashSet<&str> = rest
                .changed
                .iter()
                .map(|(k, _, _)| k.as_str())
                .chain(rest.new.iter().map(|(k, _, _, _)| k.as_str()))
                .chain(early.iter().map(|(k, _, _)| k.as_str()))
                .collect();
            for (_, key, target, _, _) in &nav.refs {
                if matches!(target, Target::Key)
                    && !own.contains(key.as_str())
                    && self.scope.get(key).is_none()
                {
                    return bad(format!("no `{key}` to lead to"));
                }
            }
        }
        Ok(Decoded {
            defs,
            datas,
            bound,
            rest,
        })
    }

    /// Loads library file `f` from an entry. On any problem, nothing has
    /// changed, and the reason is returned.
    fn replay(&mut self, bytes: &[u8], key: &Key, salt: [u8; 16]) -> Read<()> {
        let (deps, body) = open(bytes, key, salt)?;
        let head = self.read_head(body, &self.std_file_ids())?;
        if !head.pre.is_empty() {
            return bad("a library file's entry with a namespace's parts");
        }
        let d = self.decode(&deps, head, &[])?;
        if !d.rest.tables.tests.is_empty() {
            return bad("a library file's entry with tests");
        }
        self.admit_replayed(&d.defs, &d.datas, &d.bound, &d.rest.tables, true)?;
        self.replay_tables(d.rest, &[]);
        Ok(())
    }

    /// Submits an entry's declarations to the kernel's trusted admission
    /// (`check::admit_trusted_*`), which installs them as they were checked
    /// when the entry was written, without checking them again (stage 3,
    /// D1660). This is the one place a replay reaches the kernel, and so the
    /// cache's side of its trust boundary.
    ///
    /// The declarations are made in their original order (a data group
    /// goes where its `defs_before` and `datas_before` say), and each group
    /// is defined as soon as everything it refers to is final, which is no
    /// later than the elaborator defined it. Each final declaration is
    /// bound as a built-in, if it is one, as elaborating binds it, and the
    /// built-ins bound must be the entry's `bound`: only a `library` file's
    /// declarations are bound, as only elaborating the library binds them,
    /// so a namespace's entry that says it binds any is refused before
    /// anything is admitted. If the kernel refuses anything (its structural
    /// checks: dependencies final, shapes right), or other built-ins are
    /// bound, what was added is removed and the file is elaborated instead.
    /// That is never expected (`Stats::refused`), unless the operation was
    /// cancelled meanwhile, which is not counted.
    fn admit_replayed(
        &mut self,
        defs: &[DefEntry],
        datas: &[DataEntry],
        bound: &[(u8, usize, Builtin)],
        tables: &state::TablesDelta,
        library: bool,
    ) -> Read<()> {
        if !library && !bound.is_empty() {
            self.session.cache_stats.refused += 1;
            return bad("a namespace's entry that binds built-ins");
        }
        let param_defaults: HashSet<DefId> = tables.param_default_helpers().collect();
        let mark = self.kernel.mark();
        let (base_defs, base_datas) = (mark.defs(), mark.datas());
        // Taken here, compared once the undo is done (below). Every binding,
        // always; the declarations too when a test forces the refusal,
        // since dumping them for every entry would cost too much.
        let forced = self.options.refuse_replays_after.is_some();
        let witness = stitchwort_core::globals::CHECK_UNDOS.then(|| self.undo_witness(forced));
        let result = self
            .submit(defs, datas, &param_defaults, base_defs, base_datas, library)
            .and_then(|()| {
                if bound_builtins(&self.ev(), base_defs, base_datas) != bound {
                    return bad("other built-ins were bound");
                }
                Ok(())
            });
        if let Err(why) = result {
            // A cancelled operation (an editor keystroke) ends the kernel's
            // calls with an error that isn't the entry's fault: not counted.
            if !self.kernel.machine.budget.cancelled() {
                self.session.cache_stats.refused += 1;
            }
            // Nothing else refers to what was added yet. Not
            // `Kernel::rewind`: an operation may be running (a namespace
            // that needs this file), whose budget must stay as it is.
            self.kernel.forget_since(&mark);
            if let Some(witness) = witness {
                if let Some(left) = self.kernel.derived_state_since(&mark) {
                    panic!("a refused replay's undo left derived state behind: {left}");
                }
                let now = self.undo_witness(forced);
                assert!(
                    now == witness,
                    "a refused replay's undo left something behind: {}",
                    first_line_differing(&witness, &now)
                );
            }
            let ids = crate::state::Ids {
                defs: base_defs,
                datas: base_datas,
            };
            self.session.owners.truncate(ids);
            self.session.paths.get_mut().truncate(ids);
            return Err(why);
        }
        // What the entry says the declarations hash to: the next entries
        // that name them are checked against these rather than hashing the
        // terms again. An entry is sealed (`open`), and one that lies about
        // a hash makes the entries written against the true one miss.
        let mut hashes = self.kernel.caches.hashes.borrow_mut();
        for (i, def) in defs.iter().enumerate() {
            if let Some(h) = def.hash {
                hashes.insert(HashKey::Def(DefId(base_defs + i)), h);
            }
        }
        for (i, data) in datas.iter().enumerate() {
            if let Some(h) = data.hash {
                hashes.insert(HashKey::Data(DataId(base_datas + i)), h);
            }
        }
        Ok(())
    }

    fn submit(
        &mut self,
        defs: &[DefEntry],
        datas: &[DataEntry],
        param_defaults: &HashSet<DefId>,
        base_defs: usize,
        base_datas: usize,
        library: bool,
    ) -> Read<()> {
        let refused = |d: stitchwort_syntax::Diagnostic| Bad(format!("refused: {}", d.message));
        // The groups, each with the entry's own declarations its terms
        // refer to (besides its members).
        struct Group {
            data: bool,
            members: Vec<usize>,
            needs_defs: BTreeSet<usize>,
            needs_datas: BTreeSet<usize>,
            done: bool,
        }
        let mut groups: Vec<Group> = Vec::new();
        let mut seen = HashSet::default();
        for (i, def) in defs.iter().enumerate() {
            if !def.group.contains(&i) {
                return bad("a definition outside its own group");
            }
            if !seen.insert(def.group[0]) {
                continue;
            }
            let mut needs_defs = BTreeSet::new();
            let mut needs_datas = BTreeSet::new();
            for &m in &def.group {
                if defs[m].group != def.group {
                    return bad("members disagree about their group");
                }
                // What it unfolds must be final first, as what its body
                // names must.
                for id in &defs[m].unfolding {
                    if id.0 >= base_defs {
                        needs_defs.insert(id.0 - base_defs);
                    }
                }
                codec::references(
                    &defs[m].body,
                    &mut |id| {
                        if id.0 >= base_defs {
                            needs_defs.insert(id.0 - base_defs);
                        }
                    },
                    &mut |d| {
                        if d.0 >= base_datas {
                            needs_datas.insert(d.0 - base_datas);
                        }
                    },
                );
            }
            for m in &def.group {
                needs_defs.remove(m);
            }
            groups.push(Group {
                data: false,
                members: def.group.clone(),
                needs_defs,
                needs_datas,
                done: false,
            });
        }
        let mut data_groups: Vec<usize> = Vec::new();
        let mut seen = HashSet::default();
        for (j, data) in datas.iter().enumerate() {
            let Some(&first) = data.group.first() else {
                return bad("an empty data group");
            };
            if first != j {
                if !seen.contains(&first) || datas[first].group != data.group {
                    return bad("a data group out of order");
                }
                continue;
            }
            seen.insert(j);
            if data.group.iter().enumerate().any(|(k, m)| *m != j + k) || data.datas_before != j {
                return bad("a data group out of order");
            }
            let mut needs_defs = BTreeSet::new();
            let mut needs_datas = BTreeSet::new();
            for &m in &data.group {
                for ctor in &datas[m].ctors {
                    for t in ctor.fields.iter().map(|(_, t)| t).chain(&ctor.result) {
                        codec::references(
                            t,
                            &mut |id| {
                                if id.0 >= base_defs {
                                    needs_defs.insert(id.0 - base_defs);
                                }
                            },
                            &mut |d| {
                                if d.0 >= base_datas {
                                    needs_datas.insert(d.0 - base_datas);
                                }
                            },
                        );
                    }
                }
            }
            for m in &data.group {
                needs_datas.remove(m);
            }
            data_groups.push(groups.len());
            groups.push(Group {
                data: true,
                members: data.group.clone(),
                needs_defs,
                needs_datas,
                done: false,
            });
        }

        let mut def_final = vec![false; defs.len()];
        let mut data_final = vec![false; datas.len()];
        let (mut next_def, mut next_data_group) = (0, 0);
        loop {
            // Define every group that can be.
            let mut progress = true;
            while progress {
                progress = false;
                for group in groups.iter_mut().filter(|g| !g.done) {
                    let declared = if group.data {
                        group
                            .members
                            .iter()
                            .all(|m| *m < self.kernel.env.datas().len() - base_datas)
                    } else {
                        group.members.iter().all(|m| *m < next_def)
                    };
                    if !declared
                        || !group.needs_defs.iter().all(|d| def_final[*d])
                        || !group.needs_datas.iter().all(|d| data_final[*d])
                    {
                        continue;
                    }
                    if group.data {
                        let members = group
                            .members
                            .iter()
                            .map(|&m| {
                                let data = &datas[m];
                                let ctors = data
                                    .ctors
                                    .iter()
                                    .map(|c| Ctor {
                                        name: c.name.clone(),
                                        fields: c.fields.clone(),
                                        field_sorts: c.field_sorts.clone(),
                                        field_erased: c.field_erased.clone(),
                                        result: c.result.clone(),
                                        implicit: c.implicit.clone(),
                                        braced: c.braced,
                                    })
                                    .collect();
                                (DataId(base_datas + m), ctors)
                            })
                            .collect();
                        self.kernel_op(|g| kernel::admit_trusted_data_group(g, members))
                            .map_err(refused)?;
                        for m in &group.members {
                            data_final[*m] = true;
                            if library {
                                self.bind_builtin_data(DataId(base_datas + m))
                                    .map_err(refused)?;
                            }
                        }
                    } else {
                        let members: Vec<(DefId, Term)> = group
                            .members
                            .iter()
                            .map(|&m| (DefId(base_defs + m), defs[m].body.clone()))
                            .collect();
                        self.kernel_op(|g| kernel::admit_trusted_group(g, &members))
                            .map_err(refused)?;
                        for m in &group.members {
                            def_final[*m] = true;
                            if library {
                                self.bind_builtin_def(DefId(base_defs + m))
                                    .map_err(refused)?;
                            }
                        }
                        for m in &group.members {
                            if let Some(run) = &defs[*m].run_body {
                                self.kernel_op(|g| {
                                    kernel::admit_trusted_run_body(g, DefId(base_defs + m), run)
                                })
                                .map_err(refused)?;
                            }
                        }
                    }
                    group.done = true;
                    progress = true;
                    if let Some(path) = &self.options.refuse_replays_after
                        && group.members.iter().any(|&m| {
                            let declared = if group.data {
                                &datas[m].path
                            } else {
                                &defs[m].path
                            };
                            **declared == **path
                        })
                    {
                        return bad("a test made the kernel refuse it");
                    }
                }
            }
            // Then the next declaration.
            let next_data = data_groups
                .get(next_data_group)
                .map(|&gi| groups[gi].members[0]);
            if let Some(j) = next_data
                && datas[j].defs_before == next_def
            {
                let gi = data_groups[next_data_group];
                let first = &datas[j];
                for &m in &groups[gi].members {
                    module_of(&datas[m].name, &datas[m].path)?;
                }
                let members = groups[gi]
                    .members
                    .iter()
                    .map(|&m| kernel::DataDecl {
                        name: datas[m].name.clone(),
                        path: datas[m].path.clone(),
                        span: datas[m].span,
                        record: datas[m].record,
                        indices: datas[m].indices.clone(),
                    })
                    .collect();
                let (params, sort) = (first.params.clone(), first.sort);
                let ids = self
                    .kernel_op(|g| kernel::admit_trusted_data_decls(g, params, sort, members))
                    .map_err(refused)?;
                for (&m, id) in groups[gi].members.iter().zip(&ids) {
                    let data = &datas[m];
                    if id.0 != base_datas + m || *self.kernel.data(*id).path() != data.path {
                        return bad("a data type came out differently");
                    }
                    if data.params.len() != first.params.len() || data.sort != first.sort {
                        return bad("a data group's members disagree");
                    }
                    if !data.auto_params.is_empty() {
                        kernel::mark_auto_params(&mut self.kernel, *id, data.auto_params.clone());
                    }
                    if data.no_eta {
                        kernel::mark_no_eta(&mut self.kernel, *id);
                    }
                }
                next_data_group += 1;
                continue;
            }
            if next_def < defs.len() {
                let def = &defs[next_def];
                module_of(&def.name, &def.path)?;
                let id = self
                    .kernel_op(|g| {
                        kernel::admit_trusted_def(
                            g,
                            &def.name,
                            &def.path,
                            &def.ty,
                            def.theorem,
                            def.span,
                        )
                    })
                    .map_err(refused)?;
                if id.0 != base_defs + next_def || *self.kernel.def(id).path() != def.path {
                    return bad("a definition came out differently");
                }
                if def.fold {
                    kernel::mark_folded(&mut self.kernel, id);
                }
                if def.instance {
                    kernel::mark_instance(&mut self.kernel, id);
                }
                if def.opaque {
                    kernel::mark_opaque(&mut self.kernel, id);
                }
                if def.tailrec {
                    kernel::mark_tailrec(&mut self.kernel, id);
                }
                if param_defaults.contains(&id) {
                    kernel::mark_param_default(&mut self.kernel, id);
                }
                if !def.unfolding.is_empty() {
                    kernel::set_unfolding(&mut self.kernel, id, &def.unfolding);
                }
                next_def += 1;
                continue;
            }
            break;
        }
        if groups.iter().any(|g| !g.done) || next_data_group < data_groups.len() {
            return bad("some declarations could never be defined");
        }
        Ok(())
    }

    /// What [`Self::admit_replayed`] compares before and after an undo: the
    /// kernel's bindings, and with `declarations` its definitions and data
    /// types as the canonical dump prints them.
    fn undo_witness(&self, declarations: bool) -> String {
        let mut out = self.kernel.bindings_dump();
        if declarations {
            dump::declarations(&self.ev(), &mut out);
        }
        out
    }

    /// Runs one kernel call as its own operation, with its own resource
    /// limits, as elaborating each component does.
    fn kernel_op<T>(&mut self, f: impl FnOnce(&mut Kernel) -> T) -> T {
        let saved = self.kernel.machine.budget.start(self.options.limits);
        let result = f(&mut self.kernel);
        self.kernel.machine.budget.restore(saved);
        result
    }

    /// Puts an entry's side tables in place, through the same insertion
    /// functions elaboration uses, once its declarations are admitted.
    /// `early` are the names a namespace declared before its library files
    /// loaded, already there (`replay_namespace`), which now get what they
    /// name.
    fn replay_tables(&mut self, t: Rest, early: &[(String, Span, bool)]) {
        // The abilities first: a name may be one.
        self.tables.replay(t.tables, &self.session.owners);
        let ability = |e: &Elaborator, op_data: DataId| {
            e.tables
                .abilities
                .iter()
                .position(|a| a.op_data == op_data)
                .expect("checked when read (`replay`)")
        };
        let global = |e: &Elaborator, g: GlobalEntry| match g {
            GlobalEntry::Plain(g) => g,
            GlobalEntry::Ability(d) => Global::Ability(ability(e, d)),
            GlobalEntry::Op(d, j) => Global::Op(ability(e, d), j),
        };
        for (key, g, span) in t.changed {
            let g = global(self, g);
            self.scope.insert(&key, g, span, false);
        }
        for (key, g, span, follower) in t.new {
            let g = global(self, g);
            self.scope.insert(&key, g, span, follower);
        }
        for ((key, span, follower), g) in early.iter().zip(t.early) {
            let g = global(self, g);
            self.scope.insert(key, g, *span, *follower);
        }
        for key in t.members {
            self.scope.mark_member(&key);
        }
        for (key, target) in t.extensions {
            self.scope.add_extension(&key, &target);
        }
        if let (Some(nav), Some(entry)) = (&self.present.nav, t.nav) {
            for (at, key, target, g, dot) in entry.refs {
                let global = global(self, g);
                let target = match target {
                    Target::Span(span) => span,
                    Target::Key => {
                        self.scope
                            .get(&key)
                            .expect("checked when read (`decode`)")
                            .1
                    }
                };
                self.note(
                    at,
                    Noted {
                        key,
                        target,
                        global,
                        dot,
                    },
                );
            }
            let mut nav = nav.borrow_mut();
            for (at, ty) in entry.exprs {
                nav.expr_types.insert(at, ty);
            }
            for (at, ty) in entry.expr_unfolded {
                nav.expr_unfolded.insert(at, ty);
            }
            for (at, used) in entry.call_defaults {
                nav.call_defaults.insert(at, used);
            }
            for (at, ty) in entry.local_types {
                nav.local_types.insert((at.file, at.start), ty);
            }
            for (at, ty) in entry.local_unfolded {
                nav.local_unfolded.insert((at.file, at.start), ty);
            }
            for (span, name, binder) in entry.locals {
                nav.locals.push(LocalUse { span, name, binder });
            }
            for (span, name, binder) in entry.binders {
                nav.binders.push(LocalUse { span, name, binder });
            }
            nav.params.extend(entry.params);
            nav.named.extend(entry.named);
            for (at, name, span) in entry.fields {
                nav.field_spans.insert((at, name), span);
            }
        }
    }
}

/// The module a declaration was declared in, from its name and its path
/// (`Std` for `List.length` at `Std.List.length`): a path that isn't its
/// name in a module is refused.
fn module_of(name: &str, path: &str) -> Read<Name> {
    if path == name {
        return Ok("".into());
    }
    match path.strip_suffix(name).and_then(|m| m.strip_suffix('.')) {
        Some(module) if !module.is_empty() => Ok(module.into()),
        _ => bad(format!("`{path}` isn't `{name}` in a module")),
    }
}

/// A warning, as `encode` writes it.
fn read_warning(b: &mut Body) -> Read<Diagnostic> {
    let mut d = Diagnostic::warning(static_code(&b.string()?), b.string()?);
    let k = b.count()?;
    for _ in 0..k {
        d.labels.push(Label {
            span: b.span()?,
            message: b.string()?,
        });
    }
    let k = b.count()?;
    for _ in 0..k {
        d.notes.push(b.string()?);
    }
    Ok(d)
}

/// The side tables of an entry, read; any ability a name refers to must
/// be one known after replay.
fn read_tables(b: &mut Body, files: usize, early: usize) -> Read<Rest> {
    let mut t = Rest {
        changed: Vec::new(),
        new: Vec::new(),
        early: Vec::new(),
        members: Vec::new(),
        tables: state::TablesDelta::default(),
        extensions: Vec::new(),
        nav: None,
    };
    let n = b.count()?;
    for _ in 0..n {
        t.changed.push((b.string()?, b.global(files)?, b.span()?));
    }
    let n = b.count()?;
    for _ in 0..n {
        t.new
            .push((b.string()?, b.global(files)?, b.span()?, b.r.bool()?));
    }
    for _ in 0..early {
        t.early.push(b.global(files)?);
    }
    let n = b.count()?;
    for _ in 0..n {
        t.members.push(b.string()?);
    }
    t.tables = state::Tables::decode(b, |b| {
        let n = b.count()?;
        for _ in 0..n {
            t.extensions.push((b.string()?, b.string()?));
        }
        Ok(())
    })?;
    if b.r.bool()? {
        let mut nav = NavEntry {
            refs: Vec::new(),
            exprs: Vec::new(),
            expr_unfolded: Vec::new(),
            call_defaults: Vec::new(),
            local_types: Vec::new(),
            local_unfolded: Vec::new(),
            locals: Vec::new(),
            binders: Vec::new(),
            params: Vec::new(),
            named: Vec::new(),
            fields: Vec::new(),
        };
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            let at = b.span_after(&mut prev)?;
            let key = b.string()?;
            let target = if b.r.bool()? {
                Target::Key
            } else {
                Target::Span(b.span_after(&mut at.start.clone())?)
            };
            let global = b.global(files)?;
            let dot = if b.r.bool()? { Some(b.string()?) } else { None };
            nav.refs.push((at, key, target, global, dot));
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            nav.exprs.push((b.span_after(&mut prev)?, b.string()?));
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            nav.expr_unfolded
                .push((b.span_after(&mut prev)?, b.string()?));
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            nav.call_defaults
                .push((b.span_after(&mut prev)?, b.string()?));
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            nav.local_types
                .push((b.span_after(&mut prev)?, b.string()?));
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            nav.local_unfolded
                .push((b.span_after(&mut prev)?, b.string()?));
        }
        for uses in [&mut nav.locals, &mut nav.binders] {
            let n = b.count()?;
            let mut prev = 0;
            for _ in 0..n {
                let span = b.span_after(&mut prev)?;
                let name = b.string()?;
                let binder = b.span_after(&mut span.start.clone())?;
                uses.push((span, name, binder));
            }
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            let owner = b.span_after(&mut prev)?;
            let name = b.string()?;
            let binder = b.span_after(&mut owner.start.clone())?;
            nav.params.push(ParamBinder {
                owner,
                name,
                binder,
            });
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            let span = b.span_after(&mut prev)?;
            let name = b.string()?;
            let head = [
                b.span_after(&mut span.start.clone())?,
                b.span_after(&mut span.start.clone())?,
            ];
            nav.named.push(NamedUse { head, name, span });
        }
        let n = b.count()?;
        let mut prev = 0;
        for _ in 0..n {
            let at = b.span_after(&mut prev)?;
            let name = b.string()?;
            let span = b.span_after(&mut at.start.clone())?;
            nav.fields.push((at, name, span));
        }
        t.nav = Some(nav);
    }
    Ok(t)
}

#[doc(hidden)]
pub use dump::canonical_dump;

#[cfg(test)]
mod tests {
    use stitchwort_core::registry::Builtin;

    use super::state;
    use crate::Elaborator;

    /// A namespace's entry that says it binds built-ins is refused before
    /// anything reaches the kernel (only a library file's declarations are
    /// bound), and is counted.
    #[test]
    fn a_namespace_entry_that_binds_builtins_is_refused_before_anything_is_admitted() {
        let mut e = Elaborator::new();
        let before = e.kernel.bindings_dump();
        let result = e.admit_replayed(
            &[],
            &[],
            &[(0, 0, Builtin::Nat)],
            &state::TablesDelta::default(),
            false,
        );
        assert!(result.is_err(), "the entry was admitted");
        assert_eq!(e.session.cache_stats.refused, 1);
        assert_eq!(e.kernel.bindings_dump(), before, "something was admitted");
    }
}
