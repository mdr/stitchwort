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
//! - **Loading is replay** (§5.2): the declarations go to the kernel through
//!   the same `declare_*`/`define_*` functions the elaborator uses, so the
//!   kernel checks every one again (option A, D277). Only elaboration is
//!   skipped. `Elaborator::admit_replayed` is the one place that submits
//!   them.
//! - **The key** (§4.2) is computed before anything is elaborated: the
//!   compiler build, the format, the modes and limits that change results,
//!   and the unit's text. For a library file: its path and text (and the
//!   core's), and the keys of the library files it needs. For a project
//!   namespace: the hash of its sources the host gives
//!   ([`Elaborator::set_namespace_sources`]: its files' names and text, the
//!   project's namespaces and `stitchwort.yaml`), the whole library's text,
//!   and the keys of the namespaces it depends on (a Merkle chain). The
//!   files it `include`s are listed in its entry with a hash of their
//!   text, and read again to check them.
//! - **An entry that doesn't fit is a miss**: a corrupt one (checksum), one
//!   for another key or cache directory (salt), one whose dependencies don't
//!   have the expected hashes, or one the kernel refuses (whose effects are
//!   undone). The unit is then elaborated, and the entry rewritten. Only
//!   units without errors are written (D284).
//!
//! This module only encodes and replays. Where entries are kept is the
//! [`Store`] a host gives the elaborator (the CLI's is a directory).

mod codec;
mod dump;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::kernel;
use stitchwort_core::globals::State;
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::native::Native;
use stitchwort_core::registry::{Builtin, Home, Kind};
use stitchwort_core::{DataId, DefId, Globals, Name, Sort, Term};
use stitchwort_syntax::{FileId, Span};

use crate::effects::AbilityInfo;
use crate::interfaces::{InstanceInfo, InstanceParam, InterfaceInfo};
use crate::library::{Needs, PendingKind};
use crate::nav::{LocalUse, Noted};
use crate::project::SourceUnit;
use crate::records::RecordInfo;
use crate::scope::ScopeOp;
use crate::{Elaborator, Global};
use codec::{Bad, Read, ReadRefs, Reader, Refs, TermWriter, Terms, Writer, bad};
use stitchwort_syntax::{Diagnostic, Label, Severity};

/// The version of the entry format, part of every key: a change to what an
/// entry holds or how it is written bumps it, and old entries are misses.
pub const FORMAT: u32 = 4;

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
    /// Namespace entries found not to fit after their replay had begun
    /// (loading the library files they need): the namespace is then
    /// elaborated in what the replay left. Never expected; the differential
    /// test checks there are none.
    pub late_misses: usize,
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
    /// Before anything: the names there were, and the members marked.
    start_keys: HashSet<String>,
    start_members: HashSet<String>,
    /// The names the namespace declared before its library files loaded
    /// (`collect`), and what it needs from the library.
    early: Option<Vec<String>>,
    needs: Option<Needs>,
    /// Once its library files have loaded: what it is compared against,
    /// and how many library files had loaded.
    before: Option<Before>,
    library_loaded: usize,
}

/// What a library file's load is compared against, to see what it added.
pub(crate) struct Before {
    defs: usize,
    datas: usize,
    abilities: usize,
    lifted: usize,
    tests: usize,
    scope: HashMap<String, (Global, Span)>,
    instances: HashMap<(DataId, DataId), (DefId, bool)>,
    helper_keys: HashSet<String>,
    /// The sizes of the tables keyed by data type (`by_data`).
    by_data: Vec<usize>,
    nav: Option<(usize, usize, usize)>,
}

impl Elaborator {
    /// Keeps library files' results in `store` between runs, and loads them
    /// from it (see [`crate::cache`]).
    pub fn set_check_cache(&mut self, store: Rc<dyn Store>) {
        self.check_cache = Some(store);
    }

    /// What the cache has done so far.
    pub fn check_cache_stats(&self) -> Stats {
        self.cache_stats
    }

    /// For tests: every namespace replay from now on fails where a
    /// dependency that isn't what the entry was made with would make it
    /// fail (a late miss), so the namespace is elaborated after all.
    #[doc(hidden)]
    pub fn fail_namespace_replays_late(&mut self) {
        self.fail_replays_late = true;
    }

    /// Whether library files may be loaded from, and written to, the cache
    /// now. Not for the library test target, whose tests are part of the
    /// result. (A session whose core isn't the index's finds its entries'
    /// dependencies have other hashes: misses.)
    fn cache_usable(&self) -> bool {
        self.check_cache.is_some() && !self.library_tests
    }

    /// The name of the unit an entry is for: the library file, and whether
    /// navigation is recorded (an entry made without it can't give it).
    fn cache_unit(&self, f: usize) -> String {
        let index = self.library_index().expect("a library is installed");
        let path = index.files[f]
            .path
            .trim_end_matches(".sw")
            .replace('/', ".");
        let nav = if self.nav.is_some() { "+nav" } else { "" };
        format!("std.{path}{nav}")
    }

    /// The key of library file `f` (§4.2), and of the files it needs.
    pub(crate) fn library_key(&self, f: usize) -> Key {
        let index = self.library_index().expect("a library is installed");
        let store = self.check_cache.as_ref().expect("a cache is set");
        let mut keys: HashMap<usize, Key> = HashMap::new();
        // Dependencies first: the edges never form a cycle (the index is
        // checked), so a work list in post-order ends.
        let mut stack = vec![(f, false)];
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
            part(index.files[0].text.as_bytes());
            part(index.files[file].path.as_bytes());
            part(index.files[file].text.as_bytes());
            for e in &index.files[file].edges {
                part(&keys[e]);
            }
            keys.insert(file, *h.finalize().as_bytes());
        }
        keys[&f]
    }

    /// Everything else that changes what elaborating a library file gives.
    fn modes(&self) -> String {
        let g = &self.globals;
        let l = self.limits;
        format!(
            "natives {} compact {} succ {} limits {} {} {} {} rewrite {:?} instances {:?} uniform {} nav {}",
            !g.builtins.disable_natives,
            g.builtins.compact_literals().is_some(),
            self.numbers_as_succ,
            l.work,
            l.stack,
            l.size,
            l.frames,
            self.rewrite_budget,
            self.instance_budget,
            self.uniform_operators,
            self.nav.is_some(),
        )
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
        let store = self.check_cache.clone().expect("a cache is set");
        let Some(bytes) = store.read(unit, key) else {
            self.cache_stats.misses += 1;
            return false;
        };
        match self.replay(&bytes, key, store.salt()) {
            Ok(()) => {
                self.cache_stats.hits += 1;
                true
            }
            Err(Bad(why)) => {
                debug(&format!("std file {f}: a miss: {why}"));
                self.cache_stats.misses += 1;
                false
            }
        }
    }

    /// What to compare with once library file `f` has loaded, to see what
    /// it added; and starts noting the names it declares.
    pub(crate) fn cache_before(&mut self) -> Before {
        self.scope.log = Some(Vec::new());
        self.snapshot()
    }

    /// What a unit's load is compared against.
    fn snapshot(&self) -> Before {
        Before {
            defs: self.globals.defs.len(),
            datas: self.globals.datas.len(),
            abilities: self.abilities.len(),
            lifted: self.lifted.len(),
            tests: self.tests.len(),
            scope: self.scope.entries.clone(),
            instances: self
                .instances
                .iter()
                .map(|(k, v)| (*k, (v.def, v.valid)))
                .collect(),
            helper_keys: self.helper_keys.clone(),
            by_data: self.by_data().iter().map(|t| t.len()).collect(),
            nav: self.nav.as_ref().map(|nav| {
                let nav = nav.borrow();
                (nav.locals.len(), nav.binders.len(), nav.outline.len())
            }),
        }
    }

    /// The side tables keyed by data type, as `(data type, row)` lists:
    /// records, interfaces, owners, and why `==`, `show` and `compare`
    /// aren't derived. Loading a file only adds rows for its own types.
    fn by_data(&self) -> Vec<Vec<DataId>> {
        vec![
            self.records.keys().copied().collect(),
            self.interfaces.keys().copied().collect(),
            self.data_owners.keys().copied().collect(),
            self.no_eq.keys().copied().collect(),
            self.no_show.keys().copied().collect(),
            self.no_ord.keys().copied().collect(),
        ]
    }

    /// After library file `f` loaded: writes its entry, if it checked and
    /// can be cached.
    pub(crate) fn cache_after(
        &mut self,
        f: usize,
        before: Before,
        ok: bool,
        unit: &str,
        key: &Key,
    ) {
        let log = self.scope.log.take().unwrap_or_default();
        // A cancelled check isn't a result, even where it reported nothing.
        if !ok || self.globals.budget.cancelled() {
            return;
        }
        let store = self.check_cache.clone().expect("a cache is set");
        let entry = self.encode_library_file(f, &before, &log, key, store.salt());
        if let Err(why) = &entry {
            debug(&format!("std file {f} can't be cached: {why}"));
        }
        match entry {
            Ok(entry) => {
                store.write(unit, key, &entry);
                self.cache_stats.written += 1;
            }
            Err(_why) => self.cache_stats.uncacheable += 1,
        }
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
        self.namespace_sources = sources;
    }

    /// Whether this elaborator keeps results in a check cache.
    pub fn uses_check_cache(&self) -> bool {
        self.cache_usable()
    }

    /// A hash of every library file's path and text: a namespace may use
    /// any of them.
    fn library_digest(&self) -> Key {
        *self.library_digest.get_or_init(|| {
            let mut h = blake3::Hasher::new();
            if let Some(index) = self.library_index() {
                for file in &index.files {
                    for part in [file.path.as_bytes(), file.text.as_bytes()] {
                        h.update(&(part.len() as u64).to_le_bytes());
                        h.update(part);
                    }
                }
            }
            *h.finalize().as_bytes()
        })
    }

    /// The unit and key of project namespace `namespace`, about to be
    /// elaborated with the namespaces `closure` before it, if it may come
    /// from the cache: every namespace it depends on has a key.
    pub(crate) fn namespace_cache_key(
        &self,
        namespace: Option<&str>,
        closure: Option<&[String]>,
    ) -> Option<(String, Key)> {
        if !self.cache_usable() || self.loading_prelude || !self.library_stack_is_empty() {
            return None;
        }
        let (Some(ns), Some(closure)) = (namespace, closure) else {
            return None;
        };
        let source = self.namespace_sources.get(ns)?;
        let store = self.check_cache.as_ref()?;
        let library = self.library_digest();
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
            part(self.namespace_keys.get(dependency)?);
        }
        let nav = if self.nav.is_some() { "+nav" } else { "" };
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
        self.namespace_keys.insert(ns.to_string(), *key);
        let store = self.check_cache.clone().expect("a cache is set");
        let start_keys: HashSet<String> = self.scope.entries.keys().cloned().collect();
        let start_members = self.scope.members().clone();
        if stitchwort_core::registry::check_complete_core(&self.globals).is_ok()
            && let Some(bytes) = store.read(unit, key)
        {
            match self.replay_namespace(ns, files, closure, &bytes, key, store.salt()) {
                Ok(warnings) => {
                    self.replayed_names.clear();
                    self.cache_stats.namespace_hits += 1;
                    return (warnings, true);
                }
                Err(Miss::Early(why)) => debug(&format!("{ns}: a miss: {why}")),
                Err(Miss::Late(why)) => {
                    debug(&format!("{ns}: a miss after the replay began: {why}"));
                    self.cache_stats.late_misses += 1;
                    // Its files were walked already.
                    self.skip_navigation_walk = true;
                }
            }
        }
        self.cache_stats.namespace_misses += 1;
        self.include_trace.borrow_mut().clear();
        self.namespace_capture = Some(Capture {
            start_keys,
            start_members,
            early: None,
            needs: None,
            before: None,
            library_loaded: 0,
        });
        let diagnostics = self.elaborate_namespace_untimed(Some(ns), files, Some(closure));
        let capture = self.namespace_capture.take();
        self.skip_navigation_walk = false;
        let ok = !diagnostics.iter().any(|d| d.severity == Severity::Error)
            && !self.globals.budget.cancelled();
        if ok && let Some(capture) = capture {
            match self.encode_namespace(files, capture, &diagnostics, key, store.salt()) {
                Ok(entry) => {
                    store.write(unit, key, &entry);
                    self.cache_stats.namespace_written += 1;
                }
                Err(why) => {
                    debug(&format!("{ns} can't be cached: {why}"));
                    self.cache_stats.namespace_uncacheable += 1;
                }
            }
        }
        (diagnostics, false)
    }

    /// While a namespace that may be cached is elaborated: the names it has
    /// collected, before its library files load, and what it needs.
    pub(crate) fn capture_before_needs(&mut self, needs: &Needs) {
        if self.loading_prelude {
            return;
        }
        let Some(c) = &self.namespace_capture else {
            return;
        };
        if c.early.is_some() {
            return;
        }
        let early: Vec<String> = self
            .scope
            .entries
            .keys()
            .filter(|k| !c.start_keys.contains(*k))
            .cloned()
            .collect();
        let c = self.namespace_capture.as_mut().expect("checked above");
        c.early = Some(early);
        c.needs = Some(needs.clone());
    }

    /// Then, once its library files have loaded: what its entry is worked
    /// out against.
    pub(crate) fn capture_after_needs(&mut self) {
        if self.loading_prelude
            || self
                .namespace_capture
                .as_ref()
                .is_none_or(|c| c.before.is_some())
        {
            return;
        }
        let before = self.snapshot();
        let loaded = self.loaded_library_files().len();
        let c = self.namespace_capture.as_mut().expect("checked above");
        c.before = Some(before);
        c.library_loaded = loaded;
    }

    /// The names entries give the files a namespace's entry may refer to:
    /// the library's and the project's.
    fn namespace_file_names(&self) -> HashMap<FileId, String> {
        let mut names = self.std_file_names();
        for (id, path) in &self.include_locations {
            names.insert(*id, project_file_name(path));
        }
        names
    }

    /// The entry for the namespace just elaborated without errors from
    /// `files`, or why it can't be cached (see [`Self::encode`]).
    fn encode_namespace(
        &self,
        files: &[SourceUnit],
        capture: Capture,
        warnings: &[Diagnostic],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let (Some(before), Some(early), Some(needs)) =
            (capture.before, capture.early, capture.needs)
        else {
            return Err("checking stopped early".to_string());
        };
        if self.loaded_library_files().len() != capture.library_loaded {
            return Err("a library file loaded part way through".to_string());
        }
        // The names: each new one is added after those of its short name
        // that were added before it (the followers' order).
        let early_keys: HashSet<&str> = early.iter().map(String::as_str).collect();
        let mut changed = Vec::new();
        for (k, old) in &before.scope {
            if early_keys.contains(k.as_str()) {
                continue;
            }
            match self.scope.entries.get(k) {
                Some(now) if now == old => {}
                Some(_) => changed.push(k.clone()),
                None => return Err(format!("`{k}` was removed")),
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
        let mut early = early;
        early.sort_by_key(order);
        let mut late: Vec<String> = self
            .scope
            .entries
            .keys()
            .filter(|k| !before.scope.contains_key(*k))
            .cloned()
            .collect();
        late.sort_by_key(order);
        let mut members: Vec<String> = self
            .scope
            .members()
            .iter()
            .filter(|k| !capture.start_members.contains(*k))
            .cloned()
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
            includes: self.include_trace.borrow().clone(),
        };
        let unit = UnitOut {
            file_names: self.namespace_file_names(),
            own_files: files.iter().filter_map(|f| f.file).collect(),
            library: false,
        };
        if unit.own_files.len() != files.len() {
            return Err("a file without an id".to_string());
        }
        self.encode(&unit, &before, &names, &pre, warnings, key, salt)
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
        // The files it included must be as they were.
        for (path, hash) in &head.pre.includes {
            let same = self
                .include_files
                .as_ref()
                .and_then(|files| files.read(path).ok())
                .is_some_and(|text| blake3::hash(text.as_bytes()).as_bytes() == hash);
            if !same {
                return Err(Miss::Early(format!("the included `{path}` changed")));
            }
        }

        // From here on, as `elaborate_namespace_untimed` does.
        self.namespace_root = format!("{ns}.");
        self.globals.module = "".into();
        self.module = crate::module::ModuleState {
            files: files
                .iter()
                .map(|f| crate::module::FileInfo {
                    id: f.file,
                    name: f.name.to_string(),
                })
                .collect(),
            namespace: Some(ns.to_string()),
            closure: Some(closure.to_vec()),
            first_def: self.globals.defs.len(),
            first_test: self.tests.len(),
            ..crate::module::ModuleState::default()
        };
        self.scope.clear_imports();
        self.walk_for_navigation(&files.iter().map(|f| f.module).collect::<Vec<_>>());
        let pre = std::mem::take(&mut head.pre);
        for (k, span, follower) in &pre.early {
            self.scope.insert(k, Global::Failed, *span, *follower);
        }
        // If replay fails from here on, elaborating the namespace declares
        // these again where they are (`taken`).
        self.replayed_names = pre.early.iter().map(|(k, _, _)| k.clone()).collect();
        if !pre.needs.files.is_empty() || !pre.needs.dots.is_empty() {
            self.load_needs(&pre.needs).map_err(|ds| {
                Miss::Late(format!(
                    "its library files don't load: {}",
                    ds.first().map_or("", |d| d.message.as_str())
                ))
            })?;
        }
        if self.fail_replays_late {
            return Err(Miss::Late("a test made it fail".to_string()));
        }
        let mut d = self.decode(&deps, head, &pre.early).map_err(late)?;
        let warnings = std::mem::take(&mut d.tables.warnings);
        let base_defs = self.globals.defs.len();
        self.admit_replayed(&d.defs, &d.datas, &d.bound)
            .map_err(late)?;
        self.replay_tables(d.tables, &pre.early);
        self.namespace_defs
            .insert(ns.to_string(), base_defs..self.globals.defs.len());
        Ok(warnings)
    }
}

// ---- Writing --------------------------------------------------------------

/// How an entry refers to declarations and files while it is written.
struct Out<'g> {
    g: &'g Globals,
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
    def_paths: HashMap<&'g str, usize>,
    data_paths: HashMap<&'g str, usize>,
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
                self.fail(format!("`{}` has no content hash", def.path));
                ContentHash([0; 32])
            }
        };
        if self.def_paths.get(&*def.path) != Some(&1) {
            self.fail(format!("`{}` names more than one definition", def.path));
        }
        let i = self.deps.len();
        self.deps.push((0, def.path.to_string(), hash));
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
                self.fail(format!("`{}` has no content hash", data.path));
                ContentHash([0; 32])
            }
        };
        if self.data_paths.get(&*data.path) != Some(&1) {
            self.fail(format!("`{}` names more than one data type", data.path));
        }
        let i = self.deps.len();
        self.deps.push((1, data.path.to_string(), hash));
        self.ext_datas.insert(id, i);
        w.uint(((i as u64) << 1) | 1);
    }

    fn span(&mut self, w: &mut Writer, span: Span) {
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
        w.usize(file);
        w.uint(u64::from(span.start));
        w.uint(u64::from(span.end.saturating_sub(span.start)));
    }
}

/// An entry's parts while it is written: the terms and strings, and the
/// rest.
struct Encoding<'g> {
    out: Out<'g>,
    terms: TermWriter,
    w: Writer,
}

impl Encoding<'_> {
    fn str(&mut self, s: &str) {
        let i = self.terms.string(s);
        self.w.uint(u64::from(i));
    }

    fn term(&mut self, t: &Term) {
        match self.terms.term(&mut self.out, t) {
            Ok(id) => self.w.uint(u64::from(id)),
            Err(_) => self.out.fail("a term with a metavariable".to_string()),
        }
    }

    fn def(&mut self, id: DefId) {
        self.out.def(&mut self.w, id);
    }

    fn data(&mut self, id: DataId) {
        self.out.data(&mut self.w, id);
    }

    fn span(&mut self, span: Span) {
        self.out.span(&mut self.w, span);
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
                self.data(e.abilities[i].op_data);
            }
            Global::Op(i, j) => {
                self.w.u8(4);
                self.data(e.abilities[i].op_data);
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
fn bound_builtins(g: &Globals, defs: usize, datas: usize) -> Vec<(u8, usize, Builtin)> {
    let missing = g.registry.missing();
    let mut out: Vec<(u8, usize, Builtin)> = Builtin::ALL
        .iter()
        .copied()
        .filter(|b| !missing.contains(b))
        .filter_map(|b| match b.kind() {
            Kind::Def => g
                .registry
                .def(b)
                .filter(|id| id.0 >= defs)
                .map(|id| (0, id.0 - defs, b)),
            Kind::Data => g
                .registry
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

/// The operators a test's sides can have (`TestSides::op`).
const TEST_OPS: [&str; 7] = ["==", "!=", "=", "<", "<=", ">", ">="];

/// A diagnostic's code, as the `'static` text `Diagnostic` holds: the
/// codes read from entries are kept once each.
fn static_code(code: &str) -> &'static str {
    use std::sync::{Mutex, OnceLock};
    static CODES: OnceLock<Mutex<HashSet<&'static str>>> = OnceLock::new();
    let mut codes = CODES
        .get_or_init(|| Mutex::new(HashSet::new()))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(&c) = codes.get(code) {
        return c;
    }
    let c: &'static str = Box::leak(code.to_string().into_boxed_str());
    codes.insert(c);
    c
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
        before: &Before,
        log: &[ScopeOp],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let index = self.library_index().expect("a library is installed");
        // The names: those that changed, then the new ones in the order
        // they were declared, then the members marked.
        let mut changed: Vec<String> = self
            .scope
            .entries
            .iter()
            .filter(|(k, v)| before.scope.get(*k).is_some_and(|old| old != *v))
            .map(|(k, _)| k.clone())
            .collect();
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
            own_files: HashSet::from([index.files[f].id]),
            library: true,
        };
        self.encode(&unit, before, &names, &PreOut::default(), &[], key, salt)
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
        names: &NamesOut,
        pre: &PreOut,
        warnings: &[Diagnostic],
        key: &Key,
        salt: [u8; 16],
    ) -> Result<Vec<u8>, String> {
        let g = &self.globals;
        let _op = g.budget.operation(self.limits);
        let (defs, datas) = (before.defs..g.defs.len(), before.datas..g.datas.len());
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            if def.state() != State::Final || def.body().is_none() {
                return Err(format!("`{}` isn't admitted with a body", def.path));
            }
            if def.export || !def.validators.is_empty() {
                return Err(format!("`{}` is exported", def.path));
            }
            if g.builtins.primitive(id).is_some() {
                return Err(format!("`{}` is a primitive", def.path));
            }
            // Replay declares it again under its module.
            module_of(&def.name, &def.path).map_err(|Bad(why)| why)?;
        }
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            if data.state() != State::Final || !data.validators.is_empty() {
                return Err(format!("`{}` isn't admitted plainly", data.path));
            }
            module_of(&data.name, &data.path).map_err(|Bad(why)| why)?;
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
        let tests = &self.tests[before.tests..];
        if tests.iter().any(|t| t.library) || (unit.library && !tests.is_empty()) {
            return Err("a library test was kept".to_string());
        }
        let old_rows = self
            .by_data()
            .iter()
            .map(|t| t.iter().filter(|d| d.0 < before.datas).count())
            .collect::<Vec<_>>();
        if old_rows != before.by_data {
            return Err("a row for an older data type changed".to_string());
        }
        if self.instances.iter().any(|(k, v)| {
            before
                .instances
                .get(k)
                .is_some_and(|old| *old != (v.def, v.valid))
        }) {
            return Err("an instance from before changed".to_string());
        }

        let mut def_paths: HashMap<&str, usize> = HashMap::new();
        for def in &g.defs {
            *def_paths.entry(&def.path).or_default() += 1;
        }
        let mut data_paths: HashMap<&str, usize> = HashMap::new();
        for data in &g.datas {
            *data_paths.entry(&data.path).or_default() += 1;
        }
        let mut e = Encoding {
            out: Out {
                g,
                base_defs: before.defs,
                base_datas: before.datas,
                ext_defs: HashMap::new(),
                ext_datas: HashMap::new(),
                deps: Vec::new(),
                def_paths,
                data_paths,
                names: unit.file_names.clone(),
                files: Vec::new(),
                file_ids: HashMap::new(),
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
        e.w.usize(pre.includes.len());
        for (path, hash) in &pre.includes {
            e.str(path);
            e.w.raw(hash);
        }
        e.w.usize(names.early.len());
        for (k, follower) in &names.early {
            let Some((_, span)) = self.scope.entries.get(k) else {
                return Err(format!("`{k}` was declared and is gone"));
            };
            e.str(k);
            e.span(*span);
            e.w.bool(*follower);
        }
        let pre_bytes = std::mem::take(&mut e.w.bytes);

        // The kernel's declarations.
        e.w.usize(defs.len());
        for id in defs.clone().map(DefId) {
            let def = g.def(id);
            e.str(&def.name);
            e.str(&def.path);
            e.w.bool(def.theorem);
            e.w.bool(def.instance);
            e.w.bool(def.fold);
            e.span(def.span);
            e.term(&def.ty);
            e.term(def.body().expect("checked above"));
            let group = def.group.as_ref().expect("a final definition has a group");
            e.w.usize(group.len());
            for m in group.iter() {
                if m.0 < before.defs {
                    return Err(format!("`{}`'s group is older", def.path));
                }
                e.w.usize(m.0 - before.defs);
            }
            // What the runtimes run instead, for a definition with `decreasing`.
            e.w.bool(def.own_run_body().is_some());
            if let Some(run) = def.own_run_body() {
                e.term(run);
            }
        }
        e.w.usize(datas.len());
        for d in datas.clone().map(DataId) {
            let data = g.data(d);
            e.str(&data.name);
            e.str(&data.path);
            e.w.usize(data.params.len());
            for (x, ty) in &data.params {
                e.str(x);
                e.term(ty);
            }
            e.w.usize(data.auto_params.len());
            for a in &data.auto_params {
                e.w.bool(*a);
            }
            e.w.usize(data.indices.len());
            for (x, ty) in &data.indices {
                e.str(x);
                e.term(ty);
            }
            codec::sort(&mut e.w, data.sort);
            e.w.usize(data.ctors.len());
            for ctor in &data.ctors {
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
                e.w.usize(ctor.result.len());
                for r in &ctor.result {
                    e.term(r);
                }
            }
            e.w.bool(data.record);
            e.w.usize(data.group.len());
            for m in data.group.iter() {
                if m.0 < before.datas {
                    return Err(format!("`{}`'s group is older", data.path));
                }
                e.w.usize(m.0 - before.datas);
            }
            if data.defs_before < before.defs || data.datas_before < before.datas {
                return Err(format!("`{}` is declared before the file", data.path));
            }
            e.w.usize(data.defs_before - before.defs);
            e.w.usize(data.datas_before - before.datas);
            e.span(data.span);
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
                .entries
                .get(k)
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

        // The elaborator's tables.
        let new_data = |d: &DataId| d.0 >= before.datas;
        let mut records: Vec<(&DataId, &RecordInfo)> =
            self.records.iter().filter(|(d, _)| new_data(d)).collect();
        records.sort_by_key(|(d, _)| d.0);
        e.w.usize(records.len());
        for (d, info) in records {
            e.data(*d);
            e.w.usize(info.projections.len());
            for p in &info.projections {
                e.w.bool(p.is_some());
                if let Some(p) = p {
                    e.def(*p);
                }
            }
        }
        let mut interfaces: Vec<(&DataId, &InterfaceInfo)> = self
            .interfaces
            .iter()
            .filter(|(d, _)| new_data(d))
            .collect();
        interfaces.sort_by_key(|(d, _)| d.0);
        e.w.usize(interfaces.len());
        for (d, info) in interfaces {
            e.data(*d);
            e.str(&info.dict);
            e.w.usize(info.supers.len());
            for (i, s) in &info.supers {
                e.w.usize(*i);
                e.data(*s);
            }
            e.w.usize(info.projections.len());
            for p in &info.projections {
                e.def(*p);
            }
            e.w.usize(info.methods.len());
            for m in &info.methods {
                e.def(*m);
            }
            e.w.usize(info.relations.len());
            for (r, d) in &info.relations {
                e.w.usize(*r);
                e.w.usize(*d);
            }
        }
        let mut instances: Vec<(&(DataId, DataId), &InstanceInfo)> = self
            .instances
            .iter()
            .filter(|(k, _)| !before.instances.contains_key(k))
            .collect();
        instances.sort_by_key(|(k, _)| (k.0.0, k.1.0));
        e.w.usize(instances.len());
        for ((iface, head), info) in instances {
            e.data(*iface);
            e.data(*head);
            e.def(info.def);
            e.str(&info.name);
            e.span(info.span);
            e.w.usize(info.params.len());
            for p in &info.params {
                match p {
                    InstanceParam::Head(k) => {
                        e.w.u8(0);
                        e.w.usize(*k);
                    }
                    InstanceParam::Prerequisite => e.w.u8(1),
                }
            }
            e.w.bool(info.valid);
        }
        for table in [&self.data_owners, &self.no_eq, &self.no_show, &self.no_ord] {
            let mut rows: Vec<(&DataId, &String)> =
                table.iter().filter(|(d, _)| new_data(d)).collect();
            rows.sort_by_key(|(d, _)| d.0);
            e.w.usize(rows.len());
            for (d, s) in rows {
                e.data(*d);
                e.str(s);
            }
        }
        e.w.usize(self.abilities.len() - before.abilities);
        for a in &self.abilities[before.abilities..] {
            e.str(&a.name);
            e.data(a.op_data);
            e.def(a.res);
            e.def(a.elim);
            e.w.usize(a.ops.len());
            for op in &a.ops {
                e.str(op);
            }
            e.w.bool(a.order.0);
            e.str(&a.order.1);
        }
        e.w.usize(self.lifted.len() - before.lifted);
        for (id, span) in &self.lifted[before.lifted..] {
            e.def(*id);
            e.span(*span);
        }
        let mut helpers: Vec<&String> = self.helper_keys.difference(&before.helper_keys).collect();
        helpers.sort();
        e.w.usize(helpers.len());
        for k in helpers {
            e.str(k);
        }

        // The tests, in the order they run.
        e.w.usize(tests.len());
        for t in tests {
            e.str(&t.name);
            e.str(&t.namespace);
            e.def(t.def);
            e.span(t.span);
            match &t.sides {
                None => e.w.bool(false),
                Some(sides) => {
                    e.w.bool(true);
                    e.str(sides.op);
                    e.term(&sides.left);
                    e.term(&sides.right);
                }
            }
        }

        // The warnings, in the order they are reported.
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

        // What code navigation recorded in the unit's files.
        let own = |file: &FileId| unit.own_files.contains(file);
        match (&self.nav, before.nav) {
            (Some(nav), Some((locals, binders, outline))) => {
                let nav = nav.borrow();
                if !nav.pending.is_empty() || nav.outline.len() != outline {
                    return Err("navigation left something unfinished".to_string());
                }
                e.w.bool(true);
                let mut refs: Vec<(&Span, &Noted)> =
                    nav.refs.iter().filter(|(at, _)| own(&at.file)).collect();
                refs.sort_by_key(|(at, _)| (at.file.index(), at.start, at.end));
                e.w.usize(refs.len());
                for (at, noted) in refs {
                    e.span(*at);
                    e.str(&noted.key);
                    // A target in another unit's file is kept by the name
                    // of its declaration, where it is found when the entry
                    // is replayed (§4.3).
                    let by_name = !own(&noted.target.file)
                        && self.scope.get(&noted.key).map(|(_, s)| s) == Some(noted.target);
                    e.w.bool(by_name);
                    if !by_name {
                        e.span(noted.target);
                    }
                    e.global(self, noted.global);
                    e.w.bool(noted.dot.is_some());
                    if let Some(dot) = &noted.dot {
                        e.str(dot);
                    }
                }
                let mut types: Vec<(&(FileId, u32), &String)> = nav
                    .local_types
                    .iter()
                    .filter(|((file, _), _)| own(file))
                    .collect();
                types.sort_by_key(|((file, at), _)| (file.index(), *at));
                e.w.usize(types.len());
                for ((file, at), ty) in types {
                    e.span(Span::new(*file, *at, *at));
                    e.str(ty);
                }
                for uses in [&nav.locals[locals..], &nav.binders[binders..]] {
                    e.w.usize(uses.len());
                    for u in uses {
                        e.span(u.span);
                        e.str(&u.name);
                        e.span(u.binder);
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
                for ((at, name), span) in fields {
                    e.span(*at);
                    e.str(name);
                    e.span(*span);
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
}

/// A definition, read.
struct DefEntry {
    name: Name,
    path: Name,
    theorem: bool,
    instance: bool,
    fold: bool,
    span: Span,
    ty: Term,
    body: Term,
    group: Vec<usize>,
    run_body: Option<Term>,
}

/// A constructor, read.
struct CtorEntry {
    name: Name,
    fields: Vec<(Name, Term)>,
    implicit: Vec<bool>,
    result: Vec<Term>,
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
    group: Vec<usize>,
    defs_before: usize,
    datas_before: usize,
    span: Span,
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
struct Tables {
    changed: Vec<(String, GlobalEntry, Span)>,
    new: Vec<(String, GlobalEntry, Span, bool)>,
    /// What each name declared before the library files loaded names
    /// ([`Pre::early`]), in the same order.
    early: Vec<GlobalEntry>,
    members: Vec<String>,
    records: Vec<(DataId, RecordInfo)>,
    interfaces: Vec<(DataId, InterfaceInfo)>,
    instances: Vec<((DataId, DataId), InstanceInfo)>,
    /// `data_owners`, `no_eq`, `no_show`, `no_ord`.
    by_data: [Vec<(DataId, String)>; 4],
    abilities: Vec<AbilityInfo>,
    lifted: Vec<(DefId, Span)>,
    helper_keys: Vec<String>,
    tests: Vec<TestEntry>,
    warnings: Vec<Diagnostic>,
    nav: Option<NavEntry>,
}

/// A test, read.
struct TestEntry {
    name: String,
    namespace: String,
    def: DefId,
    span: Span,
    sides: Option<(&'static str, Term, Term)>,
}

/// Where a reference leads: a span, or the declaration with that key.
enum Target {
    Span(Span),
    Key,
}

struct NavEntry {
    refs: Vec<(Span, String, Target, GlobalEntry, Option<String>)>,
    local_types: Vec<(Span, String)>,
    locals: Vec<(Span, String, Span)>,
    binders: Vec<(Span, String, Span)>,
    fields: Vec<(Span, String, Span)>,
}

/// An entry's body being read.
struct Body<'a> {
    r: Reader<'a>,
    terms: Terms,
    refs: In,
}

impl Body<'_> {
    fn str(&mut self) -> Read<Name> {
        self.terms.name(&mut self.r)
    }

    fn string(&mut self) -> Read<String> {
        Ok(self.str()?.to_string())
    }

    fn term(&mut self) -> Read<Term> {
        self.terms.term(&mut self.r)
    }

    fn def(&mut self) -> Read<DefId> {
        self.refs.def(&mut self.r)
    }

    fn data(&mut self) -> Read<DataId> {
        self.refs.data(&mut self.r)
    }

    fn span(&mut self) -> Read<Span> {
        self.refs.span(&mut self.r)
    }

    fn count(&mut self) -> Read<usize> {
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

/// Finds a declaration by its path, if exactly one has it.
fn unique<T: Copy>(map: &HashMap<&str, Option<T>>, path: &str) -> Option<T> {
    map.get(path).copied().flatten()
}

/// What a namespace's replay reads before the rest of its entry (empty for
/// a library file): see [`PreOut`].
#[derive(Default)]
struct Pre {
    needs: Needs,
    includes: Vec<(String, Key)>,
    early: Vec<(String, Span, bool)>,
}

impl Pre {
    fn is_empty(&self) -> bool {
        self.needs.files.is_empty()
            && self.needs.dots.is_empty()
            && self.includes.is_empty()
            && self.early.is_empty()
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
    tables: Tables,
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
            pre.includes.push((body.string()?, body.r.array::<32>()?));
        }
        let n = body.count()?;
        for _ in 0..n {
            pre.early
                .push((body.string()?, body.span()?, body.r.bool()?));
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
        let g = &self.globals;
        let _op = g.budget.operation(self.limits);

        // The dependencies: each path names one final declaration, with the
        // hash it had when the entry was written.
        let mut def_paths: HashMap<&str, Option<DefId>> = HashMap::new();
        for (i, def) in g.defs.iter().enumerate() {
            def_paths
                .entry(&def.path)
                .and_modify(|e| *e = None)
                .or_insert(Some(DefId(i)));
        }
        let mut data_paths: HashMap<&str, Option<DataId>> = HashMap::new();
        for (i, data) in g.datas.iter().enumerate() {
            data_paths
                .entry(&data.path)
                .and_modify(|e| *e = None)
                .or_insert(Some(DataId(i)));
        }
        let mut ext_defs = vec![DefId(usize::MAX); deps.len()];
        let mut ext_datas = vec![DataId(usize::MAX); deps.len()];
        for (i, (kind, path, hash)) in deps.iter().enumerate() {
            let found = match kind {
                0 => unique(&def_paths, path).and_then(|id| {
                    ext_defs[i] = id;
                    def_hash(g, id).ok().flatten()
                }),
                1 => unique(&data_paths, path).and_then(|id| {
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
                base_defs: g.defs.len(),
                base_datas: g.datas.len(),
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
                span: body.span()?,
                ty: body.term()?,
                body: body.term()?,
                group: body.offsets(n)?,
                run_body: if body.r.bool()? {
                    Some(body.term()?)
                } else {
                    None
                },
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
                let result = (0..m).map(|_| body.term()).collect::<Read<_>>()?;
                ctors.push(CtorEntry {
                    name,
                    fields,
                    implicit,
                    result,
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
                group: body.offsets(n)?,
                defs_before: body.r.usize()?,
                datas_before: body.r.usize()?,
                span: body.span()?,
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

        let tables = read_tables(&mut body, index.files.len(), early.len())?;
        if !body.r.done() {
            return bad("bytes after the tables");
        }
        if tables.nav.is_some() != self.nav.is_some() {
            return bad("navigation recorded or not");
        }
        // Every ability a name refers to is one there will be.
        let abilities: HashSet<DataId> = self
            .abilities
            .iter()
            .chain(&tables.abilities)
            .map(|a| a.op_data)
            .collect();
        let globals = tables.changed.iter().map(|(_, g, _)| g);
        let globals = globals.chain(tables.new.iter().map(|(_, g, _, _)| g));
        let globals = globals.chain(&tables.early);
        let globals = globals.chain(tables.nav.iter().flat_map(|n| n.refs.iter().map(|r| &r.3)));
        for g in globals {
            if let GlobalEntry::Ability(d) | GlobalEntry::Op(d, _) = g
                && !abilities.contains(d)
            {
                return bad("a name refers to an ability there isn't");
            }
        }
        // Every target kept by name is one there will be.
        if let Some(nav) = &tables.nav {
            let own: HashSet<&str> = tables
                .changed
                .iter()
                .map(|(k, _, _)| k.as_str())
                .chain(tables.new.iter().map(|(k, _, _, _)| k.as_str()))
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
            tables,
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
        if !d.tables.tests.is_empty() || !d.tables.warnings.is_empty() {
            return bad("a library file's entry with tests or warnings");
        }
        self.admit_replayed(&d.defs, &d.datas, &d.bound)?;
        self.replay_tables(d.tables, &[]);
        Ok(())
    }

    /// Submits an entry's declarations to the kernel, through the same
    /// functions the elaborator uses, so it checks each one again: only
    /// elaboration is skipped (option A, D277). This is the one place a
    /// replay reaches the kernel.
    ///
    /// The declarations are made in their original order (a data group
    /// goes where its `defs_before` and `datas_before` say), and each group
    /// is defined as soon as everything it refers to is final, which is no
    /// later than the elaborator defined it. Each final declaration is
    /// bound as a built-in, if it is one, as elaborating binds it, and the
    /// built-ins bound must be the entry's `bound`. If the kernel refuses
    /// anything, or other built-ins are bound, what was added is removed
    /// and the file is elaborated instead.
    fn admit_replayed(
        &mut self,
        defs: &[DefEntry],
        datas: &[DataEntry],
        bound: &[(u8, usize, Builtin)],
    ) -> Read<()> {
        let base_defs = self.globals.defs.len();
        let base_datas = self.globals.datas.len();
        let module = self.globals.module.clone();
        let result = self
            .submit(defs, datas, base_defs, base_datas)
            .and_then(|()| {
                if bound_builtins(&self.globals, base_defs, base_datas) != bound {
                    return bad("other built-ins were bound");
                }
                Ok(())
            });
        self.globals.module = module;
        if let Err(why) = result {
            // Undo: nothing else refers to what was added yet.
            let g = &mut self.globals;
            g.registry.forget_from(base_defs, base_datas);
            g.defs.truncate(base_defs);
            g.datas.truncate(base_datas);
            g.hashes.borrow_mut().retain(|k, _| match k {
                stitchwort_core::globals::HashKey::Def(id) => id.0 < base_defs,
                stitchwort_core::globals::HashKey::Data(d) => d.0 < base_datas,
            });
            return Err(why);
        }
        Ok(())
    }

    fn submit(
        &mut self,
        defs: &[DefEntry],
        datas: &[DataEntry],
        base_defs: usize,
        base_datas: usize,
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
        let mut seen = HashSet::new();
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
        let mut seen = HashSet::new();
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
                            .all(|m| *m < self.globals.datas.len() - base_datas)
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
                                    .map(|c| kernel::CtorDecl {
                                        name: c.name.clone(),
                                        fields: c
                                            .fields
                                            .iter()
                                            .map(|(x, t)| (x.clone(), t.clone(), data.span))
                                            .collect(),
                                        result: c.result.clone(),
                                        implicit: c.implicit.clone(),
                                    })
                                    .collect();
                                (DataId(base_datas + m), ctors)
                            })
                            .collect();
                        self.kernel_op(|g| kernel::define_data_group(g, members))
                            .map_err(refused)?;
                        for m in &group.members {
                            data_final[*m] = true;
                            self.bind_builtin_data(DataId(base_datas + m))
                                .map_err(refused)?;
                        }
                    } else {
                        let members: Vec<(DefId, Term)> = group
                            .members
                            .iter()
                            .map(|&m| (DefId(base_defs + m), defs[m].body.clone()))
                            .collect();
                        self.kernel_op(|g| kernel::define_group(g, &members))
                            .map_err(refused)?;
                        for m in &group.members {
                            def_final[*m] = true;
                            self.bind_builtin_def(DefId(base_defs + m))
                                .map_err(refused)?;
                        }
                        for m in &group.members {
                            if let Some(run) = &defs[*m].run_body {
                                self.kernel_op(|g| {
                                    kernel::set_run_body(g, DefId(base_defs + m), run)
                                })
                                .map_err(refused)?;
                            }
                        }
                    }
                    group.done = true;
                    progress = true;
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
                let members = groups[gi]
                    .members
                    .iter()
                    .map(|&m| kernel::DataDecl {
                        name: datas[m].name.clone(),
                        span: datas[m].span,
                        record: datas[m].record,
                        indices: datas[m].indices.clone(),
                    })
                    .collect();
                self.globals.module = module_of(&first.name, &first.path)?;
                let (params, sort) = (first.params.clone(), first.sort);
                let ids = self
                    .kernel_op(|g| kernel::declare_indexed_data_group(g, params, sort, members))
                    .map_err(refused)?;
                for (&m, id) in groups[gi].members.iter().zip(&ids) {
                    let data = &datas[m];
                    if id.0 != base_datas + m || self.globals.data(*id).path != data.path {
                        return bad("a data type came out differently");
                    }
                    if data.params.len() != first.params.len() || data.sort != first.sort {
                        return bad("a data group's members disagree");
                    }
                    if !data.auto_params.is_empty() {
                        kernel::mark_auto_params(&mut self.globals, *id, data.auto_params.clone());
                    }
                }
                next_data_group += 1;
                continue;
            }
            if next_def < defs.len() {
                let def = &defs[next_def];
                self.globals.module = module_of(&def.name, &def.path)?;
                let id = self
                    .kernel_op(|g| {
                        kernel::declare_def(g, &def.name, &def.ty, def.theorem, false, def.span)
                    })
                    .map_err(refused)?;
                if id.0 != base_defs + next_def || self.globals.def(id).path != def.path {
                    return bad("a definition came out differently");
                }
                if def.fold {
                    kernel::mark_folded(&mut self.globals, id);
                }
                if def.instance {
                    kernel::mark_instance(&mut self.globals, id);
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

    /// Runs one kernel call as its own operation, with its own resource
    /// limits, as elaborating each component does.
    fn kernel_op<T>(&mut self, f: impl FnOnce(&mut Globals) -> T) -> T {
        let saved = self.globals.budget.start(self.limits);
        let result = f(&mut self.globals);
        self.globals.budget.restore(saved);
        result
    }

    /// Puts an entry's side tables in place, through the same insertion
    /// functions elaboration uses, once its declarations are admitted.
    /// `early` are the names a namespace declared before its library files
    /// loaded, already there (`replay_namespace`), which now get what they
    /// name.
    fn replay_tables(&mut self, t: Tables, early: &[(String, Span, bool)]) {
        self.abilities.extend(t.abilities);
        let ability = |e: &Elaborator, op_data: DataId| {
            e.abilities
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
        self.records.extend(t.records);
        self.interfaces.extend(t.interfaces);
        self.instances.extend(t.instances);
        let [owners, no_eq, no_show, no_ord] = t.by_data;
        self.data_owners.extend(owners);
        self.no_eq.extend(no_eq);
        self.no_show.extend(no_show);
        self.no_ord.extend(no_ord);
        self.lifted.extend(t.lifted);
        self.helper_keys.extend(t.helper_keys);
        for test in t.tests {
            self.tests.push(crate::TestDecl {
                library: false,
                name: test.name,
                namespace: test.namespace,
                def: test.def,
                span: test.span,
                sides: test
                    .sides
                    .map(|(op, left, right)| crate::TestSides { op, left, right }),
            });
        }
        if let (Some(nav), Some(entry)) = (&self.nav, t.nav) {
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
            for (at, ty) in entry.local_types {
                nav.local_types.insert((at.file, at.start), ty);
            }
            for (span, name, binder) in entry.locals {
                nav.locals.push(LocalUse { span, name, binder });
            }
            for (span, name, binder) in entry.binders {
                nav.binders.push(LocalUse { span, name, binder });
            }
            for (at, name, span) in entry.fields {
                nav.field_spans.insert((at, name), span);
            }
        }
    }
}

/// The module a declaration was declared in, from its name and its path
/// (`Std` for `List.length` at `Std.List.length`), so declaring it again
/// gives the same path.
fn module_of(name: &str, path: &str) -> Read<Name> {
    if path == name {
        return Ok("".into());
    }
    match path.strip_suffix(name).and_then(|m| m.strip_suffix('.')) {
        Some(module) if !module.is_empty() => Ok(module.into()),
        _ => bad(format!("`{path}` isn't `{name}` in a module")),
    }
}

/// The side tables of an entry, read; any ability a name refers to must
/// be one known after replay.
fn read_tables(b: &mut Body, files: usize, early: usize) -> Read<Tables> {
    let mut t = Tables {
        changed: Vec::new(),
        new: Vec::new(),
        early: Vec::new(),
        members: Vec::new(),
        records: Vec::new(),
        interfaces: Vec::new(),
        instances: Vec::new(),
        by_data: [Vec::new(), Vec::new(), Vec::new(), Vec::new()],
        abilities: Vec::new(),
        lifted: Vec::new(),
        helper_keys: Vec::new(),
        tests: Vec::new(),
        warnings: Vec::new(),
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
    let n = b.count()?;
    for _ in 0..n {
        let d = b.data()?;
        let k = b.count()?;
        let mut projections = Vec::with_capacity(k);
        for _ in 0..k {
            projections.push(if b.r.bool()? { Some(b.def()?) } else { None });
        }
        t.records.push((d, RecordInfo { projections }));
    }
    let n = b.count()?;
    for _ in 0..n {
        let d = b.data()?;
        let dict = b.string()?;
        let k = b.count()?;
        let supers = (0..k)
            .map(|_| Ok((b.r.usize()?, b.data()?)))
            .collect::<Read<_>>()?;
        let k = b.count()?;
        let projections = (0..k).map(|_| b.def()).collect::<Read<_>>()?;
        let k = b.count()?;
        let methods = (0..k).map(|_| b.def()).collect::<Read<_>>()?;
        let k = b.count()?;
        let relations = (0..k)
            .map(|_| Ok((b.r.usize()?, b.r.usize()?)))
            .collect::<Read<_>>()?;
        t.interfaces.push((
            d,
            InterfaceInfo {
                dict,
                supers,
                projections,
                methods,
                relations,
            },
        ));
    }
    let n = b.count()?;
    for _ in 0..n {
        let key = (b.data()?, b.data()?);
        let def = b.def()?;
        let name = b.string()?;
        let span = b.span()?;
        let k = b.count()?;
        let mut params = Vec::with_capacity(k);
        for _ in 0..k {
            params.push(match b.r.u8()? {
                0 => InstanceParam::Head(b.r.usize()?),
                1 => InstanceParam::Prerequisite,
                _ => return bad("an unknown kind of instance parameter"),
            });
        }
        let valid = b.r.bool()?;
        t.instances.push((
            key,
            InstanceInfo {
                def,
                name,
                span,
                params,
                valid,
            },
        ));
    }
    for table in &mut t.by_data {
        let n = b.count()?;
        for _ in 0..n {
            table.push((b.data()?, b.string()?));
        }
    }
    let n = b.count()?;
    for _ in 0..n {
        let name = b.string()?;
        let op_data = b.data()?;
        let res = b.def()?;
        let elim = b.def()?;
        let k = b.count()?;
        let ops = (0..k).map(|_| b.string()).collect::<Read<_>>()?;
        let order = (b.r.bool()?, b.string()?);
        t.abilities.push(AbilityInfo {
            name,
            op_data,
            res,
            elim,
            ops,
            order,
        });
    }
    let n = b.count()?;
    for _ in 0..n {
        t.lifted.push((b.def()?, b.span()?));
    }
    let n = b.count()?;
    for _ in 0..n {
        t.helper_keys.push(b.string()?);
    }
    let n = b.count()?;
    for _ in 0..n {
        let name = b.string()?;
        let namespace = b.string()?;
        let def = b.def()?;
        let span = b.span()?;
        let sides = if b.r.bool()? {
            let op = b.string()?;
            let Some(op) = TEST_OPS.iter().find(|o| **o == op) else {
                return bad(format!("no operator `{op}`"));
            };
            Some((*op, b.term()?, b.term()?))
        } else {
            None
        };
        t.tests.push(TestEntry {
            name,
            namespace,
            def,
            span,
            sides,
        });
    }
    let n = b.count()?;
    for _ in 0..n {
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
        t.warnings.push(d);
    }
    if b.r.bool()? {
        let mut nav = NavEntry {
            refs: Vec::new(),
            local_types: Vec::new(),
            locals: Vec::new(),
            binders: Vec::new(),
            fields: Vec::new(),
        };
        let n = b.count()?;
        for _ in 0..n {
            let at = b.span()?;
            let key = b.string()?;
            let target = if b.r.bool()? {
                Target::Key
            } else {
                Target::Span(b.span()?)
            };
            let global = b.global(files)?;
            let dot = if b.r.bool()? { Some(b.string()?) } else { None };
            nav.refs.push((at, key, target, global, dot));
        }
        let n = b.count()?;
        for _ in 0..n {
            nav.local_types.push((b.span()?, b.string()?));
        }
        for uses in [&mut nav.locals, &mut nav.binders] {
            let n = b.count()?;
            for _ in 0..n {
                uses.push((b.span()?, b.string()?, b.span()?));
            }
        }
        let n = b.count()?;
        for _ in 0..n {
            nav.fields.push((b.span()?, b.string()?, b.span()?));
        }
        t.nav = Some(nav);
    }
    Ok(t)
}

#[doc(hidden)]
pub use dump::canonical_dump;
