//! Where the check cache keeps its entries (docs/proposals/check-cache.md
//! §6): `check/` in a cache directory (`.stitchwort/cache` in the project,
//! next to `tests/`), one file per entry.
//!
//! - **Names.** An entry's file is `{fingerprint}-{unit}-{key}`: the
//!   compiler build that wrote it, the unit (a library file,
//!   `std.List.Toolkit`, or a project namespace, `ns.Aoc.Year2025.Day05`;
//!   `+nav` when navigation is recorded), and the entry's key in hex. The
//!   key covers only the source (docs/proposals/check-cache-across-updates.md
//!   §4.1), so another build's entry for the same unit and key is a
//!   candidate for a carried-over hit ([`Store::read_others`]); the build in
//!   the name keeps each build's own entries apart, so two builds sharing a
//!   folder don't overwrite each other's.
//! - **The header.** `check/header` holds the directory's random salt
//!   (§3.1), made the first time the directory is used. Every entry
//!   carries it, so an entry copied from another cache directory is a miss.
//! - **Writing** goes to a temporary file that is then renamed, so a reader
//!   never sees half an entry, and two writers at once (the editor and a
//!   command) just leave the last one. The temporary file's name holds the
//!   process id, a counter for the process and the thread's id, so writers
//!   in one process don't share one either.
//! - **Eviction (D283).** Writing an entry deletes the unit's other entries
//!   for this build; the first write of a run deletes entries of other
//!   builds that are more than a day old (two builds may share a project
//!   folder, hence the grace period), except each unit's newest entry,
//!   which a later build may carry over.
//!
//! The elaborator encodes, checks and replays entries; this only stores
//! them.

use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime};

use stitchwort_elab::cache::{Key, Store};

use crate::driver::{FINGERPRINT, KERNEL_FINGERPRINT};

/// How long entries of other builds are kept.
pub(crate) const GRACE: Duration = Duration::from_secs(24 * 60 * 60);

/// A check cache in a directory.
pub struct CheckCache {
    dir: PathBuf,
    /// The build, as entries' file names give it: [`FINGERPRINT`].
    build: String,
    compiler: String,
    /// The kernel side's fingerprint ([`KERNEL_FINGERPRINT`]).
    kernel: String,
    /// The folder's names when last listed, and its modification time
    /// then: the candidates for carried-over hits.
    listing: std::cell::RefCell<Option<(SystemTime, Vec<String>)>>,
    salt: [u8; 16],
    /// Whether this run has written yet (the first write sweeps).
    written: Cell<bool>,
    /// How long entries of other builds are kept.
    grace: Duration,
    /// The library's entries to read when this directory has none: the
    /// installed binary's ([`LibraryBundle::installed`]), unless a test
    /// gave one.
    installed: Option<std::sync::Arc<LibraryBundle>>,
    use_installed: bool,
}

impl CheckCache {
    /// The check cache in the cache directory `cache_dir` (its `check/`
    /// folder, made if needed).
    pub fn at(cache_dir: &Path) -> CheckCache {
        Self::with_grace(cache_dir, GRACE)
    }

    /// [`CheckCache::at`], keeping other builds' entries for `grace` only:
    /// the tests' cache, where every build of the code is a new build.
    pub fn with_grace(cache_dir: &Path, grace: Duration) -> CheckCache {
        Self::for_build(cache_dir, grace, FINGERPRINT, KERNEL_FINGERPRINT)
    }

    /// For tests: the check cache in `cache_dir` as a build whose
    /// fingerprint is `build` and whose kernel side's is `kernel` would
    /// use it, to stand for another build of the compiler.
    #[doc(hidden)]
    pub fn as_build(cache_dir: &Path, build: &str, kernel: &str) -> CheckCache {
        Self::for_build(cache_dir, GRACE, build, kernel)
    }

    fn for_build(cache_dir: &Path, grace: Duration, build: &str, kernel: &str) -> CheckCache {
        let dir = cache_dir.join("check");
        let salt = salt(&dir);
        let (compiler, kernel_name) = stamp_names(build, kernel);
        CheckCache {
            dir,
            build: build.to_string(),
            compiler,
            kernel: kernel_name,
            listing: std::cell::RefCell::new(None),
            salt,
            written: Cell::new(false),
            grace,
            installed: None,
            use_installed: true,
        }
    }

    /// For tests: this cache reads library entries from `bundle` when its
    /// directory has none, in place of the installed binary's.
    #[doc(hidden)]
    pub fn with_installed(mut self, bundle: std::sync::Arc<LibraryBundle>) -> CheckCache {
        self.installed = Some(bundle);
        self
    }

    /// For tests: this cache never reads library entries from an installed
    /// bundle.
    #[doc(hidden)]
    pub fn without_installed(mut self) -> CheckCache {
        self.installed = None;
        self.use_installed = false;
        self
    }

    /// The installed bundle's entry for library file `unit` at `key`, sealed
    /// for this directory: what the directory would hold if this build had
    /// checked the file here. An entry the directory has is always read
    /// first, so a file the user's std edit changes, or any other miss, is
    /// checked as without a bundle.
    fn installed_entry(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        if !unit.starts_with("std.") {
            return None;
        }
        let bundle = match &self.installed {
            Some(bundle) => bundle.clone(),
            None if self.use_installed => LibraryBundle::installed()?,
            None => return None,
        };
        let entry = bundle.entries.get(&(unit.to_string(), *key))?;
        stitchwort_elab::cache::reseal(entry, key, BUNDLE_SALT, self.salt)
    }

    fn file(&self, unit: &str, key: &Key) -> PathBuf {
        self.dir.join(format!("{}-{unit}-{}", self.build, hex(key)))
    }

    /// The names in the folder, listed again only when it has changed.
    fn names(&self) -> Vec<String> {
        let Some(modified) = std::fs::metadata(&self.dir).and_then(|m| m.modified()).ok() else {
            return Vec::new();
        };
        let mut listing = self.listing.borrow_mut();
        if let Some((when, names)) = &*listing
            && *when == modified
        {
            return names.clone();
        }
        let names: Vec<String> = std::fs::read_dir(&self.dir)
            .map(|entries| {
                entries
                    .flatten()
                    .filter_map(|e| e.file_name().into_string().ok())
                    .collect()
            })
            .unwrap_or_default();
        *listing = Some((modified, names.clone()));
        names
    }

    /// Deletes this unit's other entries for this build, and on the first
    /// write of a run, other builds' entries older than [`GRACE`] and
    /// temporary files left behind.
    fn evict(&self, unit: &str, keep: &Path) {
        let first = !self.written.replace(true);
        let Ok(entries) = std::fs::read_dir(&self.dir) else {
            return;
        };
        let own = format!("{}-{unit}-", self.build);
        let mine = format!("{}-", self.build);
        let now = SystemTime::now();
        // Other builds' entries past the grace period, by unit, with when
        // each was written: all but each unit's newest are deleted.
        let mut old: std::collections::BTreeMap<String, Vec<(SystemTime, PathBuf)>> =
            std::collections::BTreeMap::new();
        // The newest entry of each unit, of any build.
        let mut newest: std::collections::BTreeMap<String, SystemTime> =
            std::collections::BTreeMap::new();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if name == "header" || path == keep {
                continue;
            }
            if name.starts_with(&own) {
                let _ = std::fs::remove_file(&path);
                continue;
            }
            if !first {
                continue;
            }
            let modified = entry.metadata().and_then(|m| m.modified()).ok();
            let age = modified.and_then(|t| now.duration_since(t).ok());
            if name.starts_with(".tmp-") {
                if age.is_some_and(|age| age > self.grace) {
                    let _ = std::fs::remove_file(&path);
                }
                continue;
            }
            let (Some(unit), Some(modified)) = (entry_unit(name), modified) else {
                continue;
            };
            let latest = newest.entry(unit.to_string()).or_insert(modified);
            *latest = (*latest).max(modified);
            if !name.starts_with(&mine) && age.is_some_and(|age| age > self.grace) {
                old.entry(unit.to_string())
                    .or_default()
                    .push((modified, path.clone()));
            }
        }
        for (unit, entries) in old {
            for (modified, path) in entries {
                if newest.get(&unit).is_some_and(|&n| n > modified) {
                    let _ = std::fs::remove_file(&path);
                }
            }
        }
    }
}

impl Store for CheckCache {
    fn compiler(&self) -> &str {
        &self.compiler
    }

    fn kernel(&self) -> &str {
        &self.kernel
    }

    fn read_others(&self, unit: &str, key: &Key) -> Vec<Vec<u8>> {
        let suffix = format!("-{unit}-{}", hex(key));
        let mine = format!("{}-", self.build);
        let mut found: Vec<(SystemTime, PathBuf)> = self
            .names()
            .into_iter()
            .filter(|name| name.ends_with(&suffix) && !name.starts_with(&mine))
            .filter_map(|name| {
                let path = self.dir.join(name);
                let modified = std::fs::metadata(&path).and_then(|m| m.modified()).ok()?;
                Some((modified, path))
            })
            .collect();
        found.sort_by_key(|(modified, _)| std::cmp::Reverse(*modified));
        found
            .into_iter()
            .filter_map(|(_, path)| std::fs::read(path).ok())
            .collect()
    }

    fn salt(&self) -> [u8; 16] {
        self.salt
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        std::fs::read(self.file(unit, key))
            .ok()
            .or_else(|| self.installed_entry(unit, key))
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        let path = self.file(unit, key);
        if write_atomically(&self.dir, &path, entry).is_ok() {
            self.evict(unit, &path);
        }
    }
}

/// The folder of the cache directory `cache_dir` that keeps the library's
/// name index (`stitchwort_elab::IndexCache`).
pub fn std_index_dir(cache_dir: &Path) -> PathBuf {
    cache_dir.join("std-index")
}

/// The library index cache in the cache directory `cache_dir`, for this
/// build: its entries are named by the check cache's compiler stamp.
pub fn std_index_cache(cache_dir: &Path) -> stitchwort_elab::IndexCache {
    stitchwort_elab::IndexCache::new(
        &std_index_dir(cache_dir),
        &stamp_names(FINGERPRINT, KERNEL_FINGERPRINT).0,
    )
}

/// Makes this process read the library's name index from, and write it to,
/// the cache directory `cache_dir`, if it hasn't made the index yet
/// (`stitchwort_elab::use_index_cache`). Call it before the first session
/// starts.
pub fn use_std_index_cache(cache_dir: &Path) {
    stitchwort_elab::use_index_cache(
        &std_index_dir(cache_dir),
        &stamp_names(FINGERPRINT, KERNEL_FINGERPRINT).0,
    );
}

/// Makes the sessions this process starts from now on load the core from,
/// and keep it in, the check cache in `cache_dir` (SW-4814): checked
/// through this kernel's checking calls with `recheck` (`check
/// --recheck`). Only a session whose result the core's entry can stand for
/// uses it: the standard library's index, no library tests, no stale pins
/// falling back (`Session::start`). Call it before the first session starts;
/// tests never do, so they check the core from source.
pub fn use_core_cache(cache_dir: &Path, recheck: bool) {
    *CORE_CACHE.lock().unwrap_or_else(|e| e.into_inner()) = Some(CoreCache {
        dir: cache_dir.to_path_buf(),
        recheck,
        refuse_after: None,
    });
}

/// Where [`use_core_cache`] said to keep the core, if it was called.
#[derive(Clone)]
pub(crate) struct CoreCache {
    pub(crate) dir: std::path::PathBuf,
    pub(crate) recheck: bool,
    /// For a test: the replay is refused after this declaration
    /// (`Session::with_core_cache`).
    pub(crate) refuse_after: Option<String>,
}

static CORE_CACHE: std::sync::Mutex<Option<CoreCache>> = std::sync::Mutex::new(None);

/// [`use_core_cache`]'s setting.
pub(crate) fn core_cache() -> Option<CoreCache> {
    CORE_CACHE.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// What [`Store::compiler`] and [`Store::kernel`] say for the build whose
/// fingerprint is `build` and whose kernel side's is `kernel`.
fn stamp_names(build: &str, kernel: &str) -> (String, String) {
    let version = env!("CARGO_PKG_VERSION");
    (
        format!("stitchwort-{version}-{build}"),
        format!("stitchwort-{version}-kernel-{kernel}"),
    )
}

/// The check cache of one parallel `check --no-cache` (`check --jobs N`,
/// [`crate::parallel`]): a map in memory that lives for the run, shared by
/// its workers and the check after them, so that what one worker checked
/// another replays instead of checking it again. Nothing on disk is read or
/// written. It has this build's stamp and a salt made for the run, so an
/// entry in it is one this process wrote; each is written only once the
/// kernel has accepted every declaration in it, as a cache directory's.
///
/// Clones share the map: each thread wraps its own in an `Rc<dyn Store>`.
/// Each entry of a [`MemoryStore`], by unit and key.
type MemoryEntries = std::collections::BTreeMap<(String, Key), std::sync::Arc<[u8]>>;

#[derive(Clone)]
pub struct MemoryStore(std::sync::Arc<MemoryShared>);

struct MemoryShared {
    entries: std::sync::Mutex<MemoryEntries>,
    compiler: String,
    kernel: String,
    salt: [u8; 16],
}

impl Default for MemoryStore {
    fn default() -> Self {
        let (compiler, kernel) = stamp_names(FINGERPRINT, KERNEL_FINGERPRINT);
        MemoryStore(std::sync::Arc::new(MemoryShared {
            entries: Default::default(),
            compiler,
            kernel,
            salt: random_salt(),
        }))
    }
}

impl MemoryStore {
    /// How many entries it holds.
    pub fn len(&self) -> usize {
        self.entries().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn entries(&self) -> std::sync::MutexGuard<'_, MemoryEntries> {
        self.0.entries.lock().unwrap_or_else(|e| e.into_inner())
    }
}

impl Store for MemoryStore {
    fn compiler(&self) -> &str {
        &self.0.compiler
    }

    fn kernel(&self) -> &str {
        &self.0.kernel
    }

    fn salt(&self) -> [u8; 16] {
        self.0.salt
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.entries()
            .get(&(unit.to_string(), *key))
            .map(|entry| entry.to_vec())
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        self.entries()
            .insert((unit.to_string(), *key), std::sync::Arc::from(entry));
    }
}

/// The library files the workers of a parallel check are elaborating, so
/// that two of them needing the same uncached file don't both elaborate it
/// ([`ClaimStore`]). Shared by the workers, in memory.
pub struct Claims {
    /// Each library file's unit and key, with the worker elaborating it.
    held: std::sync::Mutex<std::collections::BTreeMap<(String, Key), usize>>,
    changed: std::sync::Condvar,
    /// How long a worker waits for another's file before elaborating it
    /// itself.
    patience: Duration,
    /// How many waits ran out.
    gave_up: AtomicU64,
}

impl Claims {
    /// Claims whose waits last at most `patience`.
    pub fn new(patience: Duration) -> Claims {
        Claims {
            held: Default::default(),
            changed: std::sync::Condvar::new(),
            patience,
            gave_up: AtomicU64::new(0),
        }
    }

    /// How many waits ran out, so a worker elaborated a file another was
    /// elaborating.
    pub fn gave_up(&self) -> u64 {
        self.gave_up.load(Ordering::Relaxed)
    }

    fn held(&self) -> std::sync::MutexGuard<'_, std::collections::BTreeMap<(String, Key), usize>> {
        self.held.lock().unwrap_or_else(|e| e.into_inner())
    }
}

/// A worker's check cache in a parallel check: its own store, with the
/// library files' entries claimed in a table the workers share ([`Claims`]).
/// While the worker has a job ([`ClaimStore::begin_job`]), a read of a
/// library file that finds no entry claims the file, and the worker
/// elaborates and writes it as it would anyway; a read of a file another
/// worker has claimed waits until that one writes it or ends its job, then
/// reads again. Namespaces' entries, and everything outside a job, go
/// straight to the store.
///
/// - **No deadlock.** A worker waits only for a library file needed by the
///   one it is elaborating (or, elaborating none, by its namespace), and
///   holds unwritten claims only on the files it is in the middle of, each
///   needing the next; the library's files have no cycle, so the waits
///   can't make one. A file whose elaboration fails is never written, and
///   its claim is let go as its elaboration ends ([`Store::abandon`]); a
///   wait that runs out of patience
///   elaborates the file itself, which changes no result.
/// - **Exactness.** A claim decides only who elaborates first. Whoever
///   does writes the same bytes the other would have, by the cache's own
///   invariant (replay equals elaboration); a worker that finds the entry
///   replays it, as a sequential check does in the next namespace.
pub struct ClaimStore {
    inner: std::rc::Rc<dyn Store>,
    claims: std::sync::Arc<Claims>,
    worker: usize,
    active: Cell<bool>,
}

impl ClaimStore {
    pub fn new(
        inner: std::rc::Rc<dyn Store>,
        claims: std::sync::Arc<Claims>,
        worker: usize,
    ) -> ClaimStore {
        ClaimStore {
            inner,
            claims,
            worker,
            active: Cell::new(false),
        }
    }

    /// From now until [`ClaimStore::end_job`], library files are claimed.
    pub fn begin_job(&self) {
        self.active.set(true);
    }

    /// Lets go of every claim this worker still holds (files whose
    /// elaboration failed), waking those waiting for them.
    pub fn end_job(&self) {
        self.active.set(false);
        let mut held = self.claims.held();
        held.retain(|_, worker| *worker != self.worker);
        drop(held);
        self.claims.changed.notify_all();
    }

    /// Lets go of this worker's claim on a file, waking those waiting for
    /// it: it has been written, or won't be.
    fn release(&self, unit: &str, key: &Key) {
        if self.claimed(unit) {
            let id = (unit.to_string(), *key);
            let mut held = self.claims.held();
            if held.get(&id) == Some(&self.worker) {
                held.remove(&id);
            }
            drop(held);
            self.claims.changed.notify_all();
        }
    }

    fn claimed(&self, unit: &str) -> bool {
        self.active.get() && unit.starts_with("std.")
    }
}

impl Store for ClaimStore {
    fn compiler(&self) -> &str {
        self.inner.compiler()
    }

    fn kernel(&self) -> &str {
        self.inner.kernel()
    }

    fn salt(&self) -> [u8; 16] {
        self.inner.salt()
    }

    fn read_others(&self, unit: &str, key: &Key) -> Vec<Vec<u8>> {
        self.inner.read_others(unit, key)
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        if !self.claimed(unit) {
            return self.inner.read(unit, key);
        }
        if let Some(entry) = self.inner.read(unit, key) {
            return Some(entry);
        }
        let id = (unit.to_string(), *key);
        let deadline = std::time::Instant::now() + self.claims.patience;
        let mut held = self.claims.held();
        loop {
            match held.get(&id) {
                Some(&worker) if worker != self.worker => {
                    let now = std::time::Instant::now();
                    if now >= deadline {
                        self.claims.gave_up.fetch_add(1, Ordering::Relaxed);
                        return None;
                    }
                    held = (self.claims.changed)
                        .wait_timeout(held, deadline - now)
                        .unwrap_or_else(|e| e.into_inner())
                        .0;
                }
                Some(_) => return None,
                None => {
                    // Read again under the lock: the owner writes before it
                    // lets go, so an entry that isn't here now isn't being
                    // made by anyone.
                    if let Some(entry) = self.inner.read(unit, key) {
                        return Some(entry);
                    }
                    held.insert(id, self.worker);
                    return None;
                }
            }
        }
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        self.inner.write(unit, key, entry);
        self.release(unit, key);
    }

    fn abandon(&self, unit: &str, key: &Key) {
        self.inner.abandon(unit, key);
        self.release(unit, key);
    }
}

/// Numbers this process's temporary files, so that two threads writing in
/// the same nanosecond don't pick the same one.
static TEMP_FILE: AtomicU64 = AtomicU64::new(0);

/// Writes `bytes` to `path` in `dir` by way of a temporary file there.
fn write_atomically(dir: &Path, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let count = TEMP_FILE.fetch_add(1, Ordering::Relaxed);
    let temp = dir.join(format!(
        ".tmp-{}-{nanos}-{count}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    let result = std::fs::write(&temp, bytes).and_then(|()| std::fs::rename(&temp, path));
    if result.is_err() {
        let _ = std::fs::remove_file(&temp);
    }
    result
}

/// The unit of the entry file `name` (`{build}-{unit}-{key}`).
fn entry_unit(name: &str) -> Option<&str> {
    let (_, rest) = name.split_once('-')?;
    let (unit, _) = rest.rsplit_once('-')?;
    Some(unit)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

const HEADER: &str = "stitchwort check cache\nsalt ";

/// The salt in `dir`'s header, making the header if there isn't one. If it
/// can't be written, a new salt for this run only (its entries can't be
/// read by a later run, which is just a miss).
fn salt(dir: &Path) -> [u8; 16] {
    let header = dir.join("header");
    let read = || -> Option<[u8; 16]> {
        let text = std::fs::read_to_string(&header).ok()?;
        let hex = text.strip_prefix(HEADER)?.trim();
        let mut salt = [0u8; 16];
        if hex.len() != 32 {
            return None;
        }
        for (i, byte) in salt.iter_mut().enumerate() {
            *byte = u8::from_str_radix(hex.get(2 * i..2 * i + 2)?, 16).ok()?;
        }
        Some(salt)
    };
    if let Some(salt) = read() {
        return salt;
    }
    let fresh = random_salt();
    let text = format!("{HEADER}{}\n", hex(&fresh));
    if write_atomically(dir, &header, text.as_bytes()).is_err() {
        return fresh;
    }
    // Another run may have written its header at the same time: the one on
    // disk wins.
    read().unwrap_or(fresh)
}

/// 16 random bytes, from the standard library's randomly keyed hasher.
fn random_salt() -> [u8; 16] {
    use std::hash::BuildHasher;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let mut salt = [0u8; 16];
    for (i, chunk) in salt.chunks_mut(8).enumerate() {
        let state = std::hash::RandomState::new();
        let word = state.hash_one((nanos, std::process::id(), i));
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    salt
}

/// A check cache for the standard library made ahead of time and shipped
/// with a host that has no cache directory: the playground's `std.cache`,
/// written by `web/build.sh` with the same WebAssembly the page runs
/// (docs/proposals/playground-editor.md §5.2.4).
///
/// - **What it holds:** the compiler that made it, a salt, an entry per
///   library file (unit, key, entry, as a [`CheckCache`] stores them), and
///   the library files that don't check under the limits it was made with
///   (`left_out`), which a session like it should not load up front.
/// - **Validity:** an entry is looked up by its key, which covers the
///   modes and limits, and the file's text and its dependencies' keys, and
///   its stamp names the compiler build; so a session made differently
///   finds only misses, and the file is checked as without a cache. A
///   bundle from another compiler is not read at all
///   ([`LibraryBundle::decode`]), so its `left_out` isn't used either.
/// - **Trust:** its entries are admitted without the kernel's checks, as
///   a cache directory's are (check-cache.md, D1660). The salt that keeps a
///   directory from reading another's entries doesn't apply: the bundle
///   comes from the build that made the WebAssembly reading it.
#[derive(Default)]
pub struct LibraryBundle {
    compiler: String,
    entries: std::collections::BTreeMap<(String, Key), Vec<u8>>,
    /// Paths under `std/` (`Float/Theory.sw`).
    pub left_out: std::collections::BTreeSet<String>,
    /// A hash of the content above, for a key that outlives the bundle's
    /// address: the language server's kept search session.
    id: Key,
}

const BUNDLE_MAGIC: &[u8] = b"stitchwort library bundle 1\n";

/// The bundle's salt, the same for every bundle so that one build makes
/// the same bytes each time.
const BUNDLE_SALT: [u8; 16] = *b"playground std\0\0";

impl LibraryBundle {
    /// The compiler this build's entries are made by.
    fn this_compiler() -> String {
        format!("stitchwort-{}-{}", env!("CARGO_PKG_VERSION"), FINGERPRINT)
    }

    /// A hash of a bundle's content, independent of where it is in memory.
    fn content_id(
        compiler: &str,
        entries: &std::collections::BTreeMap<(String, Key), Vec<u8>>,
        left_out: &std::collections::BTreeSet<String>,
    ) -> Key {
        let mut hasher = blake3::Hasher::new();
        // Each field with its length, so adjacent ones can't run together.
        let mut field = |bytes: &[u8]| {
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(bytes);
        };
        field(compiler.as_bytes());
        for ((unit, key), entry) in entries {
            field(unit.as_bytes());
            field(key);
            field(entry);
        }
        for path in left_out {
            field(path.as_bytes());
        }
        *hasher.finalize().as_bytes()
    }

    /// The bundle's content hash: equal bundles have the same id, whatever
    /// their address, for a session key that outlives the bundle's address.
    pub fn id(&self) -> Key {
        self.id
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The bundle in `bytes`, or `None` if they aren't one or it was made by
    /// another build of the compiler.
    pub fn decode(bytes: &[u8]) -> Option<LibraryBundle> {
        let mut r = bytes.strip_prefix(BUNDLE_MAGIC)?;
        let mut take = |n: usize| -> Option<&[u8]> {
            let (head, tail) = r.split_at_checked(n)?;
            r = tail;
            Some(head)
        };
        let mut chunk = || -> Option<Vec<u8>> {
            let n = u64::from_le_bytes(take(8)?.try_into().ok()?);
            Some(take(usize::try_from(n).ok()?)?.to_vec())
        };
        let compiler = String::from_utf8(chunk()?).ok()?;
        if compiler != Self::this_compiler() {
            return None;
        }
        let count = u64::from_le_bytes(chunk()?.try_into().ok()?);
        let mut entries = std::collections::BTreeMap::new();
        for _ in 0..count {
            let unit = String::from_utf8(chunk()?).ok()?;
            let key: Key = chunk()?.try_into().ok()?;
            entries.insert((unit, key), chunk()?);
        }
        let left = String::from_utf8(chunk()?).ok()?;
        let left_out: std::collections::BTreeSet<String> =
            left.lines().map(str::to_string).collect();
        let id = Self::content_id(&compiler, &entries, &left_out);
        Some(LibraryBundle {
            compiler,
            entries,
            left_out,
            id,
        })
    }

    /// The length of the magic that starts an encoded bundle, for tests that
    /// edit its bytes.
    #[doc(hidden)]
    pub const MAGIC_LEN: usize = BUNDLE_MAGIC.len();

    /// Where an installed binary keeps its bundle, relative to the folder
    /// the binary is in: beside the installed `std/` (`std_dir`).
    const INSTALLED: &'static str = "../share/stitchwort/std.cache";

    /// The bundle installed beside the executable `exe`
    /// (`../share/stitchwort/std.cache`), if there is one and this build made
    /// it ([`LibraryBundle::decode`]); else `None`, as for a build from a
    /// checkout.
    pub fn installed_beside(exe: &Path) -> Option<LibraryBundle> {
        let file = exe.parent()?.join(Self::INSTALLED);
        Self::decode(&std::fs::read(file).ok()?)
    }

    /// [`LibraryBundle::installed_beside`] for this process's executable,
    /// read the first time it is asked for.
    pub fn installed() -> Option<std::sync::Arc<LibraryBundle>> {
        static INSTALLED: std::sync::OnceLock<Option<std::sync::Arc<LibraryBundle>>> =
            std::sync::OnceLock::new();
        INSTALLED
            .get_or_init(|| {
                let exe = std::env::current_exe().ok()?;
                Self::installed_beside(&exe).map(std::sync::Arc::new)
            })
            .clone()
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut out = BUNDLE_MAGIC.to_vec();
        let mut chunk = |bytes: &[u8]| {
            out.extend((bytes.len() as u64).to_le_bytes());
            out.extend(bytes);
        };
        chunk(self.compiler.as_bytes());
        chunk(&(self.entries.len() as u64).to_le_bytes());
        for ((unit, key), entry) in &self.entries {
            chunk(unit.as_bytes());
            chunk(key);
            chunk(entry);
        }
        let left: Vec<&str> = self.left_out.iter().map(String::as_str).collect();
        chunk(left.join("\n").as_bytes());
        out
    }
}

/// The library checked as the CLI checks it (`Session::for_stack(stack)`,
/// no navigation: what `check`, `run`, `test` and `search` key their entries
/// by), as a [`LibraryBundle`] to install beside the binary
/// ([`LibraryBundle::installed`], SW-2163). Fails unless every library file
/// checks and a second session reads every entry back from the bundle, as a
/// session with the installed bundle would: a key that didn't match would
/// make a shipped bundle save nothing. The `String` says what it holds.
pub fn cli_library_bundle(stack: usize) -> Result<(std::sync::Arc<LibraryBundle>, String), String> {
    use crate::driver::Session;
    let mut session = Session::for_stack(stack);
    let recorder = std::rc::Rc::new(BundleRecorder::default());
    session.elab.set_check_cache(recorder.clone());
    session.elab.load_all_libraries().map_err(|ds| {
        format!(
            "the library doesn't check: {}",
            ds.first().map_or(String::new(), |d| d.message.clone())
        )
    })?;
    let made = session.elab.check_cache_stats();
    let bundle = std::sync::Arc::new(recorder.finish(Default::default()));
    let mut again = Session::for_stack(stack);
    again
        .elab
        .set_check_cache(std::rc::Rc::new(BundleStore(bundle.clone())));
    let loaded = again.elab.load_all_libraries();
    let replayed = again.elab.check_cache_stats();
    let summary = format!(
        "{} library files' entries; {} not cacheable",
        bundle.len(),
        made.uncacheable
    );
    if loaded.is_err() || replayed.hits != bundle.len() || replayed.misses != made.uncacheable {
        return Err(format!(
            "the library doesn't load from its bundle: {} hits and {} misses ({summary})",
            replayed.hits, replayed.misses
        ));
    }
    Ok((bundle, summary))
}

/// A [`LibraryBundle`] as a session's check cache: read only, since what
/// a session checks itself may differ from what the bundle was made with.
pub struct BundleStore(pub std::sync::Arc<LibraryBundle>);

impl Store for BundleStore {
    fn compiler(&self) -> &str {
        &self.0.compiler
    }

    fn salt(&self) -> [u8; 16] {
        BUNDLE_SALT
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.0.entries.get(&(unit.to_string(), *key)).cloned()
    }

    fn write(&self, _: &str, _: &Key, _: &[u8]) {}
}

/// What a [`LayeredStore`] did with a namespace's entry, for tests that check
/// which namespaces a re-check replays: a namespace that is replayed is read
/// and not written; one that is elaborated is written, whether or not the
/// read found an entry (an entry whose dependencies changed is found, then
/// refused by the elaborator).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreEvent {
    Found,
    Missing,
    Wrote,
}

pub type StoreLog = std::sync::Arc<std::sync::Mutex<Vec<(String, StoreEvent)>>>;

/// The playground's check cache for a project: the library's [`LibraryBundle`]
/// underneath, read only, and a writable layer in memory above it for the
/// project's namespaces. Without the layer every edit re-elaborates every
/// namespace after the edited one (the session rewinds to the edit), because
/// nothing the check wrote could be read back (SW-2919).
///
/// - **Only `ns.` units are written.** Library entries come from the bundle,
///   which was made by a session with the same limits; one a session wrote
///   itself would only duplicate it or, for a file the bundle `left_out`,
///   hold what the session chose not to load.
/// - **No disk gate.** A native server writes only while every file matches
///   disk, so unsaved text doesn't fill the cache directory. Nothing here
///   outlives the tab, and an entry for unsaved text is found again by its
///   key (the text is in it), so undoing an edit hits.
/// - **Soundness is the keys'.** An entry is found only by a key covering the
///   namespace's text, the configuration and the namespace set, and its
///   header lists its dependencies' hashes, so editing a dependency misses
///   its dependents (an `Early` miss) instead of replaying them stale.
/// - **Bounded.** A write replaces the unit's older entries but the newest
///   two, so an undo still hits, and the total is capped, dropping the
///   oldest first. Stores sharing a [`LayerBudget`] are capped together, so
///   the server can keep one per project without multiplying the cap.
pub struct LayeredStore {
    bundle: std::sync::Arc<LibraryBundle>,
    local: std::cell::RefCell<Layer>,
    log: Option<StoreLog>,
    budget: LayerBudget,
    sink: Option<(String, EntrySink)>,
}

/// Told each namespace entry a [`LayeredStore`] writes (its project's
/// folder, unit, key, entry):
/// the playground's page keeps them, so that a new worker can start from
/// what the last one had checked (SW-4871).
#[derive(Clone)]
pub struct EntrySink(pub std::sync::Arc<SinkFn>);

type SinkFn = dyn Fn(&str, &str, &Key, &[u8]) + Send + Sync;

impl std::fmt::Debug for EntrySink {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("EntrySink")
    }
}

#[derive(Default)]
struct Layer {
    /// Each entry with the order it was written in.
    entries: std::collections::BTreeMap<(String, Key), (u64, Vec<u8>)>,
    written: u64,
    bytes: usize,
}

/// Entries kept per unit: the current text and the one before it.
const ENTRIES_PER_UNIT: usize = 2;

/// The size limit of a [`LayeredStore`], or of the stores sharing one
/// [`LayerBudget`]. A whole AoC project is est. 45-60 MB; wasm memory never
/// shrinks, so this bounds what a long session can pile up.
pub const LAYER_CAP_BYTES: usize = 192 * 1024 * 1024;

/// The bytes of the namespace entries that a group of [`LayeredStore`]s may
/// hold together: the playground keeps one store per project (SW-3072), and
/// shares this budget between them so that keeping several projects' entries
/// doesn't multiply the cap.
///
/// A store that writes while the budget is full drops its own oldest entries
/// (never another store's), down to the newest one, which it keeps; so the
/// total can exceed the cap by at most that one entry per store.
#[derive(Clone, Default)]
pub struct LayerBudget(std::rc::Rc<std::cell::Cell<usize>>);

impl LayerBudget {
    /// The bytes the stores sharing it hold.
    pub fn used(&self) -> usize {
        self.0.get()
    }

    fn add(&self, bytes: usize) {
        self.0.set(self.0.get() + bytes);
    }

    fn remove(&self, bytes: usize) {
        self.0.set(self.0.get().saturating_sub(bytes));
    }
}

impl Layer {
    /// Removes `id`, returning the bytes it held.
    fn remove(&mut self, id: &(String, Key)) -> usize {
        self.entries.remove(id).map_or(0, |(_, entry)| {
            self.bytes -= entry.len();
            entry.len()
        })
    }

    fn oldest<'a>(
        of: impl Iterator<Item = (&'a (String, Key), &'a (u64, Vec<u8>))>,
    ) -> Option<(String, Key)> {
        of.min_by_key(|(_, (order, _))| *order)
            .map(|(id, _)| id.clone())
    }
}

impl LayeredStore {
    pub fn new(bundle: std::sync::Arc<LibraryBundle>) -> Self {
        Self::with_budget(bundle, LayerBudget::default())
    }

    /// A store whose entries count against `budget`, shared with the other
    /// stores of the same budget.
    pub fn with_budget(bundle: std::sync::Arc<LibraryBundle>, budget: LayerBudget) -> Self {
        LayeredStore {
            bundle,
            local: Default::default(),
            log: None,
            budget,
            sink: None,
        }
    }

    /// Tells `sink` of every namespace entry written from now on, as the
    /// entries of the project in `root`.
    pub fn with_sink(mut self, root: &str, sink: EntrySink) -> Self {
        self.sink = Some((root.to_string(), sink));
        self
    }

    /// Adds an entry an earlier store of this build wrote (the sink was
    /// told it), as if it had been written here. Sound for the same
    /// reason a written entry is: it is found only by its key, which
    /// covers the namespace's text, configuration and namespace set, and
    /// replayed only if its header's dependencies are still what they were.
    pub fn restore(&self, unit: &str, key: &Key, entry: &[u8]) {
        if unit.starts_with("ns.") {
            self.insert(unit, key, entry);
        }
    }

    /// Records every namespace lookup in `log`.
    pub fn logging(mut self, log: StoreLog) -> Self {
        self.log = Some(log);
        self
    }

    fn note(&self, unit: &str, event: StoreEvent) {
        if let (Some(log), true) = (&self.log, unit.starts_with("ns.")) {
            log.lock().unwrap().push((unit.to_string(), event));
        }
    }

    /// Drops every entry, giving their bytes back to the budget: for a
    /// server that keeps several projects' stores and makes room for a
    /// newly loaded one.
    pub fn clear(&self) {
        let mut layer = self.local.borrow_mut();
        let bytes = std::mem::take(&mut layer.bytes);
        layer.entries.clear();
        self.budget.remove(bytes);
    }

    /// How many namespace entries it holds.
    pub fn namespace_entries(&self) -> usize {
        self.local.borrow().entries.len()
    }

    /// The bytes of the namespace entries it holds.
    pub fn namespace_bytes(&self) -> usize {
        self.local.borrow().bytes
    }
}

impl Drop for LayeredStore {
    fn drop(&mut self) {
        self.budget.remove(self.local.borrow().bytes);
    }
}

impl Store for LayeredStore {
    fn compiler(&self) -> &str {
        &self.bundle.compiler
    }

    fn salt(&self) -> [u8; 16] {
        BUNDLE_SALT
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        let found = self
            .local
            .borrow()
            .entries
            .get(&(unit.to_string(), *key))
            .map(|(_, entry)| entry.clone())
            .or_else(|| self.bundle.entries.get(&(unit.to_string(), *key)).cloned());
        let event = if found.is_some() {
            StoreEvent::Found
        } else {
            StoreEvent::Missing
        };
        self.note(unit, event);
        found
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if !unit.starts_with("ns.") {
            return;
        }
        self.note(unit, StoreEvent::Wrote);
        if let Some((root, sink)) = &self.sink {
            (sink.0)(root, unit, key, entry);
        }
        self.insert(unit, key, entry);
    }
}

impl LayeredStore {
    fn insert(&self, unit: &str, key: &Key, entry: &[u8]) {
        let mut layer = self.local.borrow_mut();
        let id = (unit.to_string(), *key);
        self.budget.remove(layer.remove(&id));
        layer.written += 1;
        let order = layer.written;
        layer.bytes += entry.len();
        self.budget.add(entry.len());
        layer.entries.insert(id, (order, entry.to_vec()));
        let range = (unit.to_string(), [0; 32])..=(unit.to_string(), [255; 32]);
        while layer.entries.range(range.clone()).count() > ENTRIES_PER_UNIT {
            let oldest = Layer::oldest(layer.entries.range(range.clone()));
            self.budget
                .remove(layer.remove(&oldest.expect("more than none")));
        }
        while self.budget.used() > LAYER_CAP_BYTES && layer.entries.len() > 1 {
            let oldest = Layer::oldest(layer.entries.iter());
            self.budget
                .remove(layer.remove(&oldest.expect("more than none")));
        }
    }
}

/// A check cache that keeps the library files' entries written to it, to
/// make a [`LibraryBundle`] of them.
pub struct BundleRecorder {
    compiler: String,
    entries: std::cell::RefCell<std::collections::BTreeMap<(String, Key), Vec<u8>>>,
}

impl Default for BundleRecorder {
    fn default() -> Self {
        BundleRecorder {
            compiler: LibraryBundle::this_compiler(),
            entries: Default::default(),
        }
    }
}

impl BundleRecorder {
    /// The entries written so far, and `left_out`.
    pub fn finish(&self, left_out: std::collections::BTreeSet<String>) -> LibraryBundle {
        let entries = self.entries.take();
        let id = LibraryBundle::content_id(&self.compiler, &entries, &left_out);
        LibraryBundle {
            compiler: self.compiler.clone(),
            entries,
            left_out,
            id,
        }
    }
}

impl Store for BundleRecorder {
    fn compiler(&self) -> &str {
        &self.compiler
    }

    fn salt(&self) -> [u8; 16] {
        BUNDLE_SALT
    }

    fn read(&self, _: &str, _: &Key) -> Option<Vec<u8>> {
        None
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if unit.starts_with("std.") {
            (self.entries.borrow_mut()).insert((unit.to_string(), *key), entry.to_vec());
        }
    }
}

impl std::fmt::Debug for LibraryBundle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LibraryBundle")
            .field("compiler", &self.compiler)
            .field("entries", &self.entries.len())
            .field("left_out", &self.left_out)
            .finish()
    }
}

/// A check cache that keeps only library files' entries (unit names
/// `std.…`), not those of project namespaces: `--no-project-cache`.
pub struct LibraryOnly(pub CheckCache);

impl Store for LibraryOnly {
    fn compiler(&self) -> &str {
        self.0.compiler()
    }
    fn kernel(&self) -> &str {
        self.0.kernel()
    }
    fn salt(&self) -> [u8; 16] {
        self.0.salt()
    }
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        unit.starts_with("std.").then(|| self.0.read(unit, key))?
    }
    fn read_others(&self, unit: &str, key: &Key) -> Vec<Vec<u8>> {
        if unit.starts_with("std.") {
            self.0.read_others(unit, key)
        } else {
            Vec::new()
        }
    }
    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        if unit.starts_with("std.") {
            self.0.write(unit, key, entry);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_library_bundle_reads_back_and_only_in_its_own_build() {
        let recorder = BundleRecorder::default();
        recorder.write("std.List.Sort+nav+ty", &[1; 32], b"entry");
        // Only library files' entries are kept.
        recorder.write("ns.Aoc.Common+nav+ty", &[2; 32], b"namespace");
        let bundle = recorder.finish(["Float/Theory.sw".to_string()].into());
        let bytes = bundle.encode();
        let read = LibraryBundle::decode(&bytes).expect("this build's bundle");
        assert_eq!(read.len(), 1);
        assert_eq!(read.left_out, bundle.left_out);
        // The id is the content's, not the address's: it survives a round
        // trip, and other content has another.
        assert_eq!(read.id(), bundle.id());
        let different = BundleRecorder::default();
        different.write("std.List.Sort+nav+ty", &[4; 32], b"other entry");
        assert_ne!(different.finish(Default::default()).id(), bundle.id());
        let store = BundleStore(std::sync::Arc::new(read));
        assert_eq!(
            store.read("std.List.Sort+nav+ty", &[1; 32]).as_deref(),
            Some(&b"entry"[..])
        );
        assert_eq!(store.read("std.List.Sort+nav+ty", &[3; 32]), None);
        assert_eq!(store.salt(), recorder.salt());
        assert_eq!(store.compiler(), recorder.compiler());

        // Another build's bundle isn't read at all, and nor are bytes cut
        // short.
        let mut other = bytes.clone();
        let at = BUNDLE_MAGIC.len() + 8;
        other[at] ^= 1;
        assert!(LibraryBundle::decode(&other).is_none());
        assert!(LibraryBundle::decode(&bytes[..bytes.len() - 1]).is_none());
    }

    #[test]
    fn a_library_only_cache_keeps_library_entries_and_no_namespace_entries() {
        let dir =
            std::env::temp_dir().join(format!("stitchwort-library-only-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let store = LibraryOnly(CheckCache::at(&dir));
        store.write("std.List.Sort+nav+ty", &[1; 32], b"entry");
        store.write("ns.Aoc.Common+nav+ty", &[2; 32], b"namespace");
        assert_eq!(
            store.read("std.List.Sort+nav+ty", &[1; 32]).as_deref(),
            Some(&b"entry"[..])
        );
        assert_eq!(store.read("ns.Aoc.Common+nav+ty", &[2; 32]), None);
        // Not even written, so a plain cache on the same folder finds none.
        assert_eq!(
            CheckCache::at(&dir).read("ns.Aoc.Common+nav+ty", &[2; 32]),
            None
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn writes_from_many_threads_at_once_keep_their_own_temp_files() {
        const THREADS: usize = 8;
        const ENTRIES: usize = 32;
        let nanos = SystemTime::now()
            .duration_since(SystemTime::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        let dir = std::env::temp_dir().join(format!(
            "stitchwort-check-cache-threads-{}-{nanos}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        // Make the folder and its header first, so that what the threads
        // race is writing entries, not making the header.
        let _ = CheckCache::at(&dir);
        let key = |thread: usize, entry: usize| {
            let mut key = [0u8; 32];
            key[0] = thread as u8;
            key[1] = entry as u8;
            key
        };
        let unit = |thread: usize, entry: usize| format!("ns.Thread{thread}.Entry{entry}+nav+ty");
        let content = |thread: usize, entry: usize| format!("entry {thread} {entry}");
        let start = std::sync::Barrier::new(THREADS);
        let dir = &dir;
        std::thread::scope(|scope| {
            for thread in 0..THREADS {
                let (start, key, unit, content) = (&start, &key, &unit, &content);
                scope.spawn(move || {
                    // Its own cache over the shared folder, as two threads of
                    // one process would have (a cache isn't `Sync`).
                    let cache = CheckCache::at(dir);
                    start.wait();
                    for entry in 0..ENTRIES {
                        cache.write(
                            &unit(thread, entry),
                            &key(thread, entry),
                            content(thread, entry).as_bytes(),
                        );
                    }
                });
            }
        });
        // Every write landed, each file with its own thread's contents.
        let cache = CheckCache::at(dir);
        for thread in 0..THREADS {
            for entry in 0..ENTRIES {
                assert_eq!(
                    cache
                        .read(&unit(thread, entry), &key(thread, entry))
                        .as_deref(),
                    Some(content(thread, entry).as_bytes()),
                    "thread {thread}, entry {entry}"
                );
            }
        }
        // And none left a temporary file behind.
        let temps: Vec<PathBuf> = std::fs::read_dir(dir.join("check"))
            .unwrap()
            .flatten()
            .filter(|entry| entry.file_name().to_string_lossy().starts_with(".tmp-"))
            .map(|entry| entry.path())
            .collect();
        assert!(temps.is_empty(), "temporary files left: {temps:?}");
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn a_layered_store_reads_the_bundle_and_keeps_namespaces_only_two_to_a_unit() {
        let recorder = BundleRecorder::default();
        recorder.write("std.List.Sort+nav+ty", &[1; 32], b"entry");
        let bundle = std::sync::Arc::new(recorder.finish(Default::default()));
        let store = LayeredStore::new(bundle);
        assert_eq!(store.salt(), recorder.salt());
        assert_eq!(store.compiler(), recorder.compiler());
        assert_eq!(
            store.read("std.List.Sort+nav+ty", &[1; 32]).as_deref(),
            Some(&b"entry"[..])
        );

        // The library is not written to; a namespace is, and found again.
        store.write("std.List.Sort+nav+ty", &[2; 32], b"other");
        assert_eq!(store.read("std.List.Sort+nav+ty", &[2; 32]), None);
        assert_eq!(store.namespace_entries(), 0);
        store.write("ns.A+nav+ty", &[1; 32], b"one");
        assert_eq!(
            store.read("ns.A+nav+ty", &[1; 32]).as_deref(),
            Some(&b"one"[..])
        );
        assert_eq!(store.read("ns.A+nav+ty", &[9; 32]), None);

        // Two to a unit: the third write drops the oldest, so the one before
        // the edit is still there for an undo. Other units are untouched.
        store.write("ns.B+nav+ty", &[1; 32], b"b");
        store.write("ns.A+nav+ty", &[2; 32], b"two");
        store.write("ns.A+nav+ty", &[3; 32], b"three");
        assert_eq!(store.read("ns.A+nav+ty", &[1; 32]), None);
        assert!(store.read("ns.A+nav+ty", &[2; 32]).is_some());
        assert!(store.read("ns.A+nav+ty", &[3; 32]).is_some());
        assert!(store.read("ns.B+nav+ty", &[1; 32]).is_some());
        assert_eq!(store.namespace_entries(), 3);
        assert_eq!(
            store.namespace_bytes(),
            "two".len() + "three".len() + "b".len()
        );

        // Writing the same key again replaces it without counting it twice.
        store.write("ns.A+nav+ty", &[3; 32], b"3");
        assert_eq!(store.namespace_entries(), 3);
        assert_eq!(store.namespace_bytes(), "two".len() + "3".len() + "b".len());
    }

    #[test]
    fn a_layered_store_stays_under_its_cap_dropping_the_oldest() {
        let store = LayeredStore::new(Default::default());
        let big = vec![0u8; LAYER_CAP_BYTES / 3 + 1];
        for i in 0..4u8 {
            store.write(&format!("ns.U{i}+nav+ty"), &[i; 32], &big);
        }
        assert!(store.namespace_bytes() <= LAYER_CAP_BYTES);
        assert_eq!(store.namespace_entries(), 2);
        assert_eq!(store.read("ns.U0+nav+ty", &[0; 32]), None);
        assert!(store.read("ns.U3+nav+ty", &[3; 32]).is_some());
    }

    #[test]
    fn a_layered_store_sharing_a_budget_is_capped_with_the_others() {
        // Two projects' stores share one cap (SW-3072): the second's writes
        // drop its own oldest entries rather than the first's.
        let budget = LayerBudget::default();
        let a = LayeredStore::with_budget(Default::default(), budget.clone());
        let b = LayeredStore::with_budget(Default::default(), budget.clone());
        let first = vec![0u8; LAYER_CAP_BYTES - 1024];
        a.write("ns.A+nav+ty", &[1; 32], &first);
        let small = vec![0u8; 2048];
        b.write("ns.B+nav+ty", &[1; 32], &small);
        // `b` keeps its newest entry, so the total may be one entry over.
        assert!(budget.used() <= LAYER_CAP_BYTES + small.len());
        assert!(b.read("ns.B+nav+ty", &[1; 32]).is_some());
        b.write("ns.B+nav+ty", &[2; 32], &small);
        assert_eq!(b.namespace_entries(), 1);
        assert!(b.read("ns.B+nav+ty", &[1; 32]).is_none());
        assert!(b.read("ns.B+nav+ty", &[2; 32]).is_some());
        assert!(a.read("ns.A+nav+ty", &[1; 32]).is_some());

        // Clearing a store gives its bytes back; dropping it does too.
        a.clear();
        assert_eq!(a.namespace_entries(), 0);
        assert!(budget.used() <= small.len());
        drop(a);
        assert_eq!(budget.used(), small.len());
        drop(b);
        assert_eq!(budget.used(), 0);
    }
}
