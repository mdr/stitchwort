//! Where the check cache keeps its entries (docs/proposals/check-cache.md
//! §6): `check/` in a cache directory (`.stitchwort/cache` in the project,
//! next to `tests/`), one file per entry.
//!
//! - **Names.** An entry's file is `{fingerprint}-{unit}-{key}`: the
//!   compiler build, the unit (a library file, `std.List.Toolkit`, or a
//!   project namespace, `ns.Aoc.Year2025.Day05`; `+nav` when navigation is
//!   recorded), and the entry's key in hex.
//! - **The header.** `check/header` holds the directory's random salt
//!   (§3.1), made the first time the directory is used. Every entry
//!   carries it, so an entry copied from another cache directory is a miss.
//! - **Writing** goes to a temporary file that is then renamed, so a reader
//!   never sees half an entry, and two writers at once (the editor and a
//!   command) just leave the last one.
//! - **Eviction (D283).** Writing an entry deletes the unit's other entries
//!   for this build; the first write of a run deletes entries of other
//!   builds that are more than a day old (two builds may share a project
//!   folder, hence the grace period).
//!
//! The elaborator encodes, checks and replays entries; this only stores
//! them.

use std::cell::Cell;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use stitchwort_elab::cache::{Key, Store};

use crate::driver::FINGERPRINT;

/// How long entries of other builds are kept.
pub(crate) const GRACE: Duration = Duration::from_secs(24 * 60 * 60);

/// A check cache in a directory.
pub struct CheckCache {
    dir: PathBuf,
    compiler: String,
    salt: [u8; 16],
    /// Whether this run has written yet (the first write sweeps).
    written: Cell<bool>,
    /// How long entries of other builds are kept.
    grace: Duration,
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
        let dir = cache_dir.join("check");
        let salt = salt(&dir);
        CheckCache {
            dir,
            compiler: format!("stitchwort-{}-{}", env!("CARGO_PKG_VERSION"), FINGERPRINT),
            salt,
            written: Cell::new(false),
            grace,
        }
    }

    fn file(&self, unit: &str, key: &Key) -> PathBuf {
        self.dir
            .join(format!("{}-{unit}-{}", FINGERPRINT, hex(key)))
    }

    /// Deletes this unit's other entries for this build, and on the first
    /// write of a run, other builds' entries older than [`GRACE`] and
    /// temporary files left behind.
    fn evict(&self, unit: &str, keep: &Path) {
        let first = !self.written.replace(true);
        let Ok(entries) = std::fs::read_dir(&self.dir) else {
            return;
        };
        let own = format!("{}-{unit}-", FINGERPRINT);
        let now = SystemTime::now();
        for entry in entries.flatten() {
            let path = entry.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if name == "header" || path == keep {
                continue;
            }
            let stale = name.starts_with(&own)
                || (first
                    && !name.starts_with(&format!("{}-", FINGERPRINT))
                    && entry
                        .metadata()
                        .and_then(|m| m.modified())
                        .ok()
                        .and_then(|t| now.duration_since(t).ok())
                        .is_some_and(|age| age > self.grace));
            if stale {
                let _ = std::fs::remove_file(&path);
            }
        }
    }
}

impl Store for CheckCache {
    fn compiler(&self) -> &str {
        &self.compiler
    }

    fn salt(&self) -> [u8; 16] {
        self.salt
    }

    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        std::fs::read(self.file(unit, key)).ok()
    }

    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        let path = self.file(unit, key);
        if write_atomically(&self.dir, &path, entry).is_ok() {
            self.evict(unit, &path);
        }
    }
}

/// Writes `bytes` to `path` in `dir` by way of a temporary file there.
fn write_atomically(dir: &Path, path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let nanos = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let temp = dir.join(format!(".tmp-{}-{nanos}", std::process::id()));
    let result = std::fs::write(&temp, bytes).and_then(|()| std::fs::rename(&temp, path));
    if result.is_err() {
        let _ = std::fs::remove_file(&temp);
    }
    result
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
///   compiler build, the modes and limits, and the file's text and its
///   dependencies' keys; so a bundle from another build, or a session made
///   differently, finds only misses, and the file is checked as without a
///   cache. A bundle from another compiler is not read at all
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
        Some(LibraryBundle {
            compiler,
            entries,
            left_out: left.lines().map(str::to_string).collect(),
        })
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
        LibraryBundle {
            compiler: self.compiler.clone(),
            entries: self.entries.take(),
            left_out,
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
