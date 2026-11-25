//! The library's name index kept on disk, so that a run reads it instead of
//! parsing every library file and resolving its names (SW-4812).
//!
//! The index is not trusted by the kernel, but the check cache's keys read
//! it: a file's `edges` decide which other files' keys go into its key, and
//! the names are part of every key and stamp. An index that didn't match the
//! files would let the check cache replay an entry whose dependency had
//! changed. So, as the check cache does (docs/proposals/check-cache-trust.md),
//! it is found by the content actually read, never by modification times:
//!
//! - **The key** covers a format number, the compiler's stamp (the
//!   elaborator's and the parser's sources, as the check cache's entries
//!   name their build), the parser's stack budget, the core's text, and
//!   every library file's path and text, in the order the index numbers
//!   them. Any edit, added, removed or renamed file, or another
//!   `--std-dir` with other content is a miss; two folders with the same
//!   content share an index, rightly.
//! - **An entry** is its key and a hash of its body, then the body: each
//!   file's names, edges and named equations. The rest of the index (each
//!   name's owner, the dot targets) is computed from those as building it
//!   does, and the files' modules are parsed when first asked for
//!   ([`IndexedFile::module`]). Reading checks the key and the hash and
//!   decodes the whole body; anything else is a miss, and the index is
//!   built as if there were no entry.
//! - **Only what built cleanly is written**: a build error (a name declared
//!   twice) is reported as before and nothing is written, and an index with
//!   a file that has syntax errors isn't written either (its errors are
//!   reported from the parse, which then has to run anyway).
//! - **Writing** goes to a temporary file that is renamed into place, so
//!   processes and workers starting together never see half an entry.
//!   Entries not used for a day are removed when another is written.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::time::{Duration, SystemTime};

use stitchwort_core::collections::HashMap;
use stitchwort_syntax::{FileId, SourceMap, Span};

use super::{IndexedFile, IndexedName, LibraryIndex, PendingKind, dots_by_short};
use crate::cache::codec::{Bad, Read, Reader, Writer, bad};

/// Changes whenever what an entry holds, or how, changes.
const FORMAT: u32 = 1;

/// How an entry starts.
const MAGIC: &[u8; 8] = b"swindex\n";

/// How long an entry no run has written or read is kept.
const GRACE: Duration = Duration::from_secs(24 * 60 * 60);

/// A folder of library indexes, for one build of the compiler.
pub struct IndexCache {
    dir: PathBuf,
    compiler: String,
}

static CONFIGURED: OnceLock<IndexCache> = OnceLock::new();

/// Makes [`LibraryIndex::standard`] read and write its index in `dir`, for
/// a compiler whose stamp is `compiler` (what the check cache's entries
/// name). Call it before the index is first asked for; later calls, and
/// calls after that, change nothing. Without it the index is built.
pub fn use_index_cache(dir: &Path, compiler: &str) {
    let _ = CONFIGURED.set(IndexCache::new(dir, compiler));
}

pub(super) fn configured() -> Option<&'static IndexCache> {
    CONFIGURED.get()
}

impl IndexCache {
    pub fn new(dir: &Path, compiler: &str) -> IndexCache {
        IndexCache {
            dir: dir.to_path_buf(),
            compiler: compiler.to_string(),
        }
    }

    /// The index of `core` and `files`, as [`LibraryIndex::build`] makes it,
    /// and whether it was read from this folder rather than built.
    pub fn index(
        &self,
        core: &str,
        files: &[(&str, &str)],
        stack: usize,
    ) -> Result<(LibraryIndex, bool), String> {
        let key = key(&self.compiler, core, files, stack);
        let path = self.entry(&key);
        if let Ok(bytes) = std::fs::read(&path)
            && let Ok(index) = read(&bytes, &key, core, files, stack)
        {
            touch(&path);
            return Ok((index, true));
        }
        let index = LibraryIndex::build(core, files, stack)?;
        if let Some(body) = encode(&index) {
            self.write(&path, &key, &body);
        }
        Ok((index, false))
    }

    /// Where the entry for `key` is kept.
    pub fn entry(&self, key: &[u8; 32]) -> PathBuf {
        self.dir
            .join(blake3::Hash::from_bytes(*key).to_hex().as_str())
    }

    /// The key of the index of `core` and `files` (see the module's
    /// documentation).
    pub fn key(&self, core: &str, files: &[(&str, &str)], stack: usize) -> [u8; 32] {
        key(&self.compiler, core, files, stack)
    }

    /// Writes an entry, quietly giving up if the folder can't be written:
    /// the index was built, and the next run builds it again.
    fn write(&self, path: &Path, key: &[u8; 32], body: &[u8]) {
        if std::fs::create_dir_all(&self.dir).is_err() {
            return;
        }
        let mut bytes = Vec::with_capacity(MAGIC.len() + 64 + body.len());
        bytes.extend_from_slice(MAGIC);
        bytes.extend_from_slice(key);
        bytes.extend_from_slice(blake3::hash(body).as_bytes());
        bytes.extend_from_slice(body);
        let temporary = self.dir.join(format!(
            ".{}.{}.{:?}.tmp",
            blake3::Hash::from_bytes(*key).to_hex(),
            std::process::id(),
            std::thread::current().id()
        ));
        if std::fs::write(&temporary, &bytes).is_err() || std::fs::rename(&temporary, path).is_err()
        {
            let _ = std::fs::remove_file(&temporary);
            return;
        }
        self.sweep(path);
    }

    /// Removes the entries (and abandoned temporary files) not used for
    /// [`GRACE`], other than `kept`.
    fn sweep(&self, kept: &Path) {
        let Ok(entries) = std::fs::read_dir(&self.dir) else {
            return;
        };
        let now = SystemTime::now();
        for entry in entries.flatten() {
            let path = entry.path();
            let old = (entry.metadata().and_then(|m| m.modified()).ok())
                .and_then(|when| now.duration_since(when).ok())
                .is_some_and(|age| age > GRACE);
            if old && path != kept {
                let _ = std::fs::remove_file(&path);
            }
        }
    }
}

/// Marks an entry as used, so that the sweep keeps it. Only the sweep reads
/// the time: whether an entry is used depends on its content alone.
fn touch(path: &Path) {
    if let Ok(file) = std::fs::File::options().append(true).open(path) {
        let _ = file.set_modified(SystemTime::now());
    }
}

/// The core first, then the library files by path: the index's numbering.
fn ordered<'a>(core: &'a str, files: &[(&'a str, &'a str)]) -> Vec<(&'a str, &'a str)> {
    let mut sorted: Vec<(&str, &str)> = files.to_vec();
    sorted.sort_by_key(|(path, _)| *path);
    std::iter::once(("core", core)).chain(sorted).collect()
}

fn key(compiler: &str, core: &str, files: &[(&str, &str)], stack: usize) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    let mut field = |bytes: &[u8]| {
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    field(b"stitchwort library index");
    field(&FORMAT.to_le_bytes());
    field(compiler.as_bytes());
    field(&(stack as u64).to_le_bytes());
    let ordered = ordered(core, files);
    field(&(ordered.len() as u64).to_le_bytes());
    for (path, text) in ordered {
        field(path.as_bytes());
        field(text.as_bytes());
    }
    *hasher.finalize().as_bytes()
}

/// The body of an entry for `index`, or `None` if it isn't one to keep: a
/// file has syntax errors, or a name's span is in no file of the index.
fn encode(index: &LibraryIndex) -> Option<Vec<u8>> {
    let files = index.files.len();
    let mut w = Writer::default();
    w.usize(files);
    for file in &index.files {
        if !file.parse_errors.is_empty() {
            return None;
        }
        w.str(&file.path);
        w.usize(file.names.len());
        for name in &file.names {
            w.str(&name.key);
            w.u8(match name.kind {
                PendingKind::Def => 0,
                PendingKind::Data => 1,
                PendingKind::Ctor => 2,
                PendingKind::Op => 3,
                PendingKind::Other => 4,
            });
            w.u8(u8::from(name.follower)
                | u8::from(name.function) << 1
                | u8::from(name.candidate) << 2
                | u8::from(name.accessor) << 3);
            let span_file = if name.span.file == FileId::SCRATCH {
                u32::MAX
            } else if name.span.file.index() < files {
                name.span.file.index() as u32
            } else {
                return None;
            };
            w.uint(u64::from(span_file));
            w.uint(u64::from(name.span.start));
            w.uint(u64::from(name.span.end));
        }
        w.usize(file.edges.len());
        for &e in &file.edges {
            w.usize(e);
        }
        w.usize(file.equation_needs.len());
        for key in &file.equation_needs {
            w.str(key);
        }
    }
    Some(w.bytes)
}

/// The index an entry holds for `core` and `files`, if the entry is whole
/// and is for them.
fn read(
    bytes: &[u8],
    key: &[u8; 32],
    core: &str,
    files: &[(&str, &str)],
    stack: usize,
) -> Read<LibraryIndex> {
    let mut r = Reader::new(bytes);
    if r.array::<8>()? != *MAGIC || r.array::<32>()? != *key {
        return bad("not this index's entry");
    }
    let hash = r.array::<32>()?;
    let body = &bytes[MAGIC.len() + 64..];
    if blake3::hash(body).as_bytes() != &hash {
        return bad("the entry is damaged");
    }
    decode(body, core, files, stack)
}

fn decode(body: &[u8], core: &str, files: &[(&str, &str)], stack: usize) -> Read<LibraryIndex> {
    let ordered = ordered(core, files);
    let mut r = Reader::new(body);
    if r.usize()? != ordered.len() {
        return bad("another number of files");
    }
    // The ids building gives the files, in the same order.
    let mut sources = SourceMap::new();
    let ids: Vec<FileId> = (ordered.iter())
        .map(|(path, _)| sources.add(*path, ""))
        .collect();
    let mut parsed: Vec<IndexedFile> = Vec::with_capacity(ordered.len());
    for (&(path, text), &id) in ordered.iter().zip(&ids) {
        if r.string()? != path {
            return bad("another file");
        }
        let count = r.count(6)?;
        let mut names = Vec::with_capacity(count);
        for _ in 0..count {
            let key = r.string()?;
            let kind = match r.u8()? {
                0 => PendingKind::Def,
                1 => PendingKind::Data,
                2 => PendingKind::Ctor,
                3 => PendingKind::Op,
                4 => PendingKind::Other,
                _ => return bad("an unknown kind of name"),
            };
            let flags = r.u8()?;
            if flags >> 4 != 0 {
                return bad("unknown flags");
            }
            let file = match r.u32()? {
                u32::MAX => FileId::SCRATCH,
                f => *ids.get(f as usize).ok_or(Bad("a span in no file".into()))?,
            };
            let span = Span {
                file,
                start: r.u32()?,
                end: r.u32()?,
            };
            names.push(IndexedName {
                key,
                kind,
                follower: flags & 1 != 0,
                function: flags & 2 != 0,
                candidate: flags & 4 != 0,
                accessor: flags & 8 != 0,
                span,
            });
        }
        let count = r.count(1)?;
        let mut edges = Vec::with_capacity(count);
        for _ in 0..count {
            let e = r.usize()?;
            if e >= ordered.len() {
                return bad("an edge to no file");
            }
            edges.push(e);
        }
        let count = r.count(1)?;
        let mut equation_needs = std::collections::BTreeSet::new();
        for _ in 0..count {
            equation_needs.insert(r.string()?);
        }
        parsed.push(IndexedFile {
            path: path.to_string(),
            id,
            text: text.to_string(),
            parsed: OnceLock::new(),
            stack,
            parse_errors: Vec::new(),
            names,
            edges,
            equation_needs,
        });
    }
    if !r.done() {
        return bad("more than the index");
    }
    let mut owner: HashMap<String, usize> = HashMap::default();
    for (f, file) in parsed.iter().enumerate() {
        for name in &file.names {
            if owner.insert(name.key.clone(), f).is_some() {
                return bad("a name declared twice");
            }
        }
    }
    let dots_by_short = dots_by_short(&parsed, &owner);
    Ok(LibraryIndex {
        files: parsed,
        owner,
        dots_by_short,
    })
}
