//! The library's name index kept on disk (SW-4812): an index read from its
//! cache is the one building gives, field by field, and any change to what
//! the index is made from is a miss.

use std::path::PathBuf;
use std::sync::Arc;

use stitchwort_driver::driver::Session;
use stitchwort_elab::{IndexCache, LibraryIndex, library_files, prelude};

const STACK: usize = 16 * 1024 * 1024;

/// A new, empty folder for one test.
fn scratch(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-index-cache-{name}-{}-{nanos}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Every field of the index a reader uses, written out: two indexes are
/// the same to their readers when these are equal.
fn described(index: &LibraryIndex) -> Vec<String> {
    let mut out = Vec::new();
    let mut shorts = std::collections::BTreeSet::new();
    for (f, file) in index.files.iter().enumerate() {
        out.push(format!(
            "file {f}: {} {:?} text {} parse errors {:?}",
            file.path,
            file.id,
            blake3::hash(file.text.as_bytes()).to_hex(),
            file.parse_errors
        ));
        for name in &file.names {
            out.push(format!("  {name:?} owner {:?}", index.owner(&name.key)));
            shorts.insert(name.key.rsplit('.').next().unwrap().to_string());
        }
        out.push(format!("  edges {:?}", file.edges));
        out.push(format!("  equations {:?}", file.equation_needs));
        let module = format!("{:?}", file.module());
        out.push(format!(
            "  module {}",
            blake3::hash(module.as_bytes()).to_hex()
        ));
    }
    for short in shorts {
        out.push(format!("dots {short}: {:?}", index.dot_targets(&short)));
    }
    out.push(format!(
        "candidates {:?}",
        index.candidates().collect::<Vec<_>>()
    ));
    let mut names: Vec<_> = index.names().collect();
    names.sort();
    out.push(format!("names {names:?}"));
    out
}

fn assert_same(built: &LibraryIndex, cached: &LibraryIndex) {
    let (built, cached) = (described(built), described(cached));
    assert_eq!(built.len(), cached.len(), "the descriptions' lengths");
    for (b, c) in built.iter().zip(&cached) {
        assert_eq!(b, c, "the built index, then the cached one");
    }
}

/// The real library's index, built and then read back from its cache,
/// agrees in every field a reader uses, the files' parses included.
#[test]
fn a_cached_std_index_is_the_built_one() {
    let dir = scratch("same");
    let cache = IndexCache::new(&dir, "test-compiler");
    let (built, from_cache) = cache.index(prelude(), library_files(), STACK).unwrap();
    assert!(!from_cache, "an empty folder has no index");
    let (cached, from_cache) = cache.index(prelude(), library_files(), STACK).unwrap();
    assert!(from_cache, "the index written is read back");
    assert_same(&built, &cached);
    let fresh = LibraryIndex::build(prelude(), library_files(), STACK).unwrap();
    assert_same(&fresh, &cached);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A small library: two files, one using the other.
const A: (&str, &str) = ("A.sw", "def Lib.Tools.double (n: Nat): Nat := n + n\n");
const B: (&str, &str) = (
    "B.sw",
    "import Lib.Tools (double)\n\
     def Lib.quadruple (n: Nat): Nat := double (double n)\n",
);

fn keys(index: &LibraryIndex) -> Vec<String> {
    (index.files.iter())
        .flat_map(|f| f.names.iter().map(|n| n.key.clone()))
        .collect()
}

/// Editing a file, adding or removing one, changing the core or the
/// compiler each find no entry, and the index then answers for the files
/// given; the same files again find theirs.
#[test]
fn a_change_to_the_library_misses_the_cached_index() {
    let dir = scratch("miss");
    let cache = IndexCache::new(&dir, "test-compiler");
    let index = |cache: &IndexCache, core: &str, files: &[(&str, &str)]| {
        cache.index(core, files, STACK).unwrap()
    };
    let (_, hit) = index(&cache, prelude(), &[A, B]);
    assert!(!hit);
    let (_, hit) = index(&cache, prelude(), &[B, A]);
    assert!(hit, "the same files, in another order");

    let edited = (
        "A.sw",
        "def Lib.Tools.double (n: Nat): Nat := n + n\n\
         def Lib.Tools.triple (n: Nat): Nat := n + n + n\n",
    );
    let (built, hit) = index(&cache, prelude(), &[edited, B]);
    assert!(!hit, "an edited file");
    assert!(keys(&built).contains(&"Std.Lib.Tools.triple".to_string()));
    let (cached, hit) = index(&cache, prelude(), &[edited, B]);
    assert!(hit);
    assert_same(&built, &cached);

    let added = ("C.sw", "def Lib.half (n: Nat): Nat := n / 2\n");
    let (built, hit) = index(&cache, prelude(), &[A, B, added]);
    assert!(!hit, "an added file");
    assert!(keys(&built).contains(&"Std.Lib.half".to_string()));

    let (built, hit) = index(&cache, prelude(), &[B]);
    assert!(!hit, "a removed file");
    assert!(!keys(&built).contains(&"Std.Lib.Tools.double".to_string()));

    let renamed = ("Z.sw", A.1);
    let (built, hit) = index(&cache, prelude(), &[renamed, B]);
    assert!(!hit, "a renamed file");
    assert_eq!(
        built.files[built.owner("Std.Lib.Tools.double").unwrap()].path,
        "Z.sw"
    );

    let core = format!("{}\ndef Std.coreExtra: Nat := 0\n", prelude());
    let (built, hit) = index(&cache, &core, &[A, B]);
    assert!(!hit, "a changed core");
    assert_eq!(built.owner("Std.coreExtra"), Some(0));

    let other = IndexCache::new(&dir, "another-compiler");
    let (_, hit) = index(&other, prelude(), &[A, B]);
    assert!(!hit, "another compiler");

    let (_, hit) = cache.index(prelude(), &[A, B], STACK / 2).unwrap();
    assert!(!hit, "another stack budget");
    let _ = std::fs::remove_dir_all(&dir);
}

/// A damaged or cut-short entry is passed over silently: the index is
/// built as if there were none, and written again.
#[test]
fn a_damaged_cached_index_is_built_again() {
    let dir = scratch("damaged");
    let cache = IndexCache::new(&dir, "test-compiler");
    let (built, _) = cache.index(prelude(), &[A, B], STACK).unwrap();
    let entry = cache.entry(&cache.key(prelude(), &[A, B], STACK));
    let bytes = std::fs::read(&entry).unwrap();
    let mut flipped = bytes.clone();
    let last = flipped.len() - 1;
    flipped[last] ^= 1;
    for damaged in [flipped, bytes[..bytes.len() / 2].to_vec(), Vec::new()] {
        std::fs::write(&entry, &damaged).unwrap();
        let (index, hit) = cache.index(prelude(), &[A, B], STACK).unwrap();
        assert!(!hit, "a damaged entry is a miss");
        assert_same(&built, &index);
        assert_eq!(
            std::fs::read(&entry).unwrap(),
            bytes,
            "and is written again"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// An index that doesn't build is reported as before, and nothing is
/// written; nor is one with a file that has syntax errors, whose errors
/// come from parsing it.
#[test]
fn an_index_that_does_not_build_cleanly_is_not_cached() {
    let dir = scratch("unclean");
    let cache = IndexCache::new(&dir, "test-compiler");
    let twice = [
        ("A.sw", "def Lib.twice: Nat := 0\n"),
        ("B.sw", "def Lib.twice: Nat := 1\n"),
    ];
    let error = cache.index(prelude(), &twice, STACK).err();
    assert!(error.is_some_and(|e| e.contains("Std.Lib.twice")));
    assert!(!cache.entry(&cache.key(prelude(), &twice, STACK)).exists());

    let broken = [A, ("B.sw", "def Lib.broken (n: Nat): Nat := (n +\n")];
    let (index, _) = cache.index(prelude(), &broken, STACK).unwrap();
    assert!(!index.files[2].parse_errors.is_empty());
    let (again, hit) = cache.index(prelude(), &broken, STACK).unwrap();
    assert!(!hit, "a file with syntax errors is never cached");
    assert_eq!(
        again.files[2].parse_errors.len(),
        index.files[2].parse_errors.len()
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// The check cache finds, under a cached index, every library entry a
/// session under the built index wrote: the keys are the same.
#[test]
fn a_cached_std_index_gives_the_same_check_cache_keys() {
    let dir = scratch("keys");
    let index_cache = IndexCache::new(&dir.join("index"), "test-compiler");
    let (built, _) = index_cache
        .index(prelude(), library_files(), STACK)
        .unwrap();
    let (cached, hit) = index_cache
        .index(prelude(), library_files(), STACK)
        .unwrap();
    assert!(hit);
    let program = "import Std (List, Nat)\n\
                   def total: Nat := [3, 1, 2].sort.sum\n";
    let listing = || {
        let mut names: Vec<String> = std::fs::read_dir(dir.join("check"))
            .unwrap()
            .flatten()
            .map(|e| e.file_name().into_string().unwrap())
            .collect();
        names.sort();
        names
    };
    let mut first = Session::with_library_index(&Arc::new(built)).unwrap();
    first.use_library_check_cache(&dir);
    first
        .load("t.sw", program)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let written = first.elab.check_cache_stats();
    assert!(written.written > 0, "library entries are written");
    let before = listing();
    let mut second = Session::with_library_index(&Arc::new(cached)).unwrap();
    second.use_library_check_cache(&dir);
    second
        .load("t.sw", program)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let read = second.elab.check_cache_stats();
    assert_eq!(read.misses, 0, "every library file is found");
    assert_eq!(read.hits, written.written + written.hits);
    assert_eq!(listing(), before, "and nothing new is written");
    let _ = std::fs::remove_dir_all(&dir);
}
