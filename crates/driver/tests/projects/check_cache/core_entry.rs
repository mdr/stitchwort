//! The core's entry (SW-4814, docs/reviews/SW-4814-core-from-cache.md): a
//! session whose core comes from the check cache holds exactly what one
//! that elaborated it holds, as the canonical dump prints it, with every
//! declaration's three hashes (worked out again, not only as recorded) and
//! the warnings the core keeps; so does a program loaded after it. An entry
//! that doesn't fit is a miss, one refused part way starts the session
//! again from source, and a core of its own has entries of its own.

use std::path::Path;

use stitchwort_core::DefId;
use stitchwort_core::hash::{data_hash, def_hash, interface_hash};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::render::render;
use stitchwort_elab::cache::{Stats, canonical_dump};

use super::{STACK, entries, first_difference, small_program, temp_dir};

/// What a session holds once started, and once it has loaded a program.
#[derive(PartialEq)]
struct Started {
    dump: String,
    hashes: String,
    warnings: String,
    program: String,
}

impl std::fmt::Debug for Started {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<a started session>")
    }
}

/// Every declaration's content hash, interface hash and data hash: as the
/// session has them (a replay seeds what its entry records), then worked
/// out again from the terms.
fn hashes(session: &Session) -> String {
    let mut out = String::new();
    for again in [false, true] {
        if again {
            session.elab.kernel.caches.hashes.borrow_mut().clear();
        }
        let g = &session.elab.ev();
        let _op = g
            .machine
            .budget
            .operation(stitchwort_core::Limits::default());
        for (i, def) in g.env.defs().iter().enumerate() {
            let id = DefId(i);
            out.push_str(&format!(
                "def {} {:?} {:?}\n",
                def.path(),
                def_hash(g, id).ok().flatten(),
                interface_hash(g, id).ok().flatten()
            ));
        }
        for (i, data) in g.env.datas().iter().enumerate() {
            out.push_str(&format!(
                "data {} {:?}\n",
                data.path(),
                data_hash(g, stitchwort_core::DataId(i)).ok().flatten()
            ));
        }
    }
    out
}

/// Starts a session whose core is `prelude`, through the core's entry in
/// `cache` if given (checked again with `recheck`, refused after
/// `refuse`), and compares it after the start and after a program.
fn start(
    prelude: &str,
    cache: Option<&Path>,
    recheck: bool,
    navigation: bool,
    refuse: Option<&str>,
) -> (Started, Stats) {
    let prelude = prelude.to_string();
    let cache = cache.map(Path::to_path_buf);
    let refuse = refuse.map(str::to_string);
    with_stack(STACK, move || {
        let mut session = match &cache {
            Some(dir) => {
                Session::with_core_cache(&prelude, dir, recheck, navigation, refuse.as_deref())
                    .unwrap_or_else(|report| panic!("{report}"))
            }
            None if navigation => {
                assert_eq!(prelude, stitchwort_elab::prelude());
                Session::navigable()
            }
            None => Session::with_prelude(&prelude),
        };
        let stats = session.elab.check_cache_stats();
        let dump = canonical_dump(&session.elab);
        let hashes = hashes(&session);
        let warnings: String = (session.elab.library_warnings.iter())
            .map(|d| render(&session.sources, d, false))
            .collect();
        session.elab.options.limits = stitchwort_core::Limits::for_stack(STACK);
        let super::Source::File(name, text) = small_program() else {
            unreachable!()
        };
        let loaded = session.load(&name, &text);
        let mut program = canonical_dump(&session.elab);
        program.push_str(&format!("accepted {}\n", loaded.is_ok()));
        for d in loaded.err().unwrap_or_else(|| session.warnings.clone()) {
            program.push_str(&render(&session.sources, &d, false));
        }
        (
            Started {
                dump,
                hashes,
                warnings,
                program,
            },
            stats,
        )
    })
}

fn assert_same(fresh: &Started, cached: &Started) {
    assert!(
        fresh.dump == cached.dump,
        "the started sessions differ: {}",
        first_difference(&fresh.dump, &cached.dump)
    );
    assert!(
        fresh.hashes == cached.hashes,
        "their hashes differ: {}",
        first_difference(&fresh.hashes, &cached.hashes)
    );
    assert_eq!(fresh.warnings, cached.warnings, "the core's kept warnings");
    assert!(
        fresh.program == cached.program,
        "the sessions differ after a program: {}",
        first_difference(&fresh.program, &cached.program)
    );
}

/// The core's entries in a cache directory.
fn core_entries(dir: &Path) -> Vec<std::path::PathBuf> {
    entries(dir)
        .into_iter()
        .filter(|p| p.file_name().unwrap().to_str().unwrap().contains("-core"))
        .collect()
}

fn the_core_loads_the_same(navigation: bool) {
    let prelude = stitchwort_elab::prelude();
    let dir = temp_dir("core-entry");
    let (fresh, none) = start(prelude, None, false, navigation, None);
    assert_eq!(none.core_misses + none.core_hits + none.core_written, 0);
    let (cold, stats) = start(prelude, Some(&dir), false, navigation, None);
    assert_eq!((stats.core_misses, stats.core_written), (1, 1));
    assert_same(&fresh, &cold);
    assert_eq!(core_entries(&dir).len(), 1);
    let (warm, stats) = start(prelude, Some(&dir), false, navigation, None);
    assert_eq!(
        (stats.core_hits, stats.core_misses, stats.core_written),
        (1, 0, 0)
    );
    assert_eq!(stats.refused, 0);
    assert_same(&fresh, &warm);
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn the_core_loads_the_same_from_its_entry() {
    the_core_loads_the_same(false);
}

#[test]
fn the_core_loads_the_same_from_its_entry_with_navigation() {
    the_core_loads_the_same(true);
}

/// `check --recheck`'s path: the entry's declarations go through this
/// kernel's checking calls, with the same result.
#[test]
fn the_core_checked_again_from_its_entry_is_the_same() {
    let prelude = stitchwort_elab::prelude();
    let dir = temp_dir("core-recheck");
    let (fresh, _) = start(prelude, None, false, false, None);
    start(prelude, Some(&dir), false, false, None);
    let (again, stats) = start(prelude, Some(&dir), true, false, None);
    assert_eq!((stats.core_hits, stats.core_rechecked), (1, 1));
    assert_eq!(stats.refused_on_recheck, 0);
    assert_same(&fresh, &again);
    let _ = std::fs::remove_dir_all(&dir);
}

/// A core of its own (a test's changed prelude) misses the standard core's
/// entry, and then finds its own. A unit keeps one entry (writing one
/// deletes the unit's older ones), so the standard core then misses too.
#[test]
fn a_core_of_its_own_misses_the_standard_entry_and_hits_its_own() {
    let dir = temp_dir("core-own");
    start(stitchwort_elab::prelude(), Some(&dir), false, false, None);
    let other = format!(
        "{}\n-- Only in this test's core.\ndef sw4814Marker: Nat := 0\n",
        stitchwort_elab::prelude()
    );
    let (fresh, _) = start(&other, None, false, false, None);
    let (first, stats) = start(&other, Some(&dir), false, false, None);
    assert_eq!(
        (stats.core_hits, stats.core_misses, stats.core_written),
        (0, 1, 1),
        "the standard core's entry was replayed"
    );
    assert_same(&fresh, &first);
    assert_eq!(
        core_entries(&dir).len(),
        1,
        "the unit's older entry deleted"
    );
    let (second, stats) = start(&other, Some(&dir), false, false, None);
    assert_eq!((stats.core_hits, stats.core_misses), (1, 0));
    assert_same(&fresh, &second);
    let (_, stats) = start(stitchwort_elab::prelude(), Some(&dir), false, false, None);
    assert_eq!(
        (stats.core_hits, stats.core_misses),
        (0, 1),
        "the other core's entry was replayed"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A corrupt entry is a miss before anything changes: the core is
/// elaborated in the same session and its entry written again as it was.
#[test]
fn a_corrupt_core_entry_is_a_miss_and_is_rewritten() {
    let prelude = stitchwort_elab::prelude();
    let dir = temp_dir("core-corrupt");
    let (fresh, _) = start(prelude, None, false, false, None);
    start(prelude, Some(&dir), false, false, None);
    let [path] = &core_entries(&dir)[..] else {
        panic!("one entry for the core")
    };
    let original = std::fs::read(path).unwrap();
    let mut bytes = original.clone();
    let at = bytes.len() / 2;
    bytes[at] ^= 0x55;
    std::fs::write(path, &bytes).unwrap();
    let (again, stats) = start(prelude, Some(&dir), false, false, None);
    assert_eq!(
        (stats.core_hits, stats.core_misses, stats.core_written),
        (0, 1, 1)
    );
    assert_same(&fresh, &again);
    assert_eq!(
        std::fs::read(path).unwrap(),
        original,
        "rewritten as it was"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// A replay the kernel refuses part way (forced here, after `Bool` is
/// admitted and bound) leaves nothing behind: the session starts again
/// with a fresh elaborator, elaborates the core, counts the refusal, and
/// writes the entry again.
#[test]
fn a_core_replay_refused_part_way_starts_again_from_source() {
    let prelude = stitchwort_elab::prelude();
    let dir = temp_dir("core-refused");
    let (fresh, _) = start(prelude, None, false, false, None);
    start(prelude, Some(&dir), false, false, None);
    let (again, stats) = start(prelude, Some(&dir), false, false, Some("Std.Bool"));
    assert_eq!(stats.refused, 1);
    assert_eq!((stats.core_hits, stats.core_written), (0, 1));
    assert_same(&fresh, &again);
    let (_, stats) = start(prelude, Some(&dir), false, false, None);
    assert_eq!(stats.core_hits, 1);
    let _ = std::fs::remove_dir_all(&dir);
}
