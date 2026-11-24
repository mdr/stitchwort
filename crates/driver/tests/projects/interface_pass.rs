//! The interface pass of `check --jobs`'s stage 3
//! (docs/proposals/parallel-checking-stage-3.md §3, D3735): a namespace
//! checked with the proofs it may defer left out gives the interface digest
//! the full check gives, and an interface entry that another session loads
//! with its unproved theorems still marked, and with no full hash for them.

use std::collections::BTreeMap;
use std::rc::Rc;

use stitchwort_core::hash::def_hash;
use stitchwort_driver::check_cache::MemoryStore;
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::{MemoryFiles, Target, analyse, project_sources};
use stitchwort_elab::cache::{InterfaceEntry, Key, Store};

use crate::check_cache::STACK;

/// `Par.Facts` has one of each kind the deferral rule decides on; `Par.Uses`
/// and `Par.Top` use its theorems, in statements and in proofs.
pub(crate) fn project() -> MemoryFiles {
    let file = |ns: &str, body: &str| (format!("src/Par/{ns}.sw"), body.to_string());
    let files = [
        (
            "stitchwort.yaml".to_string(),
            "sources: [src]\n".to_string(),
        ),
        file(
            "Facts",
            "namespace Par.Facts\n\
             import Std (Nat, Eq, Bool, Iff)\n\n\
             def bump (n: Nat): Nat := match n with\n  \
               | Zero => Zero\n  \
               | Succ k => Succ (bump k)\n\n\
             -- recursive\n\
             theorem bumpId ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ n => Eq.cong Succ (bumpId n)\n\n\
             -- lone\n\
             theorem bumpFn ∀ (n: Nat): bump n = n := bumpId n\n\n\
             theorem bumpTwo: bump 2 = 2 := byComputing\n\n\
             type InRange (lo x hi: Nat): Prop = { low: lo ≤ x, high: x ≤ hi }\n\n\
             def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi\n\n\
             theorem fwd ∀ (lo x hi: Nat) (h: inRange lo x hi): InRange lo x hi :=\n  \
               { low = h.left, high = h.right }\n\n\
             @[reading]\n\
             theorem inRangeReads ∀ (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi :=\n  \
               { forward = fwd lo x hi, backward = r => Both r.low r.high }\n\n\
             -- `unfolding`: elaborated\n\
             opaque def secret (n: Nat): Nat := Succ n\n\n\
             theorem secretSucc ∀ (n: Nat): secret n = Succ n\n  \
               unfolding secret\n\
             := byComputing\n\n\
             -- mutual\n\
             theorem evenBump ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (oddBump k)\n\n\
             theorem oddBump ∀ (n: Nat): bump n = n := match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (evenBump k)\n\n\
             -- a lifted `match` that joins the theorem's group\n\
             theorem bumpBack ∀ (n: Nat): n = bump n := Eq.flipped (match n with\n  \
               | Zero => byComputing\n  \
               | Succ k => Eq.cong Succ (bumpBack k).flipped)\n\n\
             -- `decreasing`\n\
             theorem down ∀ (n: Nat): n = n\n    \
               decreasing n\n\
             :=\n  \
               match n with\n    \
                 | 0 => byComputing\n    \
                 | Succ k => match down k with | _ => byComputing\n\n\
             -- what its proof defines is private to it (D3736)\n\
             theorem addZeroTwice ∀ (n: Nat): n + 0 + 0 = n :=\n  \
               def addZero (m: Nat): Nat := m + 0\n  \
               theorem addZeroIs ∀ (m: Nat): addZero m = m := byComputing\n  \
               let both: addZero (addZero n) = n := byComputing\n  \
               both\n\n\
             -- grouped with a computing definition: elaborated\n\
             def keep (n: Nat) (h: n = n): Nat := n\n\n\
             def pick (n: Nat): Nat := keep n (pickOk n)\n\n\
             theorem pickOk ∀ (n: Nat): n = n := match pick n with | _ => byComputing\n\n\
             -- an instance: elaborated\n\
             interface Weigh (a: Type) = { weight: a → Nat }\n\n\
             instance weighNat: Weigh Nat := { weight = n => n }\n",
        ),
        file(
            "Uses",
            "namespace Par.Uses\n\
             import Std (Nat, Eq)\n\
             import Par.Facts (..)\n\n\
             theorem bumpTwice ∀ (n: Nat): bump (bump n) = n :=\n  \
               Eq.trans (bumpId (bump n)) (bumpId n)\n\n\
             theorem evenTwice ∀ (n: Nat): bump (bump n) = n :=\n  \
               Eq.trans (evenBump (bump n)) (oddBump n)\n\n\
             theorem downThree: 3 = 3 := down 3\n\n\
             def partial: ∀ (n: Nat) => bump n = n := bumpFn\n\n\
             def three: Nat := bump 3 + pick 0\n",
        ),
        file(
            "Top",
            "namespace Par.Top\n\
             import Std (Nat, Eq)\n\
             import Par.Uses (..)\n\
             import Par.Facts (..)\n\n\
             theorem bumpThrice ∀ (n: Nat): bump (bump (bump n)) = n :=\n  \
               Eq.trans (bumpTwice (bump n)) (bumpId n)\n\n\
             def four: Nat := three + 1\n",
        ),
    ];
    MemoryFiles {
        files: files.into_iter().collect(),
        reversed: false,
    }
}

const NAMESPACES: [&str; 3] = ["Par.Facts", "Par.Uses", "Par.Top"];

/// `Par.Facts`'s theorems, each with whether the interface pass leaves its
/// proof out.
const DEFERRED: [(&str, bool); 13] = [
    ("bumpId", true),
    ("bumpFn", true),
    ("bumpTwo", true),
    ("fwd", true),
    ("inRangeReads", true),
    ("evenBump", true),
    ("oddBump", true),
    ("bumpBack", true),
    ("down", true),
    ("addZeroTwice", true),
    ("secretSucc", false),
    ("pickOk", false),
    ("weighNat", false),
];

/// A session over `store`, with each namespace in `namespaces` checked in
/// turn: with `interface` as an interface pass, its entry kept; the digest
/// each ends with, and the entries.
fn check_each(
    store: Rc<dyn Store>,
    without_proofs: bool,
    interface: &[&str],
) -> (Session, BTreeMap<String, Option<Key>>, Vec<InterfaceEntry>) {
    let files = project();
    let mut session = Session::for_stack(STACK);
    session.elab.set_check_cache(store);
    session.elab.set_load_without_proofs(without_proofs);
    let sources = project_sources(&files, "par", &mut session.sources).unwrap();
    let analysis = analyse(&mut session, "par", sources);
    let prepared = session
        .prepare_analysis("par", &analysis, &Target::Everything)
        .unwrap();
    assert_eq!(prepared.order, NAMESPACES);
    let mut digests = BTreeMap::new();
    let mut entries = Vec::new();
    for name in &prepared.order {
        let pass = interface.contains(&name.as_str());
        session
            .elab
            .set_interface_pass(pass.then_some(name.as_str()));
        let ns = analysis.namespace(name).unwrap();
        let (found, _) = session.check_project_namespace(&analysis, ns);
        session.elab.set_interface_pass(None);
        assert!(found.is_empty(), "{name}: {found:?}");
        if pass {
            entries.push(
                (session.elab.take_interface_entry())
                    .unwrap_or_else(|| panic!("{name}: no interface entry")),
            );
        }
        digests.insert(name.clone(), session.elab.namespace_digest(name));
    }
    (session, digests, entries)
}

/// The definition at `path`, which must be there once.
fn def_at(session: &Session, path: &str) -> stitchwort_core::DefId {
    let defs = session.elab.kernel.env.defs();
    let found: Vec<usize> = (0..defs.len())
        .filter(|&i| &**defs[i].path() == path)
        .collect();
    assert_eq!(found.len(), 1, "{path}");
    stitchwort_core::DefId(found[0])
}

/// A store that serves interface entries as `check --jobs` will, beside an
/// inner store that holds no namespace's entry.
struct Interfaces {
    inner: MemoryStore,
    entries: BTreeMap<(String, Key), Vec<u8>>,
}

impl Store for Interfaces {
    fn compiler(&self) -> &str {
        self.inner.compiler()
    }
    fn kernel(&self) -> &str {
        self.inner.kernel()
    }
    fn salt(&self) -> [u8; 16] {
        self.inner.salt()
    }
    fn read(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.inner.read(unit, key)
    }
    fn write(&self, unit: &str, key: &Key, entry: &[u8]) {
        self.inner.write(unit, key, entry)
    }
    fn read_interface(&self, unit: &str, key: &Key) -> Option<Vec<u8>> {
        self.entries.get(&(unit.to_string(), *key)).cloned()
    }
}

/// Every namespace's interface pass gives the full check's digest, with
/// the proofs of recursive, mutual, `decreasing` and lone theorems, and of
/// one whose proof defines its own helpers, left out; a theorem with an
/// `unfolding` list, one grouped with a computing definition and an
/// instance elaborated. The pass writes no entry.
#[test]
fn an_interface_pass_gives_the_full_checks_digest() {
    with_stack(STACK, || {
        let (full, expected, _) = check_each(Rc::new(MemoryStore::default()), false, &[]);
        assert!(!full.elab.holds_unproved_theorems());
        let store = MemoryStore::default();
        let (pass, digests, entries) = check_each(Rc::new(store.clone()), true, &NAMESPACES);
        for ns in NAMESPACES {
            assert!(expected[ns].is_some(), "{ns}: the full check has no digest");
            assert_eq!(digests[ns], expected[ns], "{ns}: another digest");
        }
        for e in &entries {
            assert_eq!(Some(e.digest), expected[&e.unit[3..]], "{}", e.unit);
        }
        let stats = pass.elab.check_cache_stats();
        assert_eq!((stats.interface_passes, stats.interface_made), (3, 3));
        assert_eq!(stats.namespace_written, 0, "{stats:?}");
        assert!(pass.elab.holds_unproved_theorems());
        for (name, deferred) in DEFERRED {
            let path = format!("Par.Facts.{name}");
            let def = pass.elab.kernel.def(def_at(&pass, &path));
            assert_eq!(def.unproved(), deferred, "{path}");
            assert_eq!(def.body().is_none(), deferred, "{path}");
        }
        // Never made: what deferred proofs would have declared.
        let defs = pass.elab.kernel.env.defs();
        for helper in ["Par.Facts.down.%step", "Par.Facts.addZeroTwice.addZero"] {
            assert!(!defs.iter().any(|d| &**d.path() == helper), "{helper}");
        }
        let deferred = DEFERRED.iter().filter(|(_, d)| *d).count();
        assert_eq!(entries[0].deferred, deferred);
        // `bumpTwice`, `evenTwice`, `downThree`; `bumpThrice`.
        assert_eq!(stats.deferred, deferred + 3 + 1, "{stats:?}");
        std::mem::forget(full);
        std::mem::forget(pass);
    });
}

/// A session that loads `Par.Facts` and `Par.Uses` from their interface
/// entries holds their deferred theorems as unproved, with no full hash
/// (asking is the internal error, not `None`), and checks `Par.Top`
/// against them to the full check's digest.
#[test]
fn an_admitted_interface_entry_keeps_the_mark_and_has_no_full_hash() {
    with_stack(STACK, || {
        let (full, expected, _) = check_each(Rc::new(MemoryStore::default()), false, &[]);
        std::mem::forget(full);
        let inner = MemoryStore::default();
        let (pass, _, made) = check_each(Rc::new(inner.clone()), true, &NAMESPACES);
        std::mem::forget(pass);
        let served = Interfaces {
            inner,
            entries: (made.into_iter())
                .filter(|e| e.unit != "ns.Par.Top")
                .map(|e| ((e.unit, e.key), e.bytes))
                .collect(),
        };
        let (loaded, digests, _) = check_each(Rc::new(served), true, &[]);
        let stats = loaded.elab.check_cache_stats();
        assert_eq!(stats.interface_hits, 2, "{stats:?}");
        assert_eq!(
            (stats.namespace_hits, stats.refused, stats.late_misses),
            (0, 0, 0),
            "{stats:?}"
        );
        assert_eq!(stats.unproved, 10 + 3, "{stats:?}");
        assert_eq!(stats.namespace_written, 1, "Par.Top, checked against them");
        assert_eq!(digests, expected);
        assert!(loaded.elab.holds_unproved_theorems());
        let id = def_at(&loaded, "Par.Facts.bumpId");
        assert!(loaded.elab.kernel.def(id).unproved());
        assert!(
            !(loaded
                .elab
                .kernel
                .def(def_at(&loaded, "Par.Facts.pickOk"))
                .unproved())
        );
        let asked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = def_hash(&loaded.elab.kernel.ev(), id);
        }));
        let message = asked.expect_err("a full hash of an unproved theorem");
        let message = (message.downcast_ref::<String>().cloned())
            .or_else(|| message.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            message.contains("hasn't been checked"),
            "another panic: {message}"
        );
        std::mem::forget(loaded);
    });
}

/// A session that reports and holds a theorem whose proof hasn't been
/// checked stops with the internal error, whatever it loaded: here a check
/// whose first namespace was made an interface pass, as only `check
/// --jobs`'s workers do (`project::assert_holds_no_unproved_theorem`, in
/// `check_prepared`).
#[test]
fn a_session_that_reports_never_holds_an_unproved_theorem() {
    with_stack(STACK, || {
        let files = project();
        let mut session = Session::for_stack(STACK);
        session
            .elab
            .set_check_cache(Rc::new(MemoryStore::default()));
        session.elab.set_load_without_proofs(true);
        session.elab.set_interface_pass(Some("Par.Facts"));
        let reported = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = session.load_project_for(
                &files,
                "par",
                &Target::Everything,
                stitchwort_driver::project::Load::Diagnostics,
            );
        }));
        let message = reported.expect_err("a reporting session held an unproved theorem");
        let message = (message.downcast_ref::<String>().cloned())
            .or_else(|| message.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            message
                .contains("a session that reports holds a theorem whose proof hasn't been checked"),
            "another panic: {message}"
        );
        std::mem::forget(session);
    });
}
