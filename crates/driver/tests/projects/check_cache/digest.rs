//! Keys by interface digest (docs/proposals/interface-digest-cache.md,
//! stages A and C): a namespace's key covers each dependency's digest,
//! which leaves out the proofs of its sealed theorems, source positions,
//! the lifted `match`es only those proofs reach, and where its plain
//! theorems sit in checking order. So an edit below that changes only
//! those replays the namespaces above it, and any other edit checks them
//! again. Each run here is compared with a check
//! without the cache ([`fresh_and_cached`]), so a hit that shouldn't be one
//! shows up as a different result too.

use std::path::Path;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_elab::cache::Stats;

use super::{
    STACK, Source, entries, entry_of, first_difference, fresh_and_cached, run, temp_dir,
    temp_project, write_file,
};

/// `A` has a definition, a theorem about it and a `def` whose type is a
/// proposition; `B` uses all three.
const BASE: &[(&str, &str)] = &[
    ("src/A.sw", A),
    (
        "src/B.sw",
        "namespace B\n\nimport A (one, oneIsOne, oneProof)\n\n\
         theorem stillOne: one = 1 := oneIsOne\n\n\
         theorem alsoOne: one = 1 := oneProof\n\n\
         def two: Nat := one + one\n",
    ),
];

const A: &str = "namespace A\n\ndef one: Nat := 1\n\n\
                 theorem oneIsOne: one = 1 := byComputing\n\n\
                 def oneProof: one = 1 := byComputing\n";

/// Checks the project `files` cold and warm, then with `edits` made: the
/// cache's statistics for that last check, which agreed with one without
/// the cache.
fn after_edit(name: &str, files: &[(&str, &str)], edits: &[(&str, &str)]) -> Stats {
    after_edit_holding(name, files, edits, &[])
}

/// [`after_edit`], asserting that the entries hold each of `helpers` after
/// the edit (a `match` on a variable compiles in place, with no helper to
/// leave out) and that `check --recheck` then computes every digest as
/// written.
fn after_edit_holding(
    name: &str,
    files: &[(&str, &str)],
    edits: &[(&str, &str)],
    helpers: &[&str],
) -> Stats {
    let dir = temp_project(name, files);
    let cache = temp_dir(&format!("{name}-cache"));
    let cold = fresh_and_cached(&dir, &cache);
    assert_eq!(cold.namespace_written, files.len(), "{cold:?}");
    let warm = fresh_and_cached(&dir, &cache);
    assert_eq!(
        (warm.namespace_hits, warm.namespace_misses),
        (files.len(), 0)
    );
    for (path, text) in edits {
        write_file(&dir, path, text);
    }
    let edited = fresh_and_cached_after_edit(name, &dir, &cache);
    assert_entries_match_fresh(name, &dir, &cache);
    if !helpers.is_empty() {
        let held: Vec<Vec<u8>> = (entries(&cache).iter())
            .map(|p| std::fs::read(p).unwrap())
            .collect();
        for helper in helpers {
            let found =
                (held.iter()).any(|b| b.windows(helper.len()).any(|w| w == helper.as_bytes()));
            assert!(found, "no entry holds `{helper}`");
        }
        let rechecked = with_loaded(&dir, &cache, true, |s, ok| {
            assert!(ok, "the re-check passes");
            s.elab.check_cache_stats()
        });
        assert_eq!(
            (rechecked.namespace_rechecked, rechecked.digest_mismatches),
            (files.len(), 0),
            "{rechecked:?}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
    edited
}

/// [`fresh_and_cached`] for the edited project `name`, asserting that it
/// checks with no errors. A proof that fails to check writes no entry, so
/// both runs would show its namespace as missing; without this an edit that
/// broke the proof could pass as a cache digest change.
fn fresh_and_cached_after_edit(name: &str, dir: &Path, cache: &Path) -> Stats {
    let source = Source::Project("p".to_string(), dir.to_path_buf());
    let fresh = run(&source, true, None);
    let cached = run(&source, true, Some(cache));
    assert!(
        cached.dump == fresh.dump,
        "the cache changed the result: {}",
        first_difference(&fresh.dump, &cached.dump)
    );
    assert!(
        fresh.dump.contains("\naccepted true\n"),
        "{name}: the edited project does not check: {}",
        first_error(&fresh.dump)
    );
    cached.stats
}

/// The first error in a dump that ended with `accepted false`: the heading
/// of the first diagnostic, which names its code and message.
fn first_error(dump: &str) -> &str {
    let after = dump
        .split_once("\naccepted false\n")
        .map_or("", |(_, after)| after);
    after
        .lines()
        .find(|line| line.contains("Error:"))
        .or_else(|| after.lines().find(|line| !line.trim().is_empty()))
        .unwrap_or("(no diagnostic)")
}

/// Elaborates the project at `dir` from nothing into a new cache (given the
/// machine salt of `cache`, so the bytes are comparable) and asserts that
/// every entry it wrote is, byte for byte, the entry of the same name in
/// `cache`, outside the salt and the checksum: what `cache` replayed holds
/// what a fresh elaboration against the edited dependencies produces
/// (docs/proposals/check-cache.md, "An entry's layout").
fn assert_entries_match_fresh(name: &str, dir: &Path, cache: &Path) {
    // Magic (8), format (4) and key (32) come first; then the salt (16);
    // the checksum is the last 32 bytes.
    const SALT: std::ops::Range<usize> = 44..60;
    const CHECKSUM: usize = 32;
    let fresh = temp_dir(&format!("{name}-fresh-cache"));
    std::fs::create_dir_all(fresh.join("check")).unwrap();
    std::fs::copy(cache.join("check/header"), fresh.join("check/header")).unwrap();
    let source = Source::Project("p".to_string(), dir.to_path_buf());
    run(&source, true, Some(&fresh));
    // A project that fails to check writes nothing, and has nothing to compare.
    for path in entries(&fresh) {
        let file = path.file_name().unwrap().to_str().unwrap().to_string();
        let kept = std::fs::read(cache.join("check").join(&file))
            .unwrap_or_else(|_| panic!("the edited cache has no entry {file}"));
        let new = std::fs::read(&path).unwrap();
        assert_eq!(kept.len(), new.len(), "entry {file} differs in length");
        let differing: Vec<usize> = (0..kept.len() - CHECKSUM)
            .filter(|i| !SALT.contains(i) && kept[*i] != new[*i])
            .collect();
        assert!(
            differing.is_empty(),
            "entry {file} differs outside the salt and checksum, first at byte {:?} of {}",
            differing.first(),
            kept.len()
        );
    }
    let _ = std::fs::remove_dir_all(&fresh);
}

/// `A` edited to `text`, in [`BASE`]: whether `B` was replayed.
fn b_replayed_after(name: &str, text: &str) -> bool {
    let s = after_edit(name, BASE, &[("src/A.sw", text)]);
    assert_eq!(s.namespace_hits + s.namespace_misses, 2, "{s:?}");
    assert_eq!((s.refused, s.late_misses), (0, 0), "{s:?}");
    s.namespace_hits == 1
}

#[test]
fn an_edited_proof_below_replays_what_uses_it() {
    let edited = A.replace(
        "theorem oneIsOne: one = 1 := byComputing",
        "theorem oneIsOne: one = 1 := oneProof",
    );
    assert!(b_replayed_after("digest-proof", &edited));
}

#[test]
fn an_edit_that_moves_everything_below_replays_what_uses_it() {
    // Every position in `A` after the first line moves.
    let edited = A.replace("namespace A\n", "namespace A\n\n-- a comment\n\n");
    assert!(b_replayed_after("digest-moved", &edited));
}

#[test]
fn an_edited_statement_below_checks_what_uses_it_again() {
    let edited = A.replace(
        "theorem oneIsOne: one = 1 := byComputing",
        "theorem oneIsOne: one = 0 + 1 := byComputing",
    );
    assert!(!b_replayed_after("digest-statement", &edited));
}

#[test]
fn an_edited_computing_definition_below_checks_what_uses_it_again() {
    let edited = A.replace("def one: Nat := 1", "def one: Nat := 0 + 1");
    assert!(!b_replayed_after("digest-definition", &edited));
}

/// A `def` whose type is a proposition keeps its body in the digest, as in
/// the hashes: it isn't a theorem, so it isn't sealed.
#[test]
fn an_edited_proposition_definition_below_checks_what_uses_it_again() {
    let edited = A.replace(
        "def oneProof: one = 1 := byComputing",
        "def oneProof: one = 1 := oneIsOne",
    );
    assert!(!b_replayed_after("digest-prop-def", &edited));
}

#[test]
fn an_added_name_below_checks_what_uses_it_again() {
    let edited = format!("{A}\ndef three: Nat := 3\n");
    assert!(!b_replayed_after("digest-name", &edited));
}

#[test]
fn an_added_instance_below_checks_what_uses_it_again() {
    let a = A.replace("namespace A\n", "namespace A\n\nimport Std (Show)\n");
    let base = format!("{a}\ntype Coin = | Heads | Tails\n");
    let edited =
        format!("{base}\ninstance Coin.instShow: Show Coin := Show.fromText (c => \"coin\")\n");
    let s = after_edit(
        "digest-instance",
        &[("src/A.sw", &base), BASE[1]],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

#[test]
fn an_added_reading_below_checks_what_uses_it_again() {
    let base = "namespace A\n\ntype Small (n: Nat): Prop = { below: n < 10 }\n\n\
                def small (n: Nat): Bool := n < 10\n\n\
                theorem smallReads (n: Nat): small n ↔ Small n := \
                { forward = h => { below = h }, backward = s => s.below }\n";
    let edited = base.replace("theorem smallReads", "@[reading]\ntheorem smallReads");
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (small)\n\ndef two: Nat := 2\n",
    );
    let s = after_edit(
        "digest-reading",
        &[("src/A.sw", base), b],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

/// The audit's p1 shape (docs/reviews/SW-4732-body-read-audit.md): a proof
/// edited from a `match` to a call, arity 1 to 0, used by application, by
/// partial application and by `rewrite`.
#[test]
fn a_proof_changed_from_a_match_to_a_call_replays_what_uses_it_unchanged() {
    let head = "namespace A\n\nimport Std (Eq, Nat)\n\n\
                def bump (n: Nat): Nat := match n with\n  | Zero => Zero\n  | Succ k => Succ (bump k)\n\n";
    let before = format!(
        "{head}theorem bumpId ∀ (n: Nat): bump n = n := match n with\n  | Zero => byComputing\n  \
         | Succ n => Eq.cong Succ (bumpId n)\n\n\
         theorem bumpAux ∀ (n: Nat): bump n = n := bumpId n\n\n\
         theorem bumpFn: ∀ (n: Nat) => bump n = n := n => bumpId n\n"
    );
    let after = format!(
        "{head}theorem bumpAux ∀ (n: Nat): bump n = n := match n with\n  | Zero => byComputing\n  \
         | Succ n => Eq.cong Succ (bumpAux n)\n\n\
         theorem bumpId ∀ (n: Nat): bump n = n := bumpAux n\n\n\
         theorem bumpFn: ∀ (n: Nat) => bump n = n := bumpAux\n"
    );
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (bump, bumpId, bumpFn)\n\n\
         theorem applied (n: Nat): bump n = n := bumpId n\n\n\
         def partial: ∀ (n: Nat) => bump n = n := bumpId\n\n\
         theorem rewritten (n: Nat): bump (bump n) = n :=\n  rewrite bumpId n then bumpId n\n\n\
         theorem viaFn (n: Nat): bump n = n := bumpFn n\n",
    );
    let s = after_edit(
        "digest-p1",
        &[("src/A.sw", &before), b],
        &[("src/A.sw", &after)],
    );
    // `B` was replayed, so it was written and compared above.
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

/// The smallest walk family (`examples/accept/walk-minimal-family.sw`).
const WALK: &str = "namespace A\n\nimport Std (Parse, Nat, Option)\n\n\
    def Mine (p: () → {Parse Nat} a) (post: a → Prop): Prop := (p, post) = (p, post)\n\n\
    @[walk.done]\ntheorem mineDone ∀ [x: a] [holds: a → Prop]: Mine (() => x) holds := byComputing\n\n\
    @[walk.weaken]\ntheorem mineWeaken ∀ [p: () → {Parse Nat} a] [holds weaker: a → Prop] \
    (m: Mine p holds): Mine p weaker := byComputing\n\n\
    @[walk.bind]\ntheorem mineThen ∀ [p: () → {Parse Nat} a] [j: a → {Parse Nat} Nat] \
    [first: a → Prop] [holds: Nat → Prop]\n    (firstMine: Mine p first)\n    \
    (rest: ∀ (v: a) => first v → Mine (() => j v) holds):\n    Mine (() => j (p())) holds :=\n  \
    byComputing\n\n\
    def look(): {Parse Nat} Option Nat := Parse.next (n => True)\n\n\
    @[walk]\ntheorem mineLook: Mine (() => look()) ((v: Option Nat) => True) := byComputing\n";

#[test]
fn a_walk_tag_removed_below_checks_what_uses_it_again() {
    let edited = WALK.replace("@[walk]\ntheorem mineLook", "theorem mineLook");
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (look)\n\ndef two: Nat := 2\n",
    );
    let s = after_edit(
        "digest-walk",
        &[("src/A.sw", WALK), b],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

#[test]
fn an_edited_rule_set_below_checks_what_uses_it_again() {
    let base =
        format!("{A}\ntheorem oneAgain: one = 1 := byComputing\n\nrules ones := [oneIsOne]\n");
    let edited = base.replace("[oneIsOne]", "[oneIsOne, oneAgain]");
    let s = after_edit(
        "digest-rules",
        &[("src/A.sw", &base), BASE[1]],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

#[test]
fn an_edited_ability_below_checks_what_uses_it_again() {
    let base = format!("{A}\nability Say where\n  say: Nat → {{Say}} ()\n");
    let edited = format!("{base}  hush: () → {{Say}} ()\n");
    let s = after_edit(
        "digest-ability",
        &[("src/A.sw", &base), BASE[1]],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

#[test]
fn an_edited_field_default_below_checks_what_uses_it_again() {
    let base = format!("{A}\ntype Style = {{ width: Nat := 80 }}\n");
    let edited = base.replace(":= 80", ":= 81");
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (Style)\n\ndef plain: Style := {}\n",
    );
    let s = after_edit(
        "digest-default",
        &[("src/A.sw", &base), b],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

/// A proof that starts using a library file the namespace didn't load
/// widens what the namespaces after it reach (their instances and `auto`
/// candidates), so it is in the digest.
#[test]
fn a_proof_below_that_loads_a_new_library_file_checks_what_uses_it_again() {
    let base = "namespace A\n\ntheorem keeps: (True ∨ False) = True := byComputing\n";
    let edited = base.replace(":= byComputing", ":= Std.Bool.orFalse True");
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (keeps)\n\ndef two: Nat := 2\n",
    );
    let s = after_edit(
        "digest-reach",
        &[("src/A.sw", base), b],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

/// A namespace that uses a record of `A` with navigation recorded: an edit
/// in `A` that only moves positions replays it, and what the replay gives
/// (navigation's targets in `A` among it) is what checking gives, since
/// navigation keeps such targets by name. A warning that labels a position
/// in `A` is rule 4's case:
/// `a_warning_pointing_into_the_edited_file_checks_what_holds_it_again`.
#[test]
fn a_moved_record_below_replays_what_navigates_to_it() {
    let a = "namespace A\n\ntype Box = { width: Nat }\n";
    let b = "namespace B\n\nimport A (Box)\n\n\
             def box: Box := { width = 3 }\n\ndef w: Nat := box.width\n";
    let moved = a.replace("namespace A\n", "namespace A\n\n-- a comment\n");
    let s = after_edit(
        "digest-position",
        &[("src/A.sw", a), ("src/B.sw", b)],
        &[("src/A.sw", &moved)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

// ---- Stage C: helpers only a proof reaches, and plain theorems' order ----

/// `A` below with `proof` as `oneIsOne`'s proof, checked and then edited to
/// `edited`, with the helpers the edited entry must hold: whether `B` was
/// replayed.
fn b_replayed_after_proof(name: &str, proof: &str, edited: &str, helpers: &[&str]) -> bool {
    let a = |p: &str| {
        A.replace(
            "theorem oneIsOne: one = 1 := byComputing",
            &format!("theorem oneIsOne: one = 1 := {p}"),
        )
    };
    let s = after_edit_holding(
        name,
        &[("src/A.sw", &a(proof)), BASE[1]],
        &[("src/A.sw", &a(edited))],
        helpers,
    );
    assert_eq!(s.namespace_hits + s.namespace_misses, 2, "{s:?}");
    assert_eq!((s.refused, s.late_misses), (0, 0), "{s:?}");
    s.namespace_hits == 1
}

#[test]
fn a_match_added_to_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-match-added",
        "byComputing",
        "match one + 0 with | _ => byComputing",
        &["A.oneIsOne.%match1"],
    ));
}

#[test]
fn a_match_removed_from_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-match-removed",
        "match one + 0 with | _ => byComputing",
        "byComputing",
        &[],
    ));
}

#[test]
fn a_match_whose_arms_change_in_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-match-arms",
        "match one + 0 with | _ => byComputing",
        "match one + 0 with | 0 => byComputing | _ => byComputing",
        &["A.oneIsOne.%match1"],
    ));
}

/// A local definition in a theorem's proof is private to the proof
/// (D3736), so the digest leaves it out as it does a lifted `match`.
#[test]
fn a_local_definition_added_to_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-proof-local-added",
        "byComputing",
        "\n  def helper (m: Nat): Nat := m + 0\n  let same: helper one = 1 := byComputing\n  same",
        &["A.oneIsOne.helper"],
    ));
}

#[test]
fn a_local_definition_with_a_match_added_to_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-proof-local-match",
        "byComputing",
        "\n  def go (m: Nat): Nat := match m + 0 with | _ => m\n  byComputing",
        &["A.oneIsOne.go.%match1"],
    ));
}

#[test]
fn a_local_definition_changed_in_a_proof_below_replays_what_uses_it() {
    assert!(b_replayed_after_proof(
        "digest-proof-local-changed",
        "\n  def helper (m: Nat): Nat := m + 0\n  let same: helper one = 1 := byComputing\n  same",
        "\n  def helper (m: Nat): Nat := 0 + m\n  let same: helper one = 1 := byComputing\n  same",
        &["A.oneIsOne.helper"],
    ));
}

/// A `match` added before another renumbers it: `%match1` is now the new
/// one. Both are private, so the names don't matter.
#[test]
fn a_match_added_before_another_in_a_proof_below_replays_what_uses_it() {
    let a = |first: &str| {
        format!(
            "{A}\ntheorem both: one = 1 ∧ one = 1 := \
             ({first}, match one + 0 with | _ => byComputing)\n"
        )
    };
    let s = after_edit_holding(
        "digest-match-renumbered",
        &[("src/A.sw", &a("byComputing")), BASE[1]],
        &[("src/A.sw", &a("match one + 1 with | _ => byComputing"))],
        &["A.both.%match1", "A.both.%match2"],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

/// A recursive theorem's lifted `match` that calls it joins its group; the
/// theorem's group isn't in the digest, so the helper is still private.
#[test]
fn a_match_added_to_a_recursive_theorem_below_replays_what_uses_it() {
    let a = |step: &str| {
        format!(
            "{A}\ntheorem rec (n: Nat): n + 0 = n :=\n  match n with\n    \
             | 0 => byComputing\n    | Succ k => {step}\n"
        )
    };
    let s = after_edit_holding(
        "digest-match-recursive",
        &[("src/A.sw", &a("byComputing")), BASE[1]],
        &[(
            "src/A.sw",
            &a("match k + 0 with | _ => (match rec k with | _ => byComputing)"),
        )],
        &["A.rec.%match1", "A.rec.%match2"],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

/// A `decreasing` theorem makes `down.%step` and `down.%go` from its
/// signature, measure and proof; they are proof-private, so neither an edit
/// of the proof nor of the measure moves the digest. The entry still holds
/// them (replay declares them again).
#[test]
fn an_edited_decreasing_theorem_below_replays_what_uses_it() {
    let a = |measure: &str, step: &str| {
        format!(
            "{A}\ntheorem down ∀ (n: Nat): n = n\n    decreasing {measure}\n:=\n  \
             match n with\n    | 0 => byComputing\n    | Succ k => {step}\n"
        )
    };
    let b = "namespace B\n\nimport A (down)\n\ntheorem usesDown: 3 = 3 := down 3\n";
    let before = a("n", "match down k with | _ => byComputing");
    for (name, edited) in [
        (
            "digest-decreasing-proof",
            a(
                "n",
                "match down k with | _ => (match k with | _ => byComputing)",
            ),
        ),
        (
            "digest-decreasing-measure",
            a("n + 0", "match down k with | _ => byComputing"),
        ),
    ] {
        let s = after_edit_holding(
            name,
            &[("src/A.sw", &before), ("src/B.sw", b)],
            &[("src/A.sw", &edited)],
            &["A.down.%step", "A.down.%go"],
        );
        assert_eq!(
            (s.namespace_hits, s.namespace_misses),
            (1, 1),
            "{name}: {s:?}"
        );
    }
}

/// A `decreasing` theorem is sealed outside a program, so it isn't marked
/// folded: the mark is part of the interface digest, and a check that skips
/// the proof would otherwise write a different digest from one that runs it.
/// A `decreasing` definition keeps its mark.
#[test]
fn a_decreasing_theorem_is_not_marked_folded() {
    let a = format!(
        "{A}\ntheorem down ∀ (n: Nat): n = n\n    decreasing n\n:=\n  \
         match n with\n    | 0 => byComputing\n    | Succ k => match down k with | _ => byComputing\n\n\
         def count (n: Nat): Nat\n    decreasing n\n:=\n  \
         match n with\n    | 0 => 0\n    | Succ k => count k\n"
    );
    let dir = temp_project("digest-decreasing-fold", &[("src/A.sw", &a)]);
    let cache = temp_dir("digest-decreasing-fold-cache");
    let (theorem, def) = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok, "the project checks");
        let g = s.elab.ev();
        let fold = |name: &str| g.def(s.elab.lookup_def(name).expect(name)).fold();
        (fold("A.down"), fold("A.count"))
    });
    assert!(!theorem, "the theorem is marked folded");
    assert!(def, "the definition is not marked folded");
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// A theorem proved by `byWalking` over a recursive function is recursive
/// though its source shows no call of itself: the walk's proof of the
/// recursive call is the theorem (SW-4758). Its proof is sealed like any
/// other, so an edit of it, with or without a `match` before the walk,
/// replays what uses it. (Which theorems the entry's part B holds does
/// change: with the walk at the top, its lifted `match` keeps the group in
/// part A.)
#[test]
fn an_edited_walked_recursive_theorem_below_replays_what_uses_it() {
    let a = |proof: &str| {
        format!(
            "namespace A\n\nimport Std (Parse, Nat, Option)\n\n\
             def look(): {{Parse Nat}} Option Nat := Parse.next (n => True)\n\n\
             @[walk]\ntheorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) \
             ((v: Option Nat) => True) :=\n  \
             Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)\n\n\
             def down (fuel: Nat): {{Parse Nat}} Nat := match fuel with\n  | Zero => 0\n  \
             | Succ more =>\n    let x := look()\n    down more\n\n\
             theorem givesDown ∀ (fuel: Nat): \
             Parse.Gives Parse.Invariant.any (() => down fuel) (n => True) :=\n  {proof}\n"
        )
    };
    let b = (
        "src/B.sw",
        "namespace B\n\nimport Std (Parse, Nat)\nimport A (down, givesDown)\n\n\
         theorem downThree: Parse.Gives Parse.Invariant.any (() => down 3) (n => True) := \
         givesDown 3\n",
    );
    let walked = "byWalking []";
    let matched = "match fuel with\n    | Zero => byWalking []\n    | Succ more => byWalking []";
    for (name, before, edited) in [
        ("digest-walked-match-added", walked, matched),
        ("digest-walked-match-removed", matched, walked),
        (
            "digest-walked-match-arm",
            matched,
            "match fuel with\n    | Zero => byWalking []\n    | Succ more => byWalking [givesLook]",
        ),
        (
            "digest-walked-match-lifted",
            matched,
            "match fuel with\n    | Zero => (match 0 + 0 with | _ => byWalking [])\n    \
             | Succ more => byWalking []",
        ),
    ] {
        let s = after_edit(
            name,
            &[("src/A.sw", &a(before)), b],
            &[("src/A.sw", &a(edited))],
        );
        // A proof that fails writes nothing, and `B` would miss for that.
        assert_eq!(
            (s.namespace_hits, s.namespace_misses, s.namespace_written),
            (1, 1, 1),
            "{name}: {s:?}"
        );
    }
}

/// A helper added before a data type's declaration: the type's count of
/// definitions before it counts only those the digest keeps in order.
#[test]
fn a_match_added_to_a_proof_before_a_data_type_replays_what_uses_it() {
    let a = |proof: &str| {
        format!(
            "namespace A\n\ndef one: Nat := 1\n\n\
             theorem oneIsOne: one = 1 := {proof}\n\n\
             type Coin = | Heads | Tails\n\ndef coin: Coin := Heads\n"
        )
    };
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (Coin, coin)\n\ndef same: Coin := coin\n",
    );
    let s = after_edit_holding(
        "digest-match-data",
        &[("src/A.sw", &a("byComputing")), b],
        &[("src/A.sw", &a("match one + 0 with | _ => byComputing"))],
        &["A.oneIsOne.%match1"],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

/// A `match` the digest keeps: in a statement, a computing body or a `def`
/// of proposition type. Each checks `B` again.
#[test]
fn a_match_outside_a_sealed_proof_below_checks_what_uses_it_again() {
    let cases = [
        (
            "theorem oneIsOne: one = 1 := byComputing",
            "theorem oneIsOne: (match one + 0 with | 0 => one = 1 | _ => one = 1) := byComputing",
            "A.oneIsOne.%match1",
        ),
        (
            "def one: Nat := 1",
            "def one: Nat := match 0 + 0 with | _ => 1",
            "A.one.%match1",
        ),
        (
            "def oneProof: one = 1 := byComputing",
            "def oneProof: one = 1 := match one + 0 with | _ => byComputing",
            "A.oneProof.%match1",
        ),
    ];
    for (i, (from, to, helper)) in cases.into_iter().enumerate() {
        assert!(A.contains(from), "{from}");
        let s = after_edit_holding(
            &format!("digest-match-kept-{i}"),
            BASE,
            &[("src/A.sw", &A.replace(from, to))],
            &[helper],
        );
        assert_eq!(
            (s.namespace_hits, s.namespace_misses),
            (0, 2),
            "`{to}`: {s:?}"
        );
    }
}

/// A theorem with an `unfolding` list stores the helpers of its proof's
/// `match`es in that list (`Elaborator::in_body_of`), and the list is in
/// the digest: such a helper is kept, so `B` is checked again (today's
/// behaviour, interface-digest-cache.md C.1's table).
#[test]
fn a_match_added_to_a_proof_with_an_unfolding_list_checks_what_uses_it_again() {
    let a = |proof: &str| {
        format!(
            "namespace A\n\nopaque def f (n: Nat): Nat := n + 1\n\n\
             theorem fOne: f 0 = 1 unfolding f := {proof}\n"
        )
    };
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (f, fOne)\n\ntheorem still: f 0 = 1 := fOne\n",
    );
    let s = after_edit_holding(
        "digest-match-unfolding",
        &[("src/A.sw", &a("byComputing")), b],
        &[("src/A.sw", &a("match f 0 + 0 with | _ => byComputing"))],
        &["A.fOne.%match1"],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

/// A proof that starts using a theorem declared after it changes the order
/// the namespace is checked in; plain theorems are in the digest by path,
/// so `B` is replayed (SW-4710).
#[test]
fn a_proof_below_that_starts_using_a_later_theorem_replays_what_uses_it() {
    let a = format!("{A}\ntheorem later: one = 1 := byComputing\n");
    let edited = a.replace(
        "theorem oneIsOne: one = 1 := byComputing",
        "theorem oneIsOne: one = 1 := later",
    );
    let s = after_edit(
        "digest-later-theorem",
        &[("src/A.sw", &a), BASE[1]],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (1, 1), "{s:?}");
}

/// A proof that starts using a computing definition declared after it
/// moves that definition past another in checking order: the digest
/// changes (only plain theorems are listed by path), and what the cache
/// gives is what a check without it gives.
#[test]
fn a_proof_below_that_starts_using_a_later_definition_gives_what_a_fresh_check_gives() {
    let a = format!(
        "{A}\ndef first: Nat := 2\n\ndef second: Nat := 3\n\n\
         theorem secondIs: second = 3 := byComputing\n"
    );
    let edited = a.replace(
        "theorem oneIsOne: one = 1 := byComputing",
        "theorem oneIsOne: one = 1 := match second with | _ => byComputing",
    );
    let s = after_edit(
        "digest-later-definition",
        &[("src/A.sw", &a), BASE[1]],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.refused, s.late_misses), (0, 0), "{s:?}");
}

/// An `@[reading]` theorem keys a row, so it stays in checking order; its
/// proof starting to use a later theorem gives what a fresh check gives.
#[test]
fn a_reading_whose_proof_starts_using_a_later_theorem_gives_what_a_fresh_check_gives() {
    let a = "namespace A\n\ntype Small (n: Nat): Prop = { below: n < 10 }\n\n\
             def small (n: Nat): Bool := n < 10\n\n\
             @[reading]\ntheorem smallReads (n: Nat): small n ↔ Small n := \
             { forward = h => { below = h }, backward = s => s.below }\n\n\
             theorem later (n: Nat): small n ↔ Small n := \
             { forward = h => { below = h }, backward = s => s.below }\n";
    let edited = a.replace(
        "@[reading]\ntheorem smallReads (n: Nat): small n ↔ Small n := \
         { forward = h => { below = h }, backward = s => s.below }",
        "@[reading]\ntheorem smallReads (n: Nat): small n ↔ Small n := later n",
    );
    assert_ne!(a, edited);
    let b = (
        "src/B.sw",
        "namespace B\n\nimport A (small)\n\n\
         theorem below (n: Nat) (h: small n): n < 10 :=\n  match h with\n    | { below } => below\n",
    );
    let s = after_edit(
        "digest-later-reading",
        &[("src/A.sw", a), b],
        &[("src/A.sw", &edited)],
    );
    assert_eq!((s.refused, s.late_misses), (0, 0), "{s:?}");
}

/// `B` has a private helper of its own; `A`'s proof gains one. `B` and `C`
/// above it are replayed.
#[test]
fn private_helpers_in_two_namespaces_replay_what_is_above_both() {
    let a = |proof: &str| {
        A.replace(
            "theorem oneIsOne: one = 1 := byComputing",
            &format!("theorem oneIsOne: one = 1 := {proof}"),
        )
    };
    let b = "namespace B\n\nimport A (one, oneIsOne)\n\n\
             theorem stillOne: one = 1 := match one + 0 with | _ => oneIsOne\n\n\
             def two: Nat := one + one\n";
    let c = "namespace C\n\nimport B (two)\n\ntheorem twoIsTwo: two = 2 := byComputing\n";
    let s = after_edit_holding(
        "digest-match-two",
        &[
            ("src/A.sw", &a("byComputing")),
            ("src/B.sw", b),
            ("src/C.sw", c),
        ],
        &[("src/A.sw", &a("match one + 0 with | _ => byComputing"))],
        &["A.oneIsOne.%match1", "B.stillOne.%match1"],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (2, 1), "{s:?}");
}

/// session, with whether the load succeeded, to `then`.
fn with_loaded<R: Send>(
    dir: &Path,
    cache: &Path,
    recheck: bool,
    then: impl FnOnce(&mut Session, bool) -> R + Send,
) -> R {
    with_stack(STACK, || {
        let mut session = Session::navigable_for_stack(STACK);
        session.use_check_cache(cache);
        session.elab.set_recheck(recheck);
        let ok = session
            .load_project(
                &DiskFiles {
                    root: dir.to_path_buf(),
                },
                "p",
                &Target::Everything,
            )
            .is_ok();
        then(&mut session, ok)
    })
}

/// The open goals `B.stillOne` relies on, by path.
fn goals_of_still_one(session: &Session) -> Vec<String> {
    let id = session.elab.lookup_def("B.stillOne").expect("B.stillOne");
    let g = session.elab.ev();
    (session.elab.goals_relied_on(id).into_iter())
        .map(|goal| g.def(goal).path().to_string())
        .collect()
}

/// A `?` in a proof below gives its namespace no digest (it isn't written),
/// so what uses it is checked again, keyed to its text, and relies on the
/// goal; filling the goal again replays it from its first entry, and the
/// reliance is gone, found by the walk over the live proofs.
#[test]
fn a_goal_in_a_proof_below_checks_what_uses_it_and_is_relied_on() {
    let dir = temp_project("digest-goal", BASE);
    let cache = temp_dir("digest-goal-cache");
    let cold = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        s.elab.check_cache_stats()
    });
    assert_eq!(cold.namespace_written, 2, "{cold:?}");
    write_file(
        &dir,
        "src/A.sw",
        &A.replace(
            "theorem oneIsOne: one = 1 := byComputing",
            "theorem oneIsOne: one = 1 := ?",
        ),
    );
    let (open, goals) = with_loaded(&dir, &cache, false, |s, _| {
        (s.elab.check_cache_stats(), goals_of_still_one(s))
    });
    assert_eq!(
        (open.namespace_hits, open.namespace_misses),
        (0, 2),
        "{open:?}"
    );
    assert_eq!(goals, ["A.oneIsOne.?1"]);
    write_file(&dir, "src/A.sw", A);
    let (filled, goals) = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        (s.elab.check_cache_stats(), goals_of_still_one(s))
    });
    assert_eq!(
        (filled.namespace_hits, filled.namespace_misses),
        (2, 0),
        "{filled:?}"
    );
    assert!(goals.is_empty(), "{goals:?}");
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// A proof below that starts using an axiom changes no digest, and
/// `axioms` still finds it from the replayed namespace above: the walk is
/// over the live proofs, the edited one among them.
#[test]
fn an_axiom_a_proof_below_starts_using_is_found_above_it() {
    let a = "namespace A\n\ndef AllTrue (x y: Bool): Prop := Unit\n\n\
             def Q: Type := Quot Bool AllTrue\n\n\
             theorem same: (Quot.mk False: Q) = Quot.mk False := byComputing\n";
    let b = "namespace B\n\nimport A (Q, same)\n\n\
             theorem stillSame: (Quot.mk False: Q) = Quot.mk False := same\n";
    let dir = temp_project("digest-axiom", &[("src/A.sw", a), ("src/B.sw", b)]);
    let cache = temp_dir("digest-axiom-cache");
    let axioms_of_still_same = |s: &mut Session| {
        let id = s.elab.lookup_def("B.stillSame").expect("B.stillSame");
        stitchwort_driver::axioms::axioms(&s.elab.ev(), id)
    };
    let before = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        axioms_of_still_same(s)
    });
    assert!(!before.contains("Quot.sound"), "{before:?}");
    write_file(
        &dir,
        "src/A.sw",
        &a.replace(":= byComputing", ":= Quot.sound Trivial"),
    );
    let (stats, after) = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        (s.elab.check_cache_stats(), axioms_of_still_same(s))
    });
    assert_eq!(
        (stats.namespace_hits, stats.namespace_misses),
        (1, 1),
        "{stats:?}"
    );
    assert!(after.contains("Quot.sound"), "{after:?}");
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// Where an entry's header keeps its digest: after the magic, format, key,
/// salt, the two stamp strings, the library's index and the exact flag.
fn digest_at(bytes: &[u8]) -> usize {
    let mut at = 8 + 4 + 32 + 16;
    for _ in 0..2 {
        let (mut len, mut shift) = (0usize, 0);
        loop {
            let b = bytes[at];
            at += 1;
            len |= usize::from(b & 0x7f) << shift;
            shift += 7;
            if b < 0x80 {
                break;
            }
        }
        at += len;
    }
    at + 32 + 1
}

/// `bytes` with its checksum made again, as if written so.
fn resealed(mut bytes: Vec<u8>) -> Vec<u8> {
    let n = bytes.len() - 32;
    let sum = *blake3::hash(&bytes[..n]).as_bytes();
    bytes[n..].copy_from_slice(&sum);
    bytes
}

/// `check --recheck` computes each replayed namespace's digest again: one
/// that isn't what the entry holds is an error, so the check fails.
#[test]
fn recheck_refuses_an_entry_whose_digest_was_altered() {
    let dir = temp_project("digest-altered", BASE);
    let cache = temp_dir("digest-altered-cache");
    with_loaded(&dir, &cache, false, |_, ok| assert!(ok));
    let clean = with_loaded(&dir, &cache, true, |s, ok| {
        assert!(ok, "a re-check of untouched entries passes");
        s.elab.check_cache_stats()
    });
    assert_eq!(
        (clean.namespace_rechecked, clean.digest_mismatches),
        (2, 0),
        "{clean:?}"
    );
    let path = entry_of(&cache, "ns.A");
    let mut bytes = std::fs::read(&path).unwrap();
    let at = digest_at(&bytes);
    let true_digest = bytes[at..at + 32].to_vec();
    bytes[at] ^= 1;
    std::fs::write(&path, resealed(bytes)).unwrap();
    let altered = with_loaded(&dir, &cache, true, |s, ok| {
        assert!(!ok, "an altered digest fails the re-check");
        s.elab.check_cache_stats()
    });
    assert_eq!(altered.digest_mismatches, 1, "{altered:?}");
    // The altered entry isn't kept: a plain check elaborates `A` again, and
    // writes it with its true digest, under which `B`'s entry is found.
    let after = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        s.elab.check_cache_stats()
    });
    assert_eq!(
        (
            after.namespace_hits,
            after.namespace_misses,
            after.namespace_written
        ),
        (1, 1, 1),
        "{after:?}"
    );
    let bytes = std::fs::read(entry_of(&cache, "ns.A")).unwrap();
    let at = digest_at(&bytes);
    assert_eq!(
        bytes[at..at + 32],
        true_digest,
        "`A`'s altered entry was kept"
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// The digests of a fixed project that loads no library file, pinned: a
/// change to what the digest covers (an exclusion, the sealing test) that
/// leaves entries readable changes what a stored digest promises, and an
/// entry another build wrote would then be trusted for the wrong thing
/// with `--carry-over`. A failure here means the digest's meaning changed:
/// bump `cache::FORMAT` and pin the new values. (A change to the core's
/// `Nat` or `Eq` moves them too.)
#[test]
fn the_digest_of_a_fixed_project_is_pinned() {
    let dir = temp_project("digest-pin", BASE);
    let cache = temp_dir("digest-pin-cache");
    with_loaded(&dir, &cache, false, |_, ok| assert!(ok));
    let digest = |unit: &str| {
        let bytes = std::fs::read(entry_of(&cache, unit)).unwrap();
        let at = digest_at(&bytes);
        let hex: String = bytes[at..at + 32]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        hex
    };
    let found = [digest("ns.A"), digest("ns.B")];
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
    assert_eq!(
        found,
        [PINNED_A, PINNED_B],
        "the interface digest's meaning changed: bump `FORMAT` (crates/elab/src/cache/mod.rs) \
         and pin the new digests here"
    );
}

const PINNED_A: &str = "8a6e5b67b40b62c7ee4b26636fb7fbf2d7bad6a9d5db725c816eaef120a316e4";
const PINNED_B: &str = "7aba8d8e6a0326ee87b009e08606199107121c8fc5928ff9b8e66f1e8c756ead";

/// Rule 4 end to end: `W-MODULE-NAME` in `B` labels `A.a`'s position, so
/// `B`'s entry holds a position in `A`'s file and records the project's
/// sources. A comment above `a` leaves `A`'s digest as it was, but `B`
/// misses, and its warning points where a check without the cache does.
#[test]
fn a_warning_pointing_into_the_edited_file_checks_what_holds_it_again() {
    let a = "namespace A\n\ndef a: Type := Nat\n";
    let b = "namespace B\n\nimport A (a)\n\ndef len: List a → Nat := xs => 0\n";
    let moved = a.replace("def a", "-- a comment\ndef a");
    let s = after_edit(
        "digest-rule-4",
        &[("src/A.sw", a), ("src/B.sw", b)],
        &[("src/A.sw", &moved)],
    );
    assert_eq!((s.namespace_hits, s.namespace_misses), (0, 2), "{s:?}");
}

/// An entry found under a key it wasn't made for, whose dependency's
/// statement has changed, is refused on the trusted path: its dependency
/// records are by interface hash, so a statement is compared, and a proof
/// isn't.
#[test]
fn a_replay_refuses_an_entry_whose_dependency_statement_changed() {
    let dir = temp_project("digest-dependency", BASE);
    let cache = temp_dir("digest-dependency-cache");
    with_loaded(&dir, &cache, false, |_, ok| assert!(ok));
    let old_b = std::fs::read(entry_of(&cache, "ns.B")).unwrap();
    // `one = 0 + 1` computes to `one = 1`, so `B` still checks.
    write_file(
        &dir,
        "src/A.sw",
        &A.replace(
            "theorem oneIsOne: one = 1 := byComputing",
            "theorem oneIsOne: one = 0 + 1 := byComputing",
        ),
    );
    with_loaded(&dir, &cache, false, |_, ok| assert!(ok));
    let b: Vec<_> = (entries(&cache).into_iter())
        .filter(|p| p.to_str().unwrap().contains("-ns.B+nav-"))
        .collect();
    let new_b = b
        .iter()
        .find(|p| std::fs::read(p).unwrap() != old_b)
        .expect("B's entry for the new key");
    // The old entry under the new key.
    let new_bytes = std::fs::read(new_b).unwrap();
    let mut forged = old_b.clone();
    forged[12..44].copy_from_slice(&new_bytes[12..44]);
    std::fs::write(new_b, resealed(forged)).unwrap();
    let s = with_loaded(&dir, &cache, false, |s, ok| {
        assert!(ok);
        s.elab.check_cache_stats()
    });
    assert_eq!((s.namespace_hits, s.late_misses), (1, 1), "{s:?}");
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}

/// The differential test for proofs: for each theorem of a small project,
/// its proof replaced by another of the same statement, a check through the
/// cache (which replays what is above it) holds what one without the cache
/// does, diagnostics and all.
#[test]
fn every_proof_edit_below_gives_what_a_check_without_the_cache_gives() {
    let a = "namespace A\n\nimport Std (Nat)\n\ndef one: Nat := 1\n\n\
             theorem oneIsOne: one = 1 := byComputing\n\n\
             theorem swapped (n: Nat): n + 0 = 0 + n := Nat.addComm n 0\n\n\
             theorem split (b: Bool): b = True ∨ b = False :=\n  \
             match b with\n    | True => Inl byComputing\n    | False => Inr byComputing\n";
    let b = "namespace B\n\nimport A (one, oneIsOne, swapped, split)\n\n\
             theorem stillOne: one = 1 := oneIsOne\n\n\
             theorem stillSwapped: 3 + 0 = 0 + 3 := swapped 3\n\n\
             def two: Nat := one + one\n\ntest \"two\" := two == 2\n";
    let c = "namespace C\n\nimport B (two)\n\ntheorem twoIsTwo: two = 2 := byComputing\n";
    let edits = [
        (
            "theorem oneIsOne: one = 1 := byComputing",
            "theorem oneIsOne: one = 1 := (byComputing)",
        ),
        ("Nat.addComm n 0", "(Nat.addComm n 0: n + 0 = 0 + n)"),
        (
            "match b with\n    | True => Inl byComputing\n    | False => Inr byComputing",
            "match b with\n    | False => Inr byComputing\n    | True => Inl byComputing",
        ),
        // The same proofs with a lifted `match` around each (stage C).
        (
            "theorem oneIsOne: one = 1 := byComputing",
            "theorem oneIsOne: one = 1 := (match 0 + 0 with | _ => byComputing)",
        ),
        (
            "Nat.addComm n 0",
            "(match 0 + 0 with | _ => Nat.addComm n 0)",
        ),
        (
            "match b with\n    | True => Inl byComputing\n    | False => Inr byComputing",
            "(match 0 + 0 with | _ => match b with\n    \
             | True => Inl byComputing\n    | False => Inr byComputing)",
        ),
    ];
    let files = [("src/A.sw", a), ("src/B.sw", b), ("src/C.sw", c)];
    let dir = temp_project("digest-differential", &files);
    let cache = temp_dir("digest-differential-cache");
    fresh_and_cached(&dir, &cache);
    for (from, to) in edits {
        assert!(a.contains(from), "{from}");
        write_file(&dir, "src/A.sw", &a.replace(from, to));
        let s = fresh_and_cached(&dir, &cache);
        assert!(s.namespace_hits >= 1, "`{to}`: {s:?}");
        assert_eq!((s.refused, s.late_misses), (0, 0), "{s:?}");
        let source = Source::Project("p".to_string(), dir.clone());
        let fresh = run(&source, false, None);
        let cached = run(&source, false, Some(&cache));
        assert!(
            fresh.dump == cached.dump,
            "`{to}` without navigation: {}",
            first_difference(&fresh.dump, &cached.dump)
        );
        write_file(&dir, "src/A.sw", a);
    }
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&cache);
}
