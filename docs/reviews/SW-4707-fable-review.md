# SW-4707 Fable review: check-cache keys by interface digest, stage A

Review of `36ee7bdc0` on `lane/SW-4707` against docs/proposals/interface-digest-cache.md
(SW-4706, D3728) and the lane's notes (docs/reviews/SW-4707-notes.md). 23 Nov 2026.
Method: the diff of `crates/elab/src/cache/{mod,codec}.rs`, `module.rs`, `session.rs` and
`hash.rs` read in full; `plan_skips` and the replay caller read; 20 two- and
three-namespace probe projects run with the lane's release binary (cold, warm, edit, then
the cached result compared with `--no-cache`); the lane's 19 `check_cache::digest` tests
run once (19 passed, 14 s). Each claim below is marked **[run]** (a probe),
**[read]** (code) or **[not checked]**.

## Verdict

**Merge.** No stale replay found: in every probe the cached result after the edit was
the `--no-cache` result, and every edit a dependant can see changed the digest or the key.
The build meets the design's four properties as far as I could test them. Two small
things to fix after merging (findings 1 and 3), neither a wrong verdict today.

## Findings

### 1. A digest mismatch on `--recheck` leaves the entry trusted, and can re-stamp it (low to medium)

**[read, not reproduced]** `elaborate_namespace_cached` (`cache/mod.rs`, the `Ok((mut
warnings, digest))` arm): when `replay_namespace` reports `E-CACHE-DIGEST`, the caller
correctly gives the namespace no digest, but still runs `keep_rechecked` under
`hit.recheck`. For an entry another build wrote (`--recheck --carry-over`),
`keep_rechecked` writes it back stamped as this build's own, with the old digest, "so
that the next session carries it over without checking it again". That is the one case
where a mismatch is likely to be real (a build whose digest covers something different,
question 5), and the entry that failed is made to look confirmed. For an entry this
build wrote, nothing is rewritten, but the entry stays in the store, so the next plain
`check` trusts it and passes; the message's advice (`--no-cache`) doesn't replace it
either, since `--no-cache` writes nothing.

Fix: on a mismatch, skip `keep_rechecked`, and replace the entry: either treat it as
`Miss::Late` (the namespace is then elaborated over the replay and written with a fresh
digest, with the error and the count kept), or delete it from the store. A test: alter a
digest as `recheck_refuses_an_entry_whose_digest_was_altered` does, run `--recheck`, then
a plain check, and assert the altered entry isn't a hit.

"Not undone" is otherwise safe **[read]**: with `--recheck` every term of the replayed
namespace went through the kernel; the namespace is put in `failed_namespaces` and has no
digest, so every namespace above it gets a text key, misses, is elaborated, and isn't
written; the error fails the check. `--recheck` exists only on `check`, and
`plan_skips` isn't used with it, so no later step in that session reads a cached
"finished" from the state.

### 2. What `--recheck` can and can't catch (information)

It recomputes the digest from the *replayed* state and compares it with the header. So
it catches a header that was altered, a replay that doesn't rebuild what elaboration
built in a part the digest covers (a P1 failure for that namespace), and a digest
function that differs from the one that wrote the entry. It cannot catch a digest that
leaves out something a dependant reads: both sides leave it out. That case is caught
only by the differential test (`every_proof_edit_below_…`) and the rolling
`check --no-cache`. The design's section 2.4 reads as if the recheck were a net for a
"digest that misses an input"; it isn't, and the notes should say so.

### 3. Nothing pins the digest's meaning to `FORMAT` (low; fix before stage C)

**[read]** Because the digest is the entry encoder run again, any change to how entries
are written already forces a `FORMAT` bump (old entries would not read back). The
unguarded case is narrower: a change to the *exclusion list* alone (an `if !digest`, the
`sealed` test, stage C's reachability pass, stage D's rule 3), which leaves entries
readable and changes what a stored digest promises. Within one build that is harmless
(keys just differ); across builds it matters only with `--carry-over`. A guard is cheap
and worth having before stage C: a test that checks a fixed two-namespace project with
no library use and asserts the two digests in hex, its failure message saying "the
digest's meaning changed: bump `FORMAT`". With finding 1 fixed, `--recheck --carry-over`
is the run-time detector of the same thing.

### 4. Rule 4 has a real construct, and no driver-level test (low)

**[run]** The notes say no construct was found that puts a position in another
namespace's file into an entry. `W-MODULE-NAME` does: with `def a: Type := Nat` in `A`
and `import A (a)`, `def len: List a → Nat := xs => 0` in `B`, `B`'s stored warning
labels `A.a`'s position. Adding a comment line above `a` in `A`: `A`'s digest covers no
position, and `B` missed with "a file it holds a position in changed", was elaborated,
and the warning matched `--no-cache`. So rule 4 works end to end; this project should
be a test beside the unit test. (Such a namespace misses on any project edit, as the
notes say: coarse, sound.)

### 5. A `match` in a proof is not always a lifted helper (information, for stage C's count)

**[run]** A proof changed from one `match b with | True … | False …` to three nested
ones kept `A`'s digest (no `%match` helper is in the entry; these compile in place), and
`B` was replayed. A proof changed from `byComputing` to `match xs, g n with …` added
`A.t.%match1` to the entry, changed the digest, and `B` was elaborated. So lifted
helpers owned by theorems are in the digest, as the design requires until stage C
(question 2), and stage A's cut-off already covers proofs whose matches aren't lifted.

## Checked and sound

Question 1, the stale-replay attempts **[run]**; "replayed" means `B` came from the
cache after the edit to `A`, and in every row cached output equalled `--no-cache`:

| Edit to `A` | `B` | Note |
|---|---|---|
| a proof bracketed (positions move) | replayed | |
| a doc comment's text | replayed | `check B --index -` and `doc B.two` equal too |
| a comment above a record with a field default `B` uses | replayed | index equal |
| a proof starts using `Quot.sound` | replayed | `axioms B.stillSame` and `audit --allowed-axioms ''` name it, cached and fresh alike |
| a proof becomes `?` | elaborated | summary, `goal`, `audit` and `test` equal |
| `theorem` becomes `def` (same type and body) | elaborated | |
| a computing body; an `opaque def`'s body | elaborated | |
| a `def`'s explicit parameter renamed, `B` passes it by name | elaborated | binder names are in the digest |
| a theorem's parameter renamed | elaborated | |
| parameters swapped under the same names | elaborated | |
| `A.one` changed; `C` imports only `B`, names `A.one` in full | `B` and `C` elaborated | the closure is transitive |
| a proof starts using a later declaration | elaborated | the lane's finding: lost cut-off only |
| `A` has an `export def` (never cached) | `B` elaborated on any edit to `A`, a hit when nothing changed | text key, as before |
| position-only edit, `B` holds a warning label in `A` | elaborated | finding 4 |

Also **[run]**: `theorem t: Nat := 3` is `E-NOT-A-PROP`, so no theorem holds data a
dependant could compute with; `rewrite t.eq1` and `match induct (t n)` on a theorem `t`
of another namespace are `E-NO-EQUATION` and `E-NO-INDUCT` ("nothing unfolds a proof"),
so the equation and induction generators (the body reads in `equations.rs` and
`equations/induct.rs`) don't read a sealed proof from above. `check --recheck` on seven
of the probe caches after their edits (entries written, entries replayed, and both):
no mismatch.

By reading:

- **Rule 3** (question 3). A digest is set in three places only: after a replay without
  an error, after an entry is written (which requires no error, no goal, nothing
  unfinished, no failed dependency), and by `plan_namespace` when `plan_entry` accepts
  an entry. It is cleared at the start of `elaborate_namespace_cached` and by
  `forget_namespace_digest` when `module.rs` checks without the cache path. The map is
  the `Logged` one the key is in, so a rewind (and `check_in_order`'s fallback rewind
  after a plan) takes both back together; a plan's digests that survive that rewind are
  each reset as their namespace is loaded, before any dependant's key is computed.
- **Written and replayed digests agree.** A replay returns the header's digest, which
  the writing session computed; the probes show an entry rewritten with the same
  content gets the same digest, and `--recheck` recomputes it from decoded terms. The
  by-content node table makes that possible: nodes are deduplicated on their bytes and
  children are named by absolute node number, so the stream doesn't depend on sharing.
  The stream stays unambiguous: every part is length-prefixed in the hash, the sealed
  flag is always written in digest mode, and each omitted part has a fixed place.
- **The plan.** `plan_skips` marks a namespace "uncertain" when its plan fails, and
  everything above an uncertain one is loaded. With `planning` the key isn't computed
  when a dependency lacks a digest, so nothing above an edited namespace is ever left
  out unloaded; it is loaded and replayed. More careful than needed, and right.
- **The exclusions** (question 2) are exactly the five in the notes. Leaving out the
  library-file records is right, although the design's table listed "library needs" as
  an input: the *needs* (files, dot names, equations) are in the digest, and each
  namespace's own `pre.library` is built from its needs plus its dependencies' reach
  (`namespace_parts`, the `library_reach` lines), and compared by `library_unchanged`
  on both the replay and plan paths. So a library file changing under `A` is caught by
  `B`'s own record. `include` records: `A`'s own entry misses when an included file
  changes, and the text read is in `A`'s terms.
- **A theorem in a group with a computing definition.** `has_interface` doesn't look at
  the group, so the theorem's body is left out and its own hash is its statement's; the
  computing member's `def_hash` is the group's hash in `Mode::Content`, proofs
  included, and is written in the digest. So such a proof edit changes the digest
  (conservative). **[read; not run: I didn't construct such a group]**
- **The key** adds `project_names[D]`, the one piece of session state a dependant reads
  that comes from `D`'s syntax and is in no entry. I re-read `Session`'s fields for
  another and found none: the rest is either in the source hash (namespace list), about
  errors (which have no digest), or rebuilt from entries (`library_reach`).
- **Positions in message text** (the notes' open P3 item): a grep of `crates/elab/src`
  for code that renders a line or column into a message found none outside navigation.
  Not a proof.

## Not checked

- The editor's path (`live.rs`): only that the digest shares the key's `Logged` map.
- P2 inside `crates/core` (erasure, `value::hidden`, termination) and `live/trial.rs`,
  as the design left them. The probes above (data theorems refused, no equations or
  `induct` for theorems, axioms and goals found by the live walk) are the outside view.
- `--carry-over` between two real builds; `check --only`; entries with navigation
  (`+nav`) and whether their digest equals the plain entry's (it needn't for soundness).
- Instance priority (I found no syntax for one), on-demand derives made in a dependant,
  a `rules` set and a `@[reading]` beyond the lane's tests.
- The measure, the cost of the second encoding pass, and library files (stage B).
- Finding 1 was read, not reproduced: altering an entry needs the test harness's reseal.

## Tickets

1. `--recheck` digest mismatch: don't `keep_rechecked`, and replace or delete the entry;
   test that a later plain check doesn't hit it (finding 1). Sonnet, small.
2. A test pinning two digests, failing with "bump `FORMAT`" (finding 3), before stage C.
3. A driver-level rule 4 test from the `W-MODULE-NAME` project (finding 4).
4. Docs: section 2.4 of the design and the notes say what `--recheck` does and doesn't
   catch (finding 2); the notes' "no construct found" line (finding 4).
