# Code review: `crates/driver` (SW-1882)

**Status:** review by reading only, 7 November 2026, Opus. Nothing was built
or run, so every claim about behaviour comes from the code and carries a
confidence. Scope, as briefed: sessions and their mark and rewind, project
loading and namespaces, the check cache (keys, replay, format versions), the
test std cache (`TestCacheTurn`, fingerprints), navigation probes (`at.rs`),
extraction entry points, and how the driver calls the elaborator. The crate is
about 16,000 lines under `src/`. I read `driver.rs`, `rewind.rs`,
`check_cache.rs`, `fingerprint.rs`, `build.rs`, `test_run.rs` and `project.rs`
in full, the planning, rewinding and answering parts of `live.rs`, and
`at.rs`'s probes. I read the check of a single proof in `search_at.rs` and
`run.rs`'s IO operations, but not those files in full. `doc*`, `search.rs`,
`completion.rs`, `marks.rs`, `audit.rs` and `axioms.rs` got only a skim. I
followed the cache key and rewind into `crates/elab` as far as the driver's
calls depend on them.

This review builds on, and doesn't repeat,
[SW-1808-kept-search-session.md](SW-1808-kept-search-session.md) (the kept
probe session), [check-cache-key.md](../proposals/check-cache-key.md) (whether
to narrow the check cache's key) and
[test-cache-key.md](../proposals/test-cache-key.md) (the evaluation
fingerprint).

## Summary

The driver is sound on every point I was asked to look hard at. I found
nothing that can make a cache hit give a result the current code and sources
wouldn't. The 1 November finding is fixed properly: both fingerprints now read
their crate sets from the manifests, and tests compare those sets with
`cargo metadata`. The test cache's key is narrowed to the Rust that runs a
term, and the reasoning behind that holds when I check it against the code:
lowering, natives, erasure and partiality all live in `core` and `rt`, or are
fixed by the test's hash. Session rewind is complete at the driver's level
(three fields, all restored), and the elaborator's rewind names every field,
so a new one can't be left out without a compile error.

Project loading reports a missing or malformed `stitchwort.yaml`, a missing
source folder, unreadable files, namespace cycles and clashes as diagnostics,
with no panics I could reach. The only threads are the tests' `par_map`
helpers. The process-wide state is two mutex-guarded parse caches, which are
keyed by text and bounded.

What I did find is mostly at the edges:

- **(M1) A latent hole in a trusted path.** A session built on a custom
  prelude keys its check cache on the *standard* prelude's text. Nothing
  combines the two today, and nothing stops it either.
- **(M2) A swallowed IO error.** A source subfolder that can't be listed is
  skipped without a word, so `check` can pass without having seen its files.
- **The rest is low.** The test std cache's "full" marker ignores std edits,
  which brings back the thundering herd for proof lanes. The temp-file name
  can collide between threads. Editor warnings for namespaces that weren't
  rechecked go stale. And there is a pattern of setters on the elaborator
  whose order is a protocol that lives only in comments.

### Top five recommendations

1. **Key on the core actually loaded** (M1, Sonnet, S): refuse a check cache
   for a session whose prelude isn't the index's, or hash the loaded text.
2. **Report unreadable source folders** (M2, DeepSeek, S): make `walk` push
   `E-IO` when a subfolder can't be listed, and say "isn't a folder" for a
   file.
3. **Make the test std cache's marker cover the library** (L2, Sonnet, S):
   write the library keys' digest, not only `FINGERPRINT`, so a std edit
   re-arms the one-filler turn.
4. **Small fixes to the fingerprint and to writing entries** (L3, L4, Sonnet,
   S): fail the build when an `EVALUATION_FILES` entry is missing, and add a
   counter to temp-file names.
5. **Keep editor diagnostics fresh, and make cancelling panic-safe** (L5, L6,
   L7, Sonnet, M): work out doc-link warnings again for the steps kept by a
   rewind, take only the warnings after the mark, and turn cancel-watching
   off when a check panics.

Counts: 0 high, 2 medium, 11 low (one of them a group of test gaps).

## Findings

| # | Where | What | Sev | Conf | Size |
|---|---|---|---|---|---|
| M1 | `driver.rs:495-606`, `elab/src/cache/mod.rs:527-528` | A custom-prelude session keys cache entries on the standard core's text | medium | high | S |
| M2 | `project.rs:1518`, `project.rs:1491` | An unlistable source subfolder is skipped silently; a source "folder" that is a file is reported as missing | medium | high | S |
| L1 | `build.rs`, `check_cache.rs:59` | Build profile and dev features aren't in any fingerprint; dev and distributed builds share entries | low | medium | S (D2680) |
| L2 | `driver.rs:256-306` | `TestCacheTurn`'s marker says "full" after a std edit, so every process re-checks the edited files at once | low | high | S |
| L3 | `fingerprint.rs:116-120, 157` | A missing `EVALUATION_FILES` entry is hashed as empty instead of failing | low | high | S |
| L4 | `check_cache.rs:129-132` | Temp-file names (`pid`, `nanos`) can collide between threads of one process | low | medium | S |
| L5 | `live.rs:882-970`, `live.rs:652-657` | Steps kept by a rewind keep their `W-DOC-LINK` warnings, which go stale when another namespace's names change | low | medium | S-M |
| L6 | `live.rs:1170-1172` | `LiveFile::step` takes every session warning, including any from before its mark | low | medium | S |
| L7 | `rewind.rs:97-111` | `cancellable_at` leaves cancel-watching on if the check panics | low | medium | S |
| L8 | `check_cache.rs:74-102`, `driver.rs:1217-1251` | Each write scans the whole cache directory, and sessions with different keys for one unit evict each other | low | low | S to measure |
| L9 | `project.rs:704, 952, 968, 985, 1005-1052` | Namespace graph helpers are quadratic (linear lookups by name; dependencies recomputed per namespace) | low | high | S-M |
| L10 | `driver.rs:335-480` | `Session::start` takes three positional booleans at eleven call sites | low | high | S |
| L11 | `project.rs:139-142, 422-425, 488-491`, `live.rs:942-964` | Setting up the elaborator is a protocol of setters kept in comments, and the namespace key's inputs are assembled twice | low | high | M |
| L12 | tests | Test gaps: `TestCacheTurn`, an unreadable subfolder, a custom prelude with a cache, stale warnings in the editor | low | high | S each |

## Details

### M1. A custom-prelude session keys its cache on the standard core

`Session::start` installs the standard `LibraryIndex` whatever prelude it was
given (`Library::Standard => LibraryIndex::standard(stack)`). When the prelude
differs from `index.files[0].text`, it parses and loads the custom text
instead (`driver.rs` around line 548). It then calls
`install_library(index)`. The check cache's `library_interface` digest
(`elab/src/cache/mod.rs:527-528`) hashes `index.files[0].text`, which is
the standard prelude, not the one loaded. Every library and namespace key
inherits that digest.

So a `with_prelude(custom)` or `try_with_prelude` session that is later given
a check cache (`use_test_std_cache` or `use_check_cache`) computes the same
keys as a standard session. It would then replay entries made against the
standard core. Replay is trusted (D1660: the kernel doesn't check it again).
References by content hash catch a changed *definition*. They don't catch a
change the hashes don't carry, such as an instance, an operator's elaboration,
a flag set by the prelude's bootstrap, or a name's kind. Those change what
elaborating a library file gives.

Nobody does this today. I found no caller that pairs `with_prelude` with a
cache; `cli/tests/extraction/extract.rs` uses both, but on different
sessions. It is a trap with nothing to stop it, sitting on a trusted path.

**Recommendation (S):** in `Session::start`, record whether the loaded
prelude is the index's. Then either make `use_test_std_cache` and
`use_check_cache` refuse such a session (debug assertion plus a no-op), or
hash the loaded prelude's text rather than the index's in
`library_interface`. Add a test where a custom-prelude session with a cache
gets only misses.

### M2. Source folders that can't be read are skipped without a word

`walk` (`project.rs:1518`) starts with
`let Ok(mut entries) = files.entries(dir) else { return; }`. Only the source
*roots* are checked first (`project.rs:1491`). A subfolder that exists but
can't be listed (permissions, or a mount that went away) silently contributes
no files. Its namespaces are missing. Anything that imports them fails with an
unknown-namespace error, but a namespace nothing imports, such as a test
namespace or a day's `Tests`, just isn't checked, and `stitchwort check` and
`stitchwort test` report success.

The roots check has the opposite problem. `sources: [main.sw]`, a file, is
reported as "the source folder `main.sw` doesn't exist", which is untrue and
sends the user looking in the wrong place.

**Recommendation (S):** in `walk`, turn an `entries` error into
`E-IO: can't read the folder {project}/{dir}: {e}`, as unreadable files
already are. For roots, tell `NotFound` apart from "not a directory". Test
both with a `MemoryFiles` variant whose `entries` fails for one path.

### L1. Build profile and dev features aren't in any fingerprint

`FINGERPRINT` and `EVAL_FINGERPRINT` hash sources, the lock file, the
toolchain and the target. They don't record the profile (debug or release) or
which features the build has on. Hashing `dev-features`' sources (SW-1741)
makes a *change* to the feature set miss. It doesn't make a build that has
them on differ from one that doesn't.

The CLI and editor (built without `dev`) share `aoc/.stitchwort/cache` with
the AoC tests (built with it), and debug and release test binaries share
`target/test-std-cache/{stack}`. Two effects, both mild:

- **Stack limits.** `Limits::stack` is in bytes, and a debug frame is larger.
  A namespace that checks within the stack in release can run out in debug.
  Only clean units are written (D284), so a release entry replayed by a debug
  build hides a debug-only `E-RESOURCE`. A false *failure* can't be served.
- **Dev-only checks.** `reference` turns on `validate_inert` inside group
  checks. An entry a release build wrote is replayed by a dev build without
  that check ever having run on the unit. Since replay skips the kernel
  anyway, this only matters for that check's purpose as a dev-build tripwire.

The test cache doesn't store `OutOfResources`, so the first effect doesn't
reach it. Overflow behaviour that differs between profiles in `core` or `rt`
would reach it, but that would be a bug in itself.

**Recommendation:** see D2680. If the answer is to split, add a tag for the
profile and features to `CheckCache::compiler` (`cfg!(debug_assertions)`,
plus a `stitchwort_core::FEATURES` string made of `cfg!(feature = ...)`).
That is S. Otherwise, document in `check_cache.rs` that sharing is
intentional and why it is safe.

### L2. The test std cache's marker ignores std edits

`TestCacheTurn::take` (`driver.rs:256-294`) treats the cache as full when the
`.done` marker holds `FINGERPRINT`. Since SW-1330, std's text isn't in
`FINGERPRINT`: a std-only edit leaves the marker valid while the edited file's
key, and the keys of every file that reaches it, have changed. Every test
process then skips the lock and checks those files itself, all at once. That
is the herd the turn exists to stop, now on the commonest kind of edit in proof
lanes. The cost is CPU only; correctness is untouched, because the keys miss
properly.

**Recommendation (S):** write and compare
`FINGERPRINT + digest(library keys)` (or the index's texts) in the marker. The
digest is cheap once the index is built. Add a unit test of the turn: marker
absent, wrong and right; `finish` writes it; a second `take` doesn't lock.

### L3. A missing evaluation file is hashed as empty

`EVALUATION_FILES` (`fingerprint.rs:116-120`) names
`crates/driver/src/test_run.rs` by path, and `evaluation_fingerprint` reads
each file with `unwrap_or_default()` (line 157). If `test_run.rs` is renamed
or split, the fingerprint quietly stops covering the code that decides test
outcomes. `the_evaluation_fingerprint_covers_core_and_rt_graphs` only checks
that the path is *listed*, not that it exists. `build.rs` reads its other
sources with `expect`, so this one silent read is the odd one out.

**Recommendation (S):** `expect` in `evaluation_fingerprint` when it's called
from `build.rs` (or assert in the test that each `EVALUATION_FILES` entry
exists).

### L4. Temp-file names can collide inside one process

`write_atomically` names its temp file `.tmp-{pid}-{nanos}`
(`check_cache.rs:132`). The tests' `par_map` workers each have their own
`CheckCache` on the same directory, and on macOS `SystemTime` is often only
microsecond-precise. Suppose two workers' writes land in one tick. The second
`fs::write` overwrites the first's temp file, the first `rename` moves the
*second* entry under the *first* unit's name, and the second `rename` fails.

That is safe, because an entry carries its key and is a miss under another one
(`cache/mod.rs:1858`, "another key"). But one entry is lost, one is misfiled,
and the error is swallowed.

**Recommendation (S):** add a process-wide `AtomicU64` counter to the name.

### L5. Kept steps keep stale doc-link warnings in the editor

Doc links resolve against loaded names and, failing that, against every
project namespace's pre-pass names (`elab/src/doc_links.rs:161-173`). That is
what makes them independent of order in `check`. In `LiveProject`, a rewind
keeps every step before the first namespace whose files changed
(`live.rs:900-910`), and `answers` publishes the kept steps' stored
`diagnostics` (`live.rs:656`).

Suppose an edit to namespace B adds or removes a declaration that a doc link
in an earlier, unchanged namespace A names. A's step is kept, and the editor
keeps showing A's old `W-DOC-LINK` (or keeps not showing a new one) until A is
checked again. `stitchwort check` gives the right answer. The comment that
links "adds no dependency" is exactly why they must be worked out again here.

**Recommendation (S-M):** when `make_plan` keeps steps and the project's
names changed, replace the kept steps' `W-DOC-LINK` warnings with fresh
`doc_link_warnings` for their files (cheap: syntax plus a name lookup). Or
store steps without them and compute them in `answers`.

### L6. `LiveFile::step` takes warnings from before its mark

`self.diagnostics = std::mem::take(&mut self.session.warnings)`
(`live.rs:1171`) takes the whole vector, including anything there when `base`
was marked. That is normally nothing, since the prelude has no warnings, but a
caller that loaded something before handing over the session would see those
warnings published for this file once, and then lost. It also leaves
`warnings.len()` below `mark.warnings`, which `rewind`'s `truncate` tolerates
only by being a no-op.

**Recommendation (S):** take `warnings.split_off(base_len)` (keep the length
at the mark).

### L7. Cancelling isn't panic-safe

`cancellable_at` (`rewind.rs:97-111`) turns `watch_cancel(true)` on, runs `f`,
then turns it off. If `f` panics (an internal error in the elaborator,
`stack-check` in tests), watching stays on. In a language server that catches
the panic and keeps the session, a later check outside `cancellable` would
honour the flag after all, against the documented "checking outside
`cancellable` costs nothing extra". The session itself is mid-declaration
after a panic, and the next `mark` asserts on that. That is the bigger
problem, and it belongs to the server's recovery.

**Recommendation (S):** a drop guard that turns watching off. Separately,
document that a session that panicked must be dropped, or have the guard
rewind to `mark`.

### L8. Eviction scans the directory on every write

`CheckCache::evict` and `Cache::evict` `read_dir` the whole folder on each
write (`check_cache.rs:76`, `driver.rs:1222`). A cold project check writes
once per namespace and library file, so the scanning is O(units × entries).
That is a few hundred directory reads of a few hundred names each for AoC,
which is probably milliseconds but invisible in profiles.

Eviction deletes "the unit's other entries for this build". Two sessions that
compute different keys for the same unit, such as different limits or options
on one project cache (the AoC tests and the CLI, if their limits differ),
delete each other's entries on every write. I didn't establish whether their
limits differ.

**Recommendation (S, measure first):** count `namespace_misses` for an AoC
check right after an AoC test run. If they thrash, keep the newest *k* keys
per unit, or put the limits in the unit name.

### L9. Namespace graph helpers are quadratic

`Analysis::namespace` (`project.rs:704`) is a linear search, and it is called
inside `closure`, `dependents`, `canonical_order`'s `uses` closure (rebuilt
for each name) and the cycle search. `dependencies` (`project.rs:952`) runs
`closure` plus `canonical_order` and is called once per namespace by both
`plan_skips` and `check_project_namespace`. `canonical_order` uses
`order.contains` (line 1052). Together that is roughly O(N²·E) for N
namespaces. At AoC's scale (a few hundred namespaces) it costs little. At a
few thousand it would be seconds before any checking starts.

**Recommendation (S-M):** index `Analysis` by name (`BTreeMap<String,
usize>`), and compute every namespace's dependencies once, in topological
order, from the canonical order.

### L10. `Session::start`'s positional booleans

Eleven constructors call
`Self::start(prelude, Library::Standard, true, false, false, limits, cache)`.
The three booleans are `eager`, `library_tests` and `navigation`, and
swapping two of them still compiles. This goes against CLAUDE.md's rule on
call sites.

**Recommendation (S):** a small `Start { eager, library_tests, navigation,
.. }` struct, or enums.

### L11. Setting up the elaborator is a protocol kept in comments

To load a project, the driver calls these in order:

1. `set_project_namespaces`, which must come before the pre-pass.
2. `set_project_names`, which must come after it.
3. `set_include_location`, once for each file.
4. `set_namespace_sources`, if a check cache is in use; it must come before
   checking.
5. `probe_*`, just before the probed namespace, which the file id picks out.
6. `set_file_mode` with a context, then `set_file_mode(None)`, around a
   single-file load (not panic-safe).
7. `set_next_include_location`, which the *next* `load_file` takes up.

The ordering rules live in each setter's doc. Step 4 is repeated in
`load_analysis_for`, `load_namespaces_for` and `recheck_analysed`, and
`LiveProject::make_plan` builds the same `NamespaceSources` its own way:
display names made by hand, and the config taken from a field rather than the
source map.

A slip here is safe for the cache: a missing or different key is only a miss.
But if the CLI's and the editor's key inputs drift apart, they silently stop
sharing entries, and nothing would notice.

**Recommendation (M, when the area is next touched):** one driver function
that takes an `Analysis` (plus config) and sets up the elaborator for it, used
by all four paths. Add a test that the CLI's `namespace_sources` and
`LiveProject`'s keys are equal for the same files.

### L12. Test gaps

- `TestCacheTurn`: no direct test of the marker, the lock or `finish` (it is
  used only through the language server's tests).
- An unreadable source subfolder (M2).
- A custom-prelude session given a cache (M1).
- The editor: an edit that changes only another namespace's names, against
  the warnings of a namespace that wasn't rechecked (L5).
- CLI and editor namespace keys agree (L11).

## Checked and sound

### Mark and rewind: what the session holds and whether rewind covers it

| State | Rewound? | How |
|---|---|---|
| `Session::sources` (`SourceMap`) | yes | truncated to the mark's length. File ids after the mark are reused, so anything holding them must be dropped with the rewind. `GoalLoad` keeps only ids from before the mark (`parsed`), and `LiveProject` drops the steps it rewinds. |
| `Session::warnings` | yes | truncated (they are only ever appended; but see L6) |
| `Elaborator`: kernel, tables, scope, attempt, decl, unit, session, caches, goals, presentation | yes | `Elaborator::rewind` destructures every field, so a new one won't compile until it says how it rewinds. Logged maps go back through the journal; project tables set whole are shared with the mark. Goals are reset, which also clears a pending `probe_context` or `probe_members`. |
| `Elaborator::options` (limits, check-cache store, include files, counterexample runner, test switches) | no, by design | "settings say how to check, not what was checked". `probe_project` and the language server's warm session set these; SW-1808 covers what that means for a kept session. |
| The budget's cancel flag | no, by design | an `Arc` shared with the host; `cancellable_at` clears it at the start |
| The budget's deadline (`search_at.rs:562-575`) | reset after each check | not panic-safe (as in L7) |
| `library_interface_digest` (`OnceCell`) | not needed | the library doesn't change within a session |
| `nav.rs`'s `DOCS` and `IMPORTS` statics | not needed | keyed by (file id, text hash), and only for std files (`user` is `index >= std_files`), so they are bounded and can't serve another text short of a 64-bit collision |
| `LiveProject`'s own fields | yes | `rewind_to` truncates `steps` and clears `plan`; `make_plan` re-checks that every kept step uses only namespaces before it, falling back to `rewind_to(0)`, and the loop ends because zero steps are trivially valid. Exception: L5. |
| Check and test caches on disk | not needed | content-keyed |

`Session::cancellable` releases its mark either way. `LiveProject::step`
releases the mark after a cancelled step (`cancellable_at` has already
rewound to it) and puts the namespace back at the front of the plan.

### Check cache soundness

- **The key** (`elab/src/cache/mod.rs:240-265` and `575-596`) covers:
  - the format version (`FORMAT = 29`);
  - the compiler, as `stitchwort-{version}-{FINGERPRINT}` (`check_cache.rs:59`);
  - the modes: natives, compact text, `options.cache_key()` (limits, `succ`,
    rewrite and instance budgets, uniform operators, glue) and navigation;
  - the library interface: the core's text and every library name with its
    kind and flags;
  - for a library file, its path and text, and the keys of the files it
    needs (a Merkle chain);
  - for a namespace, the driver's source hash and the keys of its closure.

  The driver's hash (`project.rs:584-622`) covers every namespace name, the
  config text, and the namespace's own name and its files' display names and
  texts. Namespaces with parse errors get no key, so neither do the
  namespaces that use them. Option fields left out of `cache_key` are listed
  with a reason, and destructuring makes a new option fail to compile until
  it is placed.
- **What's checked on replay:** salt, checksum, the key written in the entry,
  dependencies' content hashes, library files loaded (each listed with its
  key), and included files (each listed with a hash of its text). Only units
  without errors, goals or unfinished declarations, and not cancelled, are
  written. Counterexample searches run only when a theorem fails, which is an
  error and so never cached, and their budgets count steps, not time.
- **Std edits after SW-1330:** an edit changes the edited file's key, and
  through the chain the key of every library file that needs it. A
  namespace's entry lists the library files it loaded with their keys, and
  is compared before replay. A namespace that doesn't load the file directly
  but uses a dependency that does sees changed content hashes in that
  dependency's declarations, and misses. A change that only adds or removes
  a library name changes the interface digest, and so every key.
- **Format bumps:** `FORMAT` is hashed into every key, so entries in the old
  format are misses. A bump changes source in `elab`, and so `FINGERPRINT`
  and the file-name prefix, so eviction removes the old entries after the
  grace period.
- **Entry names** (`{FINGERPRINT}-{unit}-{key}`) can't escape the folder.
  Units are `std.` plus a path in the library index, or `ns.` plus a
  namespace name that passed `check_namespace_name`. Neither contains a `-`
  (no std file name has one today), so eviction's `starts_with(own)`
  deletes only that unit's entries. A std file named with a `-` would make
  `std.A` evict `std.A-B`, which costs a miss, not soundness.
- **Concurrency on disk:** writes go through a temporary file and a rename
  (see L4 for the name); two runs racing on the header settle on whichever is
  on disk, at worst a run whose entries nobody reads again. Test results are
  written with a plain `fs::write`, but only `passed` and `failed` parse, so
  a torn read is a miss.
- **`LibraryBundle::decode`:** it bounds every read with `split_at_checked`
  and doesn't preallocate from the count, so a truncated or corrupt bundle is
  `None`. A bundle from another build is rejected before its entries are
  read.
- **Doc links in `check`'s skip path:** a namespace with doc links is never
  skipped, and resolving a link doesn't depend on which namespaces are loaded
  (pre-pass names), so `Load::Diagnostics` reports the same warnings as
  `Load::Everything`.

### The test std cache and the test result cache

- **The test std cache** is a `CheckCache` in `target/test-std-cache/{stack}`
  under the full `FINGERPRINT`, so everything above applies; the stack is in
  the key and in the folder name. `TestCacheTurn` uses an advisory file lock
  (released on drop or when the process dies) and a marker written only by
  the holder after the load. If the lock fails, the process goes on without
  it. Its weakness is L2.
- **The test result key** is `{version}-{EVAL_FINGERPRINT}-{modes}-{hash}`.
  I checked the claim that the elaborator and parser can only change a
  result by changing the hash against `test_run.rs`:
  - lowering (`stitchwort_rt::lower_definitions`), the machine, the
    reference evaluator, erasure (`core`'s inert marks) and native binding
    (`core/src/registry.rs` `bind_def`, by content) are all in `core` or `rt`;
  - partiality (`is_partial`) shows in the test's type, so in its hash;
  - `Session::failure` only explains a failure;
  - `OutOfResources` is never stored.

  The `m` suffix keeps the fast runner's results apart from the reference
  runner's. The 1 November finding about `rt` is fixed: `rt` is in
  `evaluation_crates`, tested against `cargo metadata`.
- **The manifest reader** in `fingerprint.rs` is hand-rolled. It doesn't
  understand `[dependencies.stitchwort-x]` tables or renamed packages, but
  `the_fingerprint_covers_the_crate_graph` and
  `the_evaluation_fingerprint_covers_core_and_rt_graphs` compare its answer
  with `cargo metadata`. Those tests include any path dependency, not only
  `stitchwort-*` ones, so a form it misreads fails a test rather than
  silently shrinking the key. No workspace crate has a workspace
  build-dependency, and no code generator feeds `core`, `rt` or `elab`.

### Project errors

- **`stitchwort.yaml`** is reported in every bad case: unreadable (`E-IO`),
  malformed YAML (`E-PROJECT-CONFIG` with a label, the byte offset clamped
  to a character boundary), unknown keys (with the known ones), duplicate
  keys, an empty `sources`, a path outside the project, unknown axioms, and
  a nested project.
- **Namespaces:** cycles are found by `canonical_order` on every path
  (`load_analysis_for`, `load_namespaces_for`, `LiveProject::make_plan` via
  `fail`), and `cycle_diagnostic` labels each link. The `expect`s in
  `dependencies` and the cycle search are safe: they run only on sets that
  `canonical_order` has already accepted, or on a component of size two or
  more, which reaches its own start. In `recheck_analysed`, a new edge from
  the edited namespace to one not checked before it is reported as
  `E-NAMESPACE-CYCLE` before `dependencies` runs, and only edges *into* the
  edited namespace can change, so no cycle avoids it.
- **Files:** symlinks are skipped as documented, `include` canonicalises and
  refuses paths outside the root, non-UTF-8 files are `E-IO`, and files are
  sorted, so the order a folder lists them in never matters. Exception: M2.

### Probes and extraction

- `probe_project` arms the probe after parsing, by file id, and the
  elaborator resets goals (and with them the probe) on rewind, so a probe
  that never fires can't leak into the next check of a kept session.
- `with_dummy` and `position_at` slice by byte offsets. Their callers pass
  offsets computed from the same text (the language server's `complete::typed`
  on the text it then sends), so they fall on character boundaries.
- `extract` and `extract_namespace` refuse unfinished exports (D636), and
  `run` refuses an unfinished `main` before `extract_program` is reached.
  Export checks run after every namespace, replayed ones included, so they
  needn't be cached.

### Concurrency

- `Session` holds `Rc`s, so it is `!Send` and lives on the thread that made
  it (`with_session`).
- `par_map_with_at_most` catches each item's panic, drops the worker's state
  after one, and re-raises the earliest, which makes failures deterministic.
  Its result vector is behind a mutex that recovers from poisoning.
- The cancel flag is an `AtomicBool` read with `Relaxed`, which is enough for
  a stop request.
- `nav.rs`'s parse caches parse outside the lock.
- Across processes: atomic renames, an advisory lock, and content keys.

## The 1 November review's findings in this scope

| Finding (docs/research/rust-codebase-review.md) | Status |
|---|---|
| 1.2 The test fingerprint omits the runtime | **Fixed.** SW-1123 reads the crate graph from the manifests, tested against `cargo metadata`. SW-1329 split off an evaluation fingerprint that covers `core`, `rt`, `dev-features` and `test_run.rs`. SW-1741 adds `dev-features` to the check fingerprint. SW-1132 makes the bundle fingerprint cover `web`'s graph. What remains: L3 (a hand-listed file read without failing) and L1 (profile and features). |
| 1.2 recommendation: separate checker and runner fingerprints, test the collection of inputs | **Done** (`FINGERPRINT` and `EVAL_FINGERPRINT`, both with metadata tests) |
| 3.1 Many places must know all compiler state (rollback, rewind, cache, dumps) | **Changed.** Rewind now destructures every field, and the journal replaced copies (SW-1052). At the driver's level, `Session` has three fields, all rewound. The differential rewind test still guards behaviour. The grouping it recommends is the elaborator's to do. L11 is the driver's share of the same problem. |
| 3.3 Keep the logical trust boundary explicit | **Open, as designed.** Trusted replay is documented in `cache/mod.rs`, and for the playground's bundle in `check_cache.rs`. M1 is a place where the trusted path's key can be wrong. |

## Tickets to file

- **Lane A: cache key hygiene** (Sonnet, about 45 min). M1: refuse a cache, or
  hash the loaded prelude, for a custom-prelude session, with a test. L3:
  fail on a missing `EVALUATION_FILES` entry. L4: a counter in temp-file
  names. Add L1's tag here if D2680 says split; otherwise add L1's comment.
- **Lane B: unreadable source folders** (DeepSeek, about 30 min). M2:
  `E-IO` for a subfolder that can't be listed, "isn't a folder" for a file
  root, and `MemoryFiles` tests for both.
- **Lane C: the test std cache's turn** (Sonnet, about 45 min). L2: a marker
  with the library keys' digest, and unit tests of `TestCacheTurn`
  (absent, stale and full marker; `finish`; no lock when full).
- **Lane D: editor freshness and panic safety** (Sonnet, about 60 min). L5:
  work out kept steps' doc-link warnings again, with a `LiveProject` test.
  L6: `split_off` the warnings after the mark. L7: a drop guard for
  `watch_cancel`.
- **Lane E: mechanical tidying** (DeepSeek, about 45 min). L9: index
  `Analysis` by name, and compute dependencies once. L10: an options struct
  for `Session::start`.
- **Later, when the area is next touched:** L11, one elaborator-setup path
  for projects, plus a test that CLI and editor keys agree (Sonnet, about
  60 min). L8: measure eviction thrash on AoC first (Sonnet, about 30 min),
  and file a fix only if it shows.

## Questions for Matt

- **D2680:** should check-cache entries stay shared between dev builds (tests
  built with `dev-features`, debug) and distributed ones (the CLI and editor,
  release), accepting that a dev build may replay an entry a release build
  wrote? The only effects are a debug-only stack failure and a dev-only
  `validate_inert` check that a replayed unit skips (L1). Splitting would
  make the AoC tests and the editor stop sharing warm entries. **[rec: yes,
  keep them shared, and document why it is safe in `check_cache.rs`.]**
