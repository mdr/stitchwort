# SW-2919: the playground's project checks keep no check cache (plan)

Paper lane, read-only. Numbers marked (measured) come from the repo's own
docs or files; (est.) are mine and unmeasured.

## 1. Cause

The browser's language server has a check cache for the standard library only,
and nothing for project namespaces. Three facts add up:

1. **No on-disk cache in the browser.** `Memory::project_cache` returns
   `self.cache`, which is `None` for the playground (`Memory::default()`;
   only tests use `Memory::with_cache`): `crates/lsp/src/source.rs:274-276`
   (struct at :146-150, doc "there is no check cache" at :144). The native
   server's `DiskSource::project_cache` returns `<project>/.stitchwort/cache`
   (`source.rs:129-135`), and the CLI does the same with
   `session.use_check_cache` (`crates/cli/src/main.rs:1890`).
2. **The fallback store is read-only.** `ProjectWork` setup in
   `Server::load_project` (`crates/lsp/src/lib.rs:4112-4122`) takes the
   `else if let Some(bundle)` branch: `BundleStore(bundle)`. That store's
   `write` is a no-op (`crates/driver/src/check_cache.rs:~233`,
   `fn write(&self, _: &str, _: &Key, _: &[u8]) {}`) and its entries come from
   `build_library_cache`, which records only units starting `std.`
   (`BundleRecorder::write`, `check_cache.rs:~278`). So a namespace's lookup
   (`ns.Aoc.Year2025.Day05+nav+ty`, key from `namespace_keys`,
   `crates/driver/src/project.rs:632-668`) always misses, and its fresh entry is
   thrown away.
3. **Every edit re-checks the settled steps.** `LiveProject` rewinds the linear
   session journal to the edited namespace (`crates/driver/src/live.rs:~900-962`),
   which drops every later step; "the settled steps (checked again from the
   cache, or in full without one: minutes, for a large project)" follow
   (live.rs comment at ~:946). SW-2915 (commits ac2a4a743, 4f7d52e5f) only
   reordered the work so the edit's own diagnostics come first. The settled tail
   is still a full re-elaboration in the browser.

The mechanism itself is on in the browser: `uses_check_cache()` is true with
the `BundleStore`, so `set_namespace_sources` computes keys
(`project.rs:222, 479, 541`; `live.rs:~984`). Only the store behind it is
missing. The stateless wasm entry points (`check_project`, `test_project` in
`crates/web/src/project.rs`, `new_session` via `library_session`,
`lsp/src/lib.rs:2882`) are in the same position, with a one-entry `LAST`
memo (`web/src/project.rs:~220-232`) that only helps for identical texts.

## 2. What the native editor does differently

- Entries persist in `.stitchwort/cache/check/` (`GatedCache` over `CheckCache`,
  `lsp/src/lib.rs:2932-2952`), written only while all files match disk.
  A reload or an edit is then mostly hits: measured native whole-`aoc` check
  35.6 s cold, 1.60 s warm (check-cache.md "As built (stage 3)"), because a hit
  is replayed and trusted (D1660), not re-elaborated or re-checked in the kernel.
- Real sizes from `aoc/.stitchwort/cache/check` in this checkout (measured): one
  build's entries are 356 files, 29.8 MB raw, 7.1 MB gzipped, largest single
  entry 2.5 MB (`Aoc.Year2024.Day13.Proofs`). These are CLI units without
  `+nav`; the playground's are navigable (`+nav+ty`), so larger (est. 1.5-2x:
  45-60 MB raw, 10-14 MB gz).

## 3. Browser limits that matter

- Wasm stack is 8 MiB (`crates/web/build.rs:7`), guard 256 KiB + 256 KiB reserve
  (`web/src/lsp.rs:190-193`); the "2 MiB" is the native test thread stack
  (`NATIVE_STACK`), plus V8's ~1 MiB engine stack. Replaying an entry is
  iterative decoding plus kernel admission without checks, so it adds no deep
  recursion over elaborating; risk is low but a browser test should show it.
- Memory: wasm linear memory never shrinks; a whole-project check grew it to 40 MiB
  earlier (playground-projects.md:400), now far more (native peak was 112 MB for
  135 namespaces, check-cache.md §6). 30-60 MB of entries in memory is the same
  order, under the 4 GB wasm32 limit but worth a byte cap.
- Single thread: stores are `Rc`, not `Send`; `Options` is shared across threads
  natively, so the store must live in the per-project work, not in `Options`.

## 4. Soundness constraints (what keys and invalidates)

An entry is looked up by `(unit, key)`. The key covers the compiler build
(`FINGERPRINT`), the modes and limits, the namespace's own file texts, the
config text and the namespace-name set (`namespace_keys`). The entry header
lists the dependencies with their content hashes, and a mismatch is an `Early`
miss, so editing a dependency never replays a stale dependent. Entries
carry the store's salt; `BundleStore` and the recorder use the fixed
`BUNDLE_SALT`, so a layered store must report the same salt. Namespaces with
parse errors (`parsed == false`), uncacheable ones, and ones waiting on an
errored dependency (SW-2951) are not written (stats `namespace_uncacheable`,
`namespace_waiting_on_error`). Hits are trusted, not re-run in the kernel
(D1660), which already holds for the std bundle. An in-memory store keeps that
exactly: same bytes, same keys, nothing persists past the tab. Rewinds do not
clear the cache (comment at `lsp/src/lib.rs:~4605`), and an unfinished/cancelled
check writes nothing partial (`write` is called with a complete entry).

## 5. Options

### A. In-memory writable store layered over the bundle (recommended)

A `LayeredStore { bundle: Arc<LibraryBundle>, local: RefCell<BTreeMap<(String, Key), Vec<u8>>> }`
in `check_cache.rs`: `read` tries `local` then the bundle; `write` stores units
starting `ns.` only (std stays bundle-only, so the `left_out` files are not
cached into the session); salt and compiler as `BundleStore`. Evict like D283
(a write replaces the unit's older entries, keeping the newest two so an undo hits)
and cap the total (say 192 MB, drop oldest). `load_project` uses it in the
`else if let Some(bundle)` branch.

- First whole check: no hits, same as today, plus encoding every entry
  (native +6% cold, check-cache.md stage 2; est. +5-10 s of the 129 s). Not faster.
- Re-check after an edit: the edited namespace and what uses it re-elaborate;
  the settled tail replays. Native warm/cold is 22x for the whole project
  (measured); in wasm est. the tail goes from up to ~120 s to ~6-12 s, so the
  background check finishes in roughly 10-20 s for a leaf edit (est.). Editing
  `Aoc.Common` (everything depends on it) stays near cold (matches the native
  table, check-cache.md §8).
- Also: reopening the same project in the tab, undoing an edit, and `check`/
  `test` of namespaces already checked hit.

### B. Ship the project's namespace entries in the bundle (adds to A)

Extend `bundle-std-cache.mjs`/`build_library_cache` to also check the bundled
projects (AoC first) and record `ns.` units with their `+nav+ty` keys, into a
per-project file (`pkg/projects/aoc.cache.gz`) fetched when the project is first
opened. Keys cover texts and config, so only unchanged namespaces hit, and an
edited bundle (or a changed compiler) is all misses, as today.

- First whole check: est. from ~129 s to ~25-35 s (17 s library replay measured
  in the search worker, plus ~8-15 s replay of ~356 entries); a first-time
  visitor downloads est. 10-14 MB gz extra (not measured; the page's wasm is
  12 MB, std.cache.gz 3 MB), lazily.
- Re-check after an edit: as A, but the first re-check also hits.
- Cost: build.sh gains the AoC project's cold check in node (about 2-3 minutes,
  est.), the bundle grows with the repo's AoC, and `LibraryBundle` must learn
  per-project files (the recorder filters on `std.`). Do after A, measured.

### C. Keep settled namespaces across a re-check (no rewind)

The session state is one linear journal (rewind drops everything after the
mark), so a settled namespace cannot survive an edit to an earlier one
without a non-linear or per-namespace state design. Not a cheap fix; a design
note, not a lane. Rejected here.

## 6. Risks

- **Memory**: entries are held twice while read (stored `Vec<u8>` plus decode),
  `Store::read` returns an owned `Vec` (a 2.5 MB clone per hit). Mitigate with the
  cap and, if needed, `Rc<[u8]>`; not a trait change for A.
- **Cold cost**: encoding every namespace's entry on the first check (est.
  +5-10 s on 129 s); the first check is not helped by A. Measure.
- **Churn from keystrokes**: an edited namespace is rewritten each check; the
  two-per-unit rule bounds it. Entries for unsaved text are fine here (no disk
  to pollute), so no `GatedCache`-style gate.
- **Wrong-store reuse**: do not put it in `Options`; project reload via
  `add_project` makes a new `ProjectWork` and a fresh store (lost entries: a
  full check on re-add, as today). A store keyed by project root in the Server
  would keep them; optional.
- **Differential check**: `late_misses`, `refused` must be 0 (the existing
  differential tests assert it for disk caches).
- Stack: replay should not deepen recursion, but the browser stress test
  (`web/stress.html`) is the place to see it.

## 7. Recommendation

Do **A** now (small, sound by construction, only layers a store). Then measure
in the browser and file **B** with the numbers. Reason: A fixes the edit loop
SW-2915 made visible (the tail redone after every edit, minutes) and touches no
bundle format; B needs a build step and a format change and is better judged on
A's measured replay cost.

## 8. Build-lane brief (Sonnet; expected 60 min, stop at 90)

Goal: the playground's language server keeps an in-memory check cache for
project namespaces, so a re-check after an edit replays the settled
namespaces instead of re-elaborating them (SW-2919, after SW-2915).

Change:
1. `crates/driver/src/check_cache.rs`: add `pub struct LayeredStore` (bundle +
   `RefCell` map of `ns.` entries; salt `BUNDLE_SALT`; compiler the bundle's).
   `write` keeps only units starting `ns.`; replaces the unit's older entries,
   keeping the newest two; total cap 192 MB, oldest dropped first. Add
   `pub fn namespace_entries(&self) -> usize` for tests. Comment why std is
   not written and why no disk gate.
2. `crates/lsp/src/lib.rs:4117-4122` (`load_project`): use
   `Rc::new(LayeredStore::new(bundle.clone()))` in the bundle branch; keep
   `skip = bundle.left_out.clone()`. Leave the `GatedCache` branch alone.
3. Optionally `library_session` (:2882) users in `crates/web/src/project.rs`
   keep `BundleStore` (no change: stateless one-shot sessions).
4. No `docs/` language changes. Add a line to
   `docs/proposals/check-cache.md` ("As built": the playground's in-memory
   layer) and fix the `Memory` doc (`source.rs:143-144`, "there is no check
   cache") to say the server keeps an in-memory one.

Tests (by name, one command at a time, `nice -n 15`):
- New unit test in `check_cache.rs` tests: a layered store reads the bundle,
  stores `ns.` entries, refuses `std.` writes, evicts to two per unit, stays
  under the cap. `task test:one -- a_layered_store`
- New LSP memory test in `crates/lsp/tests/it/memory.rs` (pattern of
  `files_the_client_asks_for...`), project with 3 namespaces A <- B <- C
  using the `Inline` server with `Options` whose `library` is the test std
  bundle (as `cached_memory` does): open the project, check, edit B's text,
  recheck; assert via a counter on the layered store (or `check_cache_stats`)
  that C's second check is not a miss when it does not use B, hits for the
  unchanged namespaces, and that diagnostics equal those of a fresh server
  (soundness). `task test:one -- -E 'binary(it) & test(/memory::.*cache/)'`
- Existing: `task test:one -- an_edit_re_elaborates_the_namespace_and_what_uses_it`
  (driver, unchanged behaviour) and
  `task test:one -- a_project_in_memory_is_checked_as_a_project`.
- Browser (only if the machine is quiet; one test): web/test.sh with the
  existing test "in a project, after a jump into another file and the whole
  project's check, an error in the day is underlined" (SW-2914/2915); report
  the whole-project check time before/after. Do not run the browser suite.
  Do not run any aoc/ check or std audit.

Report: before/after of the SW-2915 browser test's re-check time; sizes of
`local` after a whole AoC check (print `namespace_entries()` and bytes once in
the test log, do not commit the number).

Findings to file after the lane: B (project entries in the bundle, with
measurements); the `Store::read` owned `Vec` clone for large entries.
