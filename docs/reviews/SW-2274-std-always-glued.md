# SW-2274: review of SW-2254 (std always elaborates glued)

Reviewed: merge e013370b8 (lane commit 529e2cd82), `Elaborator::gluing()`
= `options.glue || unit.loading_prelude` at the 13 sites that set
`machine.glue`, and the `docs/core.md` sentence. Read-only. No builds or
tests were run.

## Summary

The fix is right, and the deeper fix isn't worth doing. Gluing was never
just an evaluation flag. It is an elaboration mode: a glued value
remembers the call it came from and an unglued one doesn't, so read-back
can keep `f x` only when glued. SW-1156 already showed this
(`Std.Nat.divModEq`), and the check cache keys on it. The pins
(`crates/core/src/pins.rs`) hash elaborated terms by design (backend-trust
P2), so they pin the library as the default elaborator makes it. One
canonical elaboration of std is what a pin needs, and SW-2254 provides
it. None of the 13 sites needs the old behaviour.

Two loose ends:

- On-demand library equations don't set the switch, so they still follow
  the caller's setting (F1).
- The cache's `glue` key now does nothing for library files except force
  misses (F2).

Losing "std elaborated unglued" is a small loss: that check had not run
for some time (F3).

Top recommendations:

1. Set the switch to `gluing()` around `in_library_file`'s `run` (F1).
2. Leave `glue` out of the key for library-file entries, keep it for
   project namespaces, and rewrite the cache test to match (F2).
3. Fix four stale comments (F4).
4. Optionally, add a test-only "library unglued" switch, so that one daily
   test can elaborate std unglued with the pins bypassed (F3). Backlog.

## Findings

| # | Severity | Confidence | Where | What |
|---|---|---|---|---|
| F1 | medium | medium | `crates/elab/src/library.rs:1381` (`in_library_file`), `equations.rs:5821` | Equations made on demand use the caller's glue switch, so the same library equation can come out glued or unglued |
| F2 | low | high | `crates/elab/src/state/options.rs:104-148`, `cache/mod.rs:300` | `glue` in the key now only causes library-file misses; the key's doc and the cache test's premise are stale |
| F3 | low | high | `lib.rs:909` | std is no longer elaborated unglued anywhere; the D3030 coverage that check gave was already not running |
| F4 | low | high | `proof_equivalence.rs:1284`, `options.rs:30-36`, `lib.rs:665`, `lib.rs:912` | Stale or incomplete comments |

### F1: on-demand equations follow the caller's glue setting

`ensure_equations` makes a library definition's equations "whoever asks"
(SW-1068): a proof in a user file, `search`, `doc`
(`generate_deferred_equations`), or another library file. It runs in
`in_library_file`, which enters a nested unit (`loading_prelude: true`)
but never sets `machine.glue`. Equation generation evaluates and reads
back with `quote_folded` (`equations.rs:2538`), and that keeps calls only
when the switch is on. So the result depends on who asks:

- From a user declaration with the default setting: glued.
- From a user declaration with `STITCHWORT_GLUE=0`: unglued.
- From a top-level driver call outside any `glued()`, as in `search` or
  `doc` listing every equation: unglued, because the machine's switch is
  off outside `glued()`.

SW-2254's intent ("std always glued") and SW-1068's ("they come out the
same whoever asks") both say this should be one term. Equations aren't
pinned, so nothing fails today. It does make what `search` lists differ
from what a proof uses.

My confidence is medium. I read the paths but didn't run a case.

**Fix (S):** in `in_library_file`, wrap `run(self)` in
`machine.glue.replace(self.gluing())` and restore it afterwards. Inside
the nested unit, `gluing()` is true. A test can generate one equation
from `generate_deferred_equations` and from a proof that names it, and
compare the two hashes.

### F2: the cache's `glue` key wastes library entries

`Options::cache_key` feeds `modes()` for both library-file entries
(`cache/mod.rs:287`) and project-namespace entries (`:610`). Since
SW-2254, a library file elaborates the same whatever `options.glue` says.
A `STITCHWORT_GLUE=0` run therefore misses every std entry, elaborates
std again (glued), and writes the same entries under a second key.

Three things are now stale:

- `cache_key`'s doc ("the settings that change what elaborating a library
  file gives") no longer fits `glue`.
- The test `the_cache_keeps_glued_results_from_an_unglued_run`
  (`crates/driver/tests/projects/check_cache.rs:303`) rests on
  `divModEq` differing between glued and unglued runs, which is no longer
  true for std.
- That test still asserts `hits == 0`, which now passes only because of
  the key.

User namespaces still elaborate differently, so they need the key.

The cost is small: one std elaboration per unglued run, and the switch is
rarely used. But the key now states something false.

**Fix (S–M):** build library keys with `glue` fixed to true, or left out,
and keep `glue` in namespace keys. Turn the test into two assertions:

- An unglued warm run gets library hits, and its dump matches a fresh
  unglued run.
- Project-namespace entries still miss across glue settings.

Every existing entry misses once (format churn doesn't count against the
change).

### F3: std is no longer elaborated unglued

The equality rule (`docs/core.md`, "The equality rule", Consequence) holds
every mode to one relation, and D3030 says glued and unglued agree. Std's
few thousand declarations were the largest corpus for the elaborator's
unglued mode. That loss is real, but it was already happening:

- Every program that imports `Float` failed at the pins unglued
  (SW-2254's own bug).
- The unglued corpus run on aoc took over 24 minutes and about 13 GB
  (SW-1156's follow-up), so nobody ran it.
- The kernel checks std's bodies glued either way (`admit_group`), so its
  coverage is unchanged.
- The planned evidence for D3030 is the enumerated three-way harness and
  the G probes in `proof_equivalence.rs` (glued, unglued, kernel,
  reference, plain), and the plain evaluator in `reference.rs`. None of
  them depends on std being elaborated unglued: the harness's `glue:
  false` row switches gluing off after loading.

So nothing the equality plan currently relies on is lost.

**Option (M, backlog):** to get the corpus check back, add a test-only
option (`test-bypass`, beside `stale_pins_fall_back`) that makes
`gluing()` ignore `loading_prelude`. Then one ignored or daily test loads
the whole library unglued with stale pins falling back. Pins can't hold
there by construction, so the bypass is required. This finds unifier-only
D3030 gaps in real proofs.

### F4: stale comments

- `proof_equivalence.rs:1284`: says G4's probe can't load unglued because
  of SW-2254's pins. It can now, so the comment should go. The probe
  could also gain an unglued run once SW-2244 fixes G4.
- `options.rs:30-36` (`Options::glue` doc) and `lib.rs:665` (in `new`):
  they say "on unless `STITCHWORT_GLUE=0`" and should add "the library
  always glues (`Elaborator::gluing`)".
- `lib.rs:912` (`glued`'s doc): "if [`Elaborator::glue`] is set" names
  something that doesn't exist. It should name `Elaborator::gluing`.

## Answers to the brief's questions

1. **Right fix, or should terms be independent of glue?** Right fix. To
   make read-back independent of glue, you'd have to either rebuild calls
   from unglued values, which have forgotten them, or always write
   unfoldings, which throws away gluing's smaller terms. The equality
   rule asks modes to agree on what's equal, not on what term is written.
   `docs/core.md` now says the library always glues, which is the
   contract pins need.
2. **Does any site need the old switch?** No. The sites in
   `closing.rs` (the try-candidate `Restore`s), `goals.rs` and `glued()`
   run inside a library declaration's `glued()`, which already turned
   gluing on, so `gluing()` agrees with it. The rest (`open_goal`,
   `search_pattern`, `theorem_pattern`, `use_pattern`, `type_index`, the
   search `Restore`) run at query time with `loading_prelude` false, so
   they behave as before. `search_candidates` computes `type_index`
   lazily, so the index and the query use the same setting. One gap
   remains, and it isn't one of the 13: F1.
3. **Is losing "std checked unglued" a real loss?** Small, and not for the
   current plan (F3). It can come back as an opt-in test.
4. **Does the cache's `glue` key mislead or waste?** Both, for library
   entries only (F2).

## Checked and sound

- `unit.nested()` sets `loading_prelude: true` for every library file
  loaded inside any unit, including lazy loads from user code, and
  `leave_nested_unit` restores the outer unit. So a std file loaded while
  a `STITCHWORT_GLUE=0` program is checked still glues, and the program
  stays unglued afterwards.
- No direct reads of `options.glue` remain except in `gluing()`.
- The forced switches at `unify.rs:3619`, `auto.rs:827-831`,
  `interfaces.rs:1281` and `search.rs:400` are independent of this change.
- Test helpers that set `loading_prelude = true` to elaborate small
  sources (`queue.rs:2332`, `:2597`, `rows.rs:545`, `library_tests.rs:31`)
  glue anyway, and they turn the switch on themselves afterwards.
- With `STITCHWORT_GLUE=0`, user code now refers to std terms that keep
  folded calls. Evaluating them unglued just unfolds them, which is
  harmless.

## The 1 Nov review's finding in scope

`rust-codebase-review.md:261`: manual save and restore of the glue switch
isn't panic-safe. It is **still open and unchanged**. SW-2254 kept the
same pattern: `glued()`, `open_goal`, the `goals.rs` sites,
`search_pattern`, `theorem_pattern`, `use_pattern` and `type_index` set
and restore by hand. The `Restore` guards in `closing.rs` and
`search.rs` are panic-safe.

## Tickets to file

- **Lane A (Sonnet, about 40 min):** F1 and F4. Set the switch in
  `in_library_file`, add an equation-hash test (made on demand from
  `search` versus from a proof), and fix the four comments.
- **Lane B (Sonnet, about 45 min):** F2. Key library entries without
  `glue`, keep it in namespace keys, and rewrite
  `the_cache_keeps_glued_results_from_an_unglued_run` as two
  assertions.
- **Backlog (Sonnet, about 60 min):** F3's option, a test-only "library
  unglued" switch plus one ignored test that loads std unglued with the
  pins bypassed.

## Calls I made

- F3 goes to the backlog as an option, not a D question: it's a test
  strategy, and reversible.
- No D questions.
