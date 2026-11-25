# Review of the checking-speed profile and the D3744 plan (SW-4816)

**Status:** Fable paper lane SW-4816, 25 November 2026, 13:09-13:15, for D3745 ("yes, proceed
with Fable review"). Reviews [SW-4809](SW-4809-small-proof-profile.md) (the profile), the
SW-4806 and SW-4810 reruns at the end of [SW-4608](SW-4608-proof-checking-speed.md),
`bench/compare/proofs.py`, the Lean ports in `bench/compare/lean-proofs/`, and the plan D3744
(SW-4813, then SW-4812, then SW-4814). Nothing was built. I ran the worktree's plain release
binary four times on 2024 day 2 (one `--timings=all` run, library cached, one job; machine at
load 4-5), and did not run Lean.

Marks: **[read]** read in the code or data today; **[measured]** from my one run or the lanes'
recorded data; **[estimated]** my judgement; **[from memory]** not checked against a source
today.

## In plain words

**The measurements hold up; two of the conclusions are stated too strongly.** The old "3-5x
behind Lean" was a bench bug, and SW-4809 found it correctly. But "1.01x, 0.62x, 0.76x" reads
as more exact, and more in our favour, than three files can support: the honest statement is
**"level with Lean on these three days, 0.6-1.3x, within the noise of the comparison"**. And
the plan's third step, loading core from the cache, saves less than its ticket says (60-80 ms,
not 95 + 84) and is the only step that widens what a cached run trusts.

**Recommendation on D3744: do SW-4813 and SW-4812 now, hold SW-4814.** The first two take a
library-cached day from 1.4-1.8x Lean's file time to about 0.8-1.0x **[estimated]** and touch
nothing the kernel trusts directly. SW-4814 should wait for a re-measurement after they land,
for a fix to the core's cache key that the trust note asked for and that isn't in the code,
and for Matt's yes to "core joins the trusted cache".

## Findings, ranked

1. **SW-4814's ticket counts the same time twice.** Its title says "about 95 ms, plus 444 Std
   declarations re-elaborated through core, about 84 ms". The 444 `Std.*` rows in the
   declaration table *are* core's declarations: with the library cached, only core and the
   day's own namespaces are elaborated, and my run's table covers "482 declarations" = 38
   `Aoc` + 444 `Std`, while the unit table has core at 585 declarations, 73.3 + 20.4 = 93.7 ms
   **[measured, plain binary]**. So the gross cost is about 94 ms, and the saving is that less
   the cost of replaying 585 declarations from an entry. Cached library files replay at about
   22 µs a declaration in the plain binary (3,346 declarations in 73 ms **[measured]**), so
   core's replay is about 13 ms plus reading and decoding: **net 60-80 ms [estimated]**, the
   smallest of the three.

2. **SW-4814 is a trust change, and its precondition is missing.** Today every process
   elaborates core and its own kernel checks it (`Session::start_in`,
   `crates/driver/src/driver.rs:775-834` **[read]**); core is the one part of the base that no
   run takes from disk. After SW-4814 a cache hit installs core through `admit_trusted_*` as
   library files are (D1660). The kernel's rules don't change; what a cached run rests on
   does, by the unit everything else is built on. Separately,
   `docs/proposals/check-cache-trust.md` §2.2 (M1) asked for cache keys to hash the core text
   the session *actually elaborated*; `library_interface` still hashes
   `index.files[0].text`, the index's copy (`crates/elab/src/cache/mod.rs:1131` **[read]**;
   no digest of the loaded prelude exists in `crates/elab` or `crates/driver`). That gap is
   tolerable while core is always re-elaborated. It is not tolerable for an entry that *is*
   core: a session with another prelude would replay the standard one.

3. **The headline ratio is noisier and less like-for-like than "1.01x, 0.62x, 0.76x" says.**
   - *Lean net is a difference of two small medians of 3 runs.* Day 2's has been 143, 93 and
     118 ms in three runs (22 Nov, 25 Nov morning, 25 Nov afternoon); the empty-file time moved
     262 to 288 ms within the day **[read, SW-4608]**. Day 2's ratio is anywhere in
     0.8-1.3x on those figures.
   - *"sw net" is one run, not a median* (`own_net_seconds` runs once **[read]**), though it
     agrees with SW-4809's separate runs to 10%.
   - *"sw net" is CPU-like, Lean's is wall time.* Ours sums timers on one job. Lean elaborates
     and kernel-checks theorem bodies on several threads by default in recent versions
     (`Elab.async`) **[from memory; not checked for 4.34.1]**, so its wall time may be below
     its CPU time. This leans the ratio towards Lean; hyperfine's user and system times, which
     the bench throws away, would settle it.
   - *The two sides check different amounts.* Details in answer 1; they push both ways and
     roughly cancel.

4. **The gap is 0.25-0.32 s, not 0.5 s; the fixed costs are bigger than the gap.** Whole day,
   library cached, less Lean's file: 301, 244 and 277 ms (SW-4809, plain binary), 315, 299
   and 319 ms (SW-4810) **[measured by the lanes]**. The three fixed costs sum to about 0.5 s.
   Both figures are right; the plan's wording ("the gap is about 0.5 s of fixed cost") merges
   them. The consequence is good news: the first two steps alone reach parity, which is the
   argument for holding the third.

5. **A fourth fixed cost is not in the plan: loading library entries from the cache.** 73 ms
   on day 2 in the plain binary today **[measured]**, and by SW-4809's dev-build figures less
   `validate_marks` about 170 ms on day 18 **[estimated]**. After SW-4812 and SW-4813 it is
   the largest fixed cost left, larger than core, and making it cheaper changes no trust. It
   deserves a profile before SW-4814 is built (which would add to it).

6. **The bench measures one job; a plain `check` runs workers, and every worker repeats two of
   the three costs.** `--only` and `--no-project-cache` both force one job. In a parallel
   check each worker makes its own session, so elaborates core again, and calls `analyse` on
   the whole project's texts (`crates/driver/src/parallel.rs:996, 1016` **[read]**). The std
   index is shared (`OnceLock`). So SW-4813's saving in CPU is multiplied by the worker count
   on the command people actually run, and nobody has measured that command against Lean.
   Parsing the project once and sharing it between workers is a simpler change than a disk
   cache and may be worth doing first inside SW-4813.

7. **The index and the project analysis are not "just name resolution": both feed cache
   keys.** The index's `edges` decide which library files' keys go into a file's key
   (`library_keys`), and its names are `library_interface`, part of every key and stamp
   **[read]**; the analysis's edges and declared names feed `namespace_cache_key`. A stale
   cached index could leave a changed dependency out of a key, and the check cache then
   replays an entry without the kernel. So SW-4812 and SW-4813 sit beside the check cache's
   trust boundary, not far from it, and must follow its rule: keyed on the content actually
   read, never on modification times or sizes.

8. **Day 15's "sw net" includes all of `Aoc.Common`.** 183 + 34 = 217 ms of its 458 ms is the
   shared `Aoc.Common` namespace (709 declarations: bit readers, life, planes, prefix sums),
   checked whole because `--only` trims only the namespaces named
   (`units-cached-d15.txt` **[read]**). The Lean file ports only the grid parts. Without that
   unit day 15 is 279 ms, 0.5-0.6x; the truth is between, since Lean does port some of it.

Small: the README's "sw net / lean net: the like-for-like ratio of proof work" should say
what it leaves out (below). SW-4809's 625 ms "fully cached day 2" was a dev build; the plain
binary's figure was not recorded (my two single runs, at load 5, were 0.75 and 0.81 s, too
noisy to use).

## 1. Is (a) a fair comparison?

Fair as "we are not 3-5x behind on small proofs". Not strong enough for "we are faster".

| | sw net | lean net | leans the ratio |
|---|---|---|---|
| What is timed | internal timers: elaboration + kernel of the project's unit rows, one run, one job | wall time of `lean Day.lean` minus wall time of a file with only `import Lib`, medians of 3 | Lean's wall may hide multi-thread CPU: towards Lean |
| Parsing its own source | left out (about 1 ms: 30 KB at the 37 ms/MB the project scan shows **[estimated]**) | included | towards us, negligible |
| Name resolution, tactics, unification | included (in elaboration) | included | none |
| Kernel check | included | included | none |
| Loading the library | left out (not in the unit rows) | subtracted (`import Lib` and `Init` are in both Lean runs) | none; the load cost shows in the whole-file column |
| Per-namespace work outside declarations (27-94 ms) | included | n/a | against us |
| Compiling definitions to runnable code | none at check time | included: Lean compiles each `def` **[from memory]** | towards us, small |
| Program and parser | the whole program namespace, parser included (day 2: 28 ms of 124) | parser left out; cut-down definitions | against us |
| Shared helpers | all of `Aoc.Common` on day 15 (217 ms) | only the grid parts used | against us, day 15 only |
| Data types | equality, show and compare derived for every type (day 18: 43% of own time) | `deriving` only where needed | against us |
| Library facts used | proved in std, loaded | day 15: Dijkstra's theorem is a hypothesis and the map a function; `Lib.lean`'s lemmas precompiled | none for time (both precompiled), but Lean's objects are simpler |
| Theorems | `--only` the ported names; unported theorems skipped | the same names | none |
| Proof style | explicit `cases`, `rewrite`, `match` arms | `simp` (143 uses, 65 of them `simp only`), `omega` (40), `cases <;>` | towards us: bare `simp` searches Lean's whole simp set, and a speed-minded Lean author would write `simp only` or terms |

The ports are equivalent in statement (same names, same Bool-valued specs; I read day 2 in
full and the heads of the others) and similar in structure, since they were written by
copying ours. They are not what either community would write for speed. So the comparison is
"the same proof plan, each in its own idiom", on three files, written by agents, on one
machine.

**Corrected headline.** "On three AoC days our time on the days' own namespaces is 0.6-1.3x
Lean's net time for the ported file: level, within the noise. By day: day 2 0.8-1.3x, day 18
0.6-0.7x, day 15 0.5-1.0x." The whole-file figure, 1.4-1.8x with the library cached, is the
sounder number, since both sides are single wall times of the whole command; it needs no
correction, only the caveat that it is one job.

## 2. Is (b) right?

Yes in substance. My plain-binary run of day 2: wall 720 ms; "outside the units" 429 ms, which
is the index (about 230) plus the project scan and reading sources (about 175-200); core 94;
library entries 73; own namespaces 124 **[measured, one run]**. That matches SW-4809's
profile. Corrections:

- The gap to Lean is about 0.3 s; the fixed costs are about 0.5-0.6 s (finding 4).
- Savings are stated gross. Net of what a cache still costs **[estimated]**:
  - **SW-4812, std index:** still reads 133 files (3.4 MB) and hashes them (a few ms with
    blake3, which the cache already uses), and reads the stored names, edges and dot targets.
    Net **190-220 ms**, provided no start-up path needs every file's parsed module (see 3).
  - **SW-4813, project scan:** still reads 633 files (the 22-35 ms "project sources" stays)
    and hashes them. A third of the scan is finding edges, which depends on the whole
    project's names, so it is saved only if that part is cached too. Net **100-170 ms**.
  - **SW-4814, core:** net **60-80 ms** (finding 1).
- Missing from the plan: library entry loading (finding 5); the per-worker repeats (finding
  6). Not significant: process start (a 33 MB static binary), key hashing, printing.
- With SW-4812 and SW-4813 done: day 2 about 0.39 s against Lean's 0.36-0.41, day 18 about
  0.40-0.47 against 0.46-0.50, day 15 about 0.72-0.85 against 0.76-0.86: **parity, about
  0.8-1.0x [estimated]**. SW-4814 would then move it by another 0.1x.

## 3. What each change must keep true

### SW-4812: cache the std name index

- **Where it sits.** Outside the kernel: it holds names, not terms. But see finding 7: its
  edges and names are inputs to every check-cache key, so an index that is wrong for the
  files on disk can cause an unchecked replay. Treat it as part of the check cache.
- **Must stay true.** For the same core text and the same (path, text) set, the loaded index
  equals the built one in every field a reader uses: each file's names (key, kind, flags,
  span, follower, candidate), `owner`, `dots_by_short`, `edges`, `equation_needs`, parse
  errors, and the file numbering the session asserts (`driver.rs`, "the library's files are
  numbered as the index's"). The parsed `module` of each file becomes lazy: parsed on first
  use, from the same text, id and stack limit, so it is the same parse.
- **Key (what invalidates it).** The core text and every library file's path and text *as
  this process read them* (so any std edit, added, removed or renamed file, and a different
  `--std-dir` with different content, all miss; two directories with the same content
  rightly share); the compiler stamp the check cache uses (`store.compiler()`: covers the
  parser and the resolver, so every new binary misses); a format number; the stack limit if
  a parse can fail on depth. No modification times. No kernel fingerprint is needed: the
  compiler stamp covers it and the index has no kernel content. `Library::Files` (tests)
  either uses the same key or never caches.
- **Brief should require.** A differential test over the real std: built index against
  cached index, compared field by field (it belongs in std's own tests so every std change
  runs it); miss tests for an edit that changes a name, an added file, a removed file and a
  changed core; a corrupt or truncated cache file falls back to building, silently and
  correctly; a build error (a name declared twice, a parse error in a library file) is never
  cached; `--no-cache` builds from source, so the reference run stays independent; writes are
  atomic (several processes and workers start at once). Confirm in the brief that nothing
  reaches `LibraryIndex::build` from options or the environment (it uses a default scratch
  elaborator **[read]**). Review: Opus, with finding 7 as the question to answer. No Fable
  review needed.

### SW-4813: cache each project file's analysis (briefly)

- Same position as SW-4812: outside the kernel, but its edges and declared names feed
  `namespace_cache_key`.
- Of the ticket's two options, take the content-hash cache, not "read headers only": the
  second changes what a user sees (a syntax error in an unrelated file, a missing namespace
  line or a duplicate namespace would go unreported), which is a language-behaviour decision.
  The first can be identical: store each file's namespace line, declared names, references
  and parse diagnostics by content hash and path, and recompute the cross-file part
  (grouping, edges) each run, or key it on the whole set.
- Share one analysis between a parallel check's workers (finding 6).
- Tests: cached analysis equals fresh analysis on a small project, with edits (rename a
  namespace, add a declaration another file refers to, introduce a syntax error); a
  whole-`aoc/` comparison is the verifier's or Overmind's, not the lane's. Sonnet with an
  Opus review of the diff is enough.

### SW-4814: load core from the check cache

- **Does it change what the kernel trusts?** The kernel's rules, no. What a cached run's
  result rests on, yes: core moves from "checked by this process" to "trusted on a key
  match", joining the library files (D1660). `--no-cache --jobs 1` stays the full check, and
  tests don't use the check cache, so the tiers still check core from source. That is a
  trust decision, so it is Matt's.
- **Must stay true.**
  1. *The key is computed from the prelude text the session elaborates* (trust note §2.2,
     design A), plus everything a library file's key has: compiler stamp, kernel side,
     format, modes (natives, compact text), `Options::cache_key`, the navigation tag, and the
     library's names, because core's doc links are checked against them and a broken one
     fails the load **[read: `set_core_link_names`, `W-DOC-LINK` in `start_in`]**. Session
     flavours that change core's result (`library_tests`, `stale_pins_fall_back`,
     `Library::None` or `Files`) are in the key or never cached.
  2. *Exact hits only.* No carried-over hit for core.
  3. *Everything loading core does is in the entry or redone.* Entries were designed for
     library files. Core loads under `loading_prelude`, and afterwards `finish_core` and
     `check_library_declares_all` tie the kernel's built-in names, native pins and registry
     to core's definitions. Those checks must still run on every start, against the replayed
     declarations. The brief should have the lane list every piece of kernel and elaborator
     state that core's elaboration sets, and show each is replayed or recomputed.
  4. *A refused or failed replay leaves nothing behind*: start again with a fresh elaborator
     and elaborate from source.
  5. *Same results.* A session with core replayed and one with core elaborated are equal:
     every declaration's flags and three hashes, the side tables, the `hash_stability`
     prelude snapshot, and the diagnostics kept from core (`library_warnings`).
- **Brief should require.** The state-equality differential test above, in the suite; the
  custom-prelude test the trust note describes (misses against standard entries, hits on its
  own); a corrupt-entry test; `docs/core.md` (§11's table row, and the trust paragraphs) and
  `check-cache-trust.md` updated in the lane; the soundness examples run by lane and review;
  a Fable review after, as the ticket says.

## 4. Recommendation on D3744

**The problem.** Every check pays about 0.55 s before it looks at a proof, which is why a
day with the library cached takes 1.4-1.8x Lean's time although the proofs themselves are
level. The plan removes three of the costs in the order scan, index, core. The third saves
the least (60-80 ms, not the 180 its ticket implies), is the only one that makes a cached run
trust more, and needs a key fix first.

**The change.** Reordered and cut:

1. **SW-4813 and SW-4812 now**, as proposed, and they can run side by side (different
   files: `driver/project.rs` and the CLI against `elab/library.rs`). Add to their briefs the
   requirements in answer 3, and to SW-4813 the sharing of one analysis between workers.
2. **Then measure again**, with the bench fixed in small ways: "sw net" as a median, user
   and system time recorded for both sides, the ratio reported as a range, a plain-binary
   "nothing to check" time (the floor every edit pays), and one default-jobs row.
3. **Profile library entry loading** (finding 5) before deciding on core. A cheaper replay
   helps every check and is what a core entry's cost would be made of.
4. **SW-4814 held**, to return as a D question for Matt after step 2: "core joins the
   trusted cache, for about 70 ms a check: yes or no?", with the M1 key fix as its first
   step if yes.
5. **SW-4650 and SW-4612** are rightly not part of this: they don't touch these days'
   times. They don't need to queue behind it either; they are separate code and are judged
   on the formatter's proofs.

**What it should do.** A library-cached day goes from 1.4-1.8x Lean's file time to about
0.8-1.0x, and the wait before any check starts drops from about 0.55 s to about 0.2 s, with
no change to what a check trusts **[estimated from the lanes' measurements and my one run]**.
SW-4814 would add about 0.07 s to that at the cost of a trust change, which is why it should
be decided on its own.

## Not done

- Lean was not rerun, and its thread use on 4.34.1 not checked: finding 3's third point is
  from memory.
- I read day 2's port in full and only the heads and tactic counts of days 18 and 15.
- I did not trace every reader of `IndexedFile::module` (SW-4812's saving depends on none of
  them running at start-up for files that load from the cache), nor every piece of state
  core's elaboration sets (SW-4814's item 3): both are for the lanes' briefs.
- No measurement of a parallel check's per-worker costs (finding 6 is from the code).
