# Checking std from a cold cache (SW-2156)

**Status:** design note, 7 November 2026, for Matt's decisions. Nothing is
built. Read only: no builds or runs went into it, so every timing here comes
from the code, the docs or the tickets, and is marked **[measured]** (by
someone, with the source), **[checked]** (I read the code, at `93a4c7862`),
**[git]** (I counted from `git log`) or **[inferred]** (my reasoning). The
decisions are D3120 and D3121, at the [end](#7-decisions-for-matt).

It builds on [check-cache-key.md](check-cache-key.md) (SW-1753: a narrower
key or a shared cache across checkouts wins 3 to 11%; D2560-D2562),
[check-cache-trust.md](check-cache-trust.md) (what a replay trusts),
[playground-editor.md](playground-editor.md) §5.2.4 (the playground's
shipped std cache) and the parallel checking measurements
(`dev/measurements/parallel-checking.md`, SW-1170). It doesn't repeat them.

## 1. In short

- **The problem.** You install or upgrade Stitchwort, open a project in VS
  Code, and wait about 27 s on Speedwell (about 120 s on Overmind) before the
  first diagnostics, because the editor checks the whole standard library
  first. Then your first proof search checks the whole library *again*, in
  another mode, for as long again. A new project, a fresh worktree after a
  checker change, and the language server's own tests all pay the same.
- **Where the time goes.** Up to three separate cold checks of all of std
  per project per build, one for each "mode" that is part of the cache key:
  the CLI's, the editor checker's and the editor search's (§2.1). One of
  them, the search's, is a pure duplicate. Inside each check, one file,
  `Float/Theory.sw`, was most of the time in the playground's measurement
  (33 to 97 s of 103 s at the playground's limits); whether it dominates at
  native limits is the first thing to measure.
- **The change I recommend, in order:**
  1. measure: per-file times in each mode, on both machines (§6, stage 1);
  2. let the editor's searches use the checker's std entries, as the
     playground's already do: one cold editor fill instead of two (stage 2);
  3. make the slowest file or two cheaper to check, if stage 1 shows a
     hotspot (stage 3);
  4. ship a prebuilt std cache with the installed binary, as the playground
     already does with `std.cache.gz` (stage 4, D3120).
- **What it should do.** For a user on an installed release: first
  diagnostics and first search replay std in about a second, as a warm
  cache does today. For a checkout build (Matt's VS Code, worktrees, tests):
  one cold std fill per build instead of two, and a shorter one if stage 3
  finds a hotspot. We'd know from stage 1's numbers repeated after each
  stage, and from the language server's cold `features` run (SW-2144's
  30 s should fall to about half after stage 2).
- **Not recommended:** loading std lazily in the editor (§4.3), and a
  parallel std check unless stage 1 shows the library's file graph has
  become much wider than SW-1170's 2.2x ceiling (§4.4, D3121).

## 2. Where the time goes

### 2.1 Up to three whole-std checks per project per build

The cache key of a library file includes the navigation mode
(`modes()`, `crates/elab/src/cache/mod.rs:300-310`, which hashes
`nav_tag()`, `:313-320`), and the unit name has it too (`cache_unit`,
`:244-252`). So entries made in one mode are never read in another
[checked]. Three modes check std:

| Who | Session | Mode (`nav_tag`) | Loads |
|---|---|---|---|
| CLI `check`, `run`, `test` | `Session` without navigation | `""` | only the files the project needs (`needed_roots`, `cache/mod.rs:574-586`) |
| Editor checker | `session_for`: `navigable_for_stack` + `enable_expression_types` (`crates/lsp/src/lib.rs:2314-2318`) | `+nav+ty` | all of std up front (`LiveProject::new_except`, `crates/driver/src/live.rs:469-475`) |
| Editor search, completion after `.` | `search_session` (`lsp/src/lib.rs:3924-3930`): natively `Session::for_stack`, then `load_libraries_for_probes` turns navigation on (`crates/driver/src/at.rs:756-762`) | `+nav` | all of std (`load_all_libraries`) |

- **The search's fill is a duplicate.** Its comment already says
  "navigation recording only adds to what a session keeps; it doesn't
  change what it elaborates" (`lsp/src/lib.rs:3921-3923`), and when the
  playground's bundle is loaded it *does* make its sessions as the checker
  does (`library_session`), so that they share entries. That was SW-1458's
  fix for the browser (17.4 s to 2.7 s for one search, memory 183 to
  229 MB in Node) [measured, SW-1458]. Natively, with no bundle, it falls
  back to a plain session, so it writes `+nav` entries nobody else reads.
- **The test helper shows it.** `cached_memory`
  (`crates/lsp/tests/it/common/mod.rs:16-47`) fills the checker's entries
  and, in a second thread, the search's (`fill_for_searches`, `:55-59`).
  SW-2144 made them run side by side: cold 55 s to 30 s [measured], so the
  two fills cost about the same, and each is a whole-std check.
- **The CLI's fill is separate but smaller.** It checks only what the
  project reaches, and a user who never runs the CLI never pays it. I leave
  it alone (§4.6).

### 2.2 What one whole-std check costs

- **Size:** 96 `.sw` files, 33,773 lines [checked]. The largest are lemma
  files: `List/Lemmas` (2,962 lines), `Parse/Runs` (2,301), `Parse/Reads`
  (1,997), `Map/Spec` (1,952), `Float/Theory` (1,832), `List/SortLemmas`
  (1,565).
- **No navigation:** about 10 s for all of std (docs/core.md:430), 9 to 10 s
  of CPU in the test std cache, against 0.6 s to replay it
  (docs/testing.md, "The test std cache"), and 14.4 s cold per test binary
  in SW-1716's profile (check-cache-key.md §1) [measured, under load].
- **Editor mode:** about 27 s release on Speedwell, about 120 s on Overmind
  (SW-2144) [measured, under load, two fills at once].
- **The hotspot:** at the playground's limits (a 256 KiB guard),
  `Float/Theory.sw` alone was 33 to 97 s of the library's 103 s, natively
  (playground-editor.md §5.2.4) [measured, load 30-60]. SW-985 (backlog)
  has `cases` splits in `Float.Theory` taking about 100 s or 1.2 GB before
  giving up, and SW-1456 a recursion-depth failure in
  `Float.Theory.roundMagnitudeSpec` at those limits. At the CLI's 64 MiB
  stack (`crates/cli/src/main.rs:509`) the file may be much cheaper; nobody
  has measured it per file at native editor limits.
- **Why the editor mode is 2-3x the CLI's** [inferred, low confidence]:
  either recording expression types costs that much (every subterm's type
  is kept for hovers), or the 27 s is the two fills contending on a loaded
  machine, or `Float/Theory` is cheap at 64 MiB and expensive at the
  editor's stack. Stage 1 tells these apart.
- **Why Overmind is 4.4x Speedwell for std** but about 2x for the whole AoC
  check [inferred]: two whole-std fills at once on 4 real cores and a
  smaller cache, during a merge-tier run at load 10.6 on 8 threads
  (SW-2144's ticket). Stage 1 measures it alone.
- **Proof search entries do double it** for the editor: the second fill is
  a whole-std check of the same size (§2.1). For the language server tests
  the doubling is hidden by running the two fills at once, which costs CPU
  and memory but not wall time; for a user it is a second wait at their
  first search, since the two happen at different times.

### 2.3 How often it happens

In the week to `93a4c7862` [git]: of 2,207 first-parent commits on `main`
(merges counted by their diff against the first parent), 267 changed
`FINGERPRINT`'s inputs, so left every std entry cold: 242 in the checker's
crates or `Cargo.lock`, 25 in the driver only. That agrees with
check-cache-key.md's 91% / 7%. Another 99 touched std's `.sw` files; one
that adds or removes a name misses every std entry too, because every key
has the library's index of names (`library_interface`,
`cache/mod.rs:543-569`; docs/core.md:430). So on `main` std goes cold
roughly 40 times a day, and each time the editor, the CLI and each test
stack size pay their own fill.

## 3. Who pays it, and when

| Who | When | What they wait | Today |
|---|---|---|---|
| A user, installed release | First editor session per project after install or upgrade | First diagnostics, then first search | ~27 s, then ~27 s again [measured, Speedwell] |
| A user with several projects | Each project's first session | The same, again | The cache is per project: `.stitchwort/cache` (`crates/lsp/src/source.rs:128-135`, `check_cache.rs:1-3`) |
| Matt in VS Code on a checkout build | After every rebuild that changes the checker (~40 a day on `main`) | As above | As above |
| Lanes, worktrees, scratch clones | `task worktree:new` copies `aoc/.stitchwort` and `games/rogue/.stitchwort` (`Taskfile.yml`, `worktree:new`), so they are warm until the lane changes checker Rust; `target/test-std-cache` is per checkout and starts empty | The first test binary that loads std; the first AoC check | 14 s per stack size per run, once (SW-1741) |
| The flake's gates (`nix flake check`, the daily tier) | Every run: the sandbox has no cache | Same as lanes | By design: the gates check from source (check-cache.md, "The gates still run the kernel") |
| GitHub CI | Only `playground.yml`, which builds the playground's `std.cache.gz` | About 40 s (playground-editor.md §5.2.4) | Already a prebuilt cache |
| Overmind | Every soak run's first fill | ~4x Speedwell | ~120 s per editor fill [measured] |

The user rows are the ones that matter most: they are the first impression,
and nothing in the dev loop helps them. The dev rows are paid often, but
mostly in the background, and check-cache-key.md already found that
narrowing the key or sharing caches across checkouts saves little there.

## 4. The options

### 4.1 The search uses the checker's std entries

- **The change.** `search_session` natively makes its session as the
  checker does (`session_for`, or `library_session` with no bundle), so its
  std units are `+nav+ty` and replay the checker's entries. The test helper
  then needs one fill, not two.
- **Cost:** small, one function and the test helper. Memory: a search
  session records expression types too (SW-1458 measured +46 MB in Node).
- **Risk:** low. It is the change the playground already runs, reviewed in
  SW-1458 ("navigation recording only adds data, and searched proofs are
  pasted into the source and re-checked"). A search started before the
  checker's fill has finished still fills itself; that is today's
  behaviour, not a regression.
- **Trust:** unchanged: the same entries, the same directory, the same
  salt.
- **Benefit:** halves the editor's cold cost on every host, dev and user.
  Absorbs the measurable half of SW-2120.

### 4.2 A prebuilt std cache shipped with the binary

- **The change.** The flake's `installRuntime` (`flake.nix:157-166`) already
  copies std to `$out/share/stitchwort/std`. After the build it would also
  run the installed binary once to write `$out/share/stitchwort/std.cache`:
  a `LibraryBundle` (`crates/driver/src/check_cache.rs:191-287`) holding
  the editor's entries (`stitchwort_lsp::library_bundle`, `lsp/src/lib.rs:2344`,
  which already makes exactly this for the playground and fails if the
  library doesn't replay from it) and the CLI's. The CLI and the language
  server read it through a layered store: the project's directory first,
  then the bundle, writing only to the directory. A key the bundle doesn't
  have (another stack, `--std-dir`, an edited std) is a miss and is checked
  as today.
- **Cost:** medium. A host-side layered `Store`, a CLI subcommand (or
  `doc`-style internal command) to write the bundle, the flake step. Build
  time: one more whole-std check per mode in the Nix build, roughly 30-60 s
  on Speedwell [inferred from §2.2]. Size: the playground's is about 14 MB
  unpacked (SW-1458); two modes, gzipped, perhaps 5-10 MB [inferred].
- **Risk:** low to medium. The parts exist and are tested
  (`a_library_bundle_reads_back_and_only_in_its_own_build`); the new parts
  are the layering and keeping the bundle's limits equal to the hosts'
  (stack sizes are in the key: a mismatch is a silent all-miss, so the
  build step must fail on it, as `library_bundle` already does).
- **Trust.** A loaded entry is trusted (D1660), so the question is whose
  entries we trust. Today natively it is only the cache directory's own
  (the salt, check-cache.md §3.1: "never read caches you didn't write").
  The bundle would be the second exception after the playground's, and the
  argument is the same (`check_cache.rs:206-210`): it is made by the same
  build that reads it, which `LibraryBundle::decode` checks before reading
  anything (the compiler string has the version and `FINGERPRINT`). It sits
  in the same read-only store path as the binary and std's text; anyone
  who can change it can already change those. The pins still guard the
  natives: replay binds every pinned built-in through `bind_builtin_def`,
  which checks its content hash (`cache/mod.rs:2852,2867`;
  `crates/elab/src/lib.rs:3035`, SW-2081), so a bundle can't attach a
  native to a different definition. What it does add to the trusted base:
  that the Nix build ran the check honestly, and that a check in the build
  sandbox gives what a check on the user's machine would (D2680's
  invariant: an environment may change only whether a check runs out, not
  what it accepts; `left_out` covers files that run out).
- **Benefit:** users only, which is where it matters most. Nothing for
  checkout builds: `cargo build` runs no `postInstall`, and making `task
  build` write it would only move the same fill earlier.
- **Elsewhere:** Lean's toolchain releases ship the compiled `.olean` files
  of `Init`, `Std` and `Lean`, trusted on import, and Mathlib users fetch
  prebuilt ones (`lake exe cache get`); GHC ships `base`'s interface files.
  rust-analyzer ships nothing and indexes the sysroot on each start, which
  is why its first minute is slow.

### 4.3 Checking std lazily, per file, on first use

- **The change.** The CLI already does this (`needed_roots`). The editor
  would do it too: load only what the project's namespaces need before the
  first mark, then the rest in the background.
- **Cost:** medium to large. `LiveProject` loads everything before its base
  mark on purpose: a file loaded later is unloaded by every rewind and
  loaded again on the next re-check, which made re-checking 2025 day 1 take
  140 ms instead of 30 (`live.rs:469-474`). A background load would need a
  new base mark after it, and every search still needs all of std.
- **Risk:** medium; the rewind invariants are subtle (elaborator-state.md).
- **Benefit:** small for real projects: the playground note found the AoC
  days use most of the library (§5.2.4), so the first check would still
  wait for most of it. Only toy projects gain.
- **Recommendation:** no.

### 4.4 Checking std files in parallel

- **The change.** A few threads, each with its own `Session`, check the std
  files in dependency order (`LibraryIndex::files[..].edges`) into the
  shared cache directory, each replaying the files it needs from there;
  then the real session replays the lot. Separate sessions on separate
  threads already work (the test helper runs two), so this needs no `Rc` to
  `Arc` change.
- **Cost:** medium: a scheduler over the index, and care with memory.
- **Risk:** medium: N sessions' memory at once (a worker was 130-190 MB
  after replay in SW-1170; the language server tests run under a 4 GB
  cap), and a CPU burst in the editor exactly when the user starts typing.
- **Benefit:** at most **2.2x** for std alone, a deep chain of files
  (SW-1170, measured on an older std) [measured]; less after the replay
  overhead per worker. Parallel checking is deprioritised (D2299).
- **Trust:** unchanged (own directory, own salt). It doesn't help the
  gates, which must check from source in one session.
- **Recommendation:** only if stage 1's recomputed ceiling is well above
  2.2x: D3121.

### 4.5 Making the check itself cheaper

- **The change.** Depends on stage 1. If `Float/Theory.sw` (or another
  file) dominates, look at why: `cases` splits (SW-985), deep evaluation
  (SW-1456), or hidden arguments solved to unfolded normal forms, which
  were 44% of the library's core term nodes (proof-check-speed.md,
  cause 1). Fixes range from rewriting a few proofs to an elaborator
  change.
- **Cost:** unknown until measured. A proof rewrite is small; an
  elaborator change is not.
- **Risk:** a changed elaborated term changes content hashes
  (`snap:hashes`, `hash_stability`) and could unbind a pinned native
  (SW-2081 makes that fail loudly at binding, so it can't go unnoticed).
  Any evaluator change must keep glued and unglued evaluation agreeing on
  what's equal (D3030).
- **Benefit:** the only option that helps everyone: users, checkout
  builds, the gates' from-source checks, Overmind, the playground's build.
- **Trust:** unchanged.

### 4.6 Covered elsewhere, or rejected

- **A narrower key, or one cache shared across checkouts:** 3-4% and 11% of
  fills (check-cache-key.md, D2560-D2562). My recount (§2.3) agrees.
- **One mode for all std entries** (the CLI replaying the editor's
  `+nav+ty` entries, or the key accepting entries made with more
  navigation): saves the CLI's partial fill when someone uses both. It
  changes the key's meaning, and SW-1458 chose to keep `nav_tag` exact.
  Not worth it beside §4.1.
- **A per-user std cache** (`~/.cache/stitchwort`) shared by a user's
  projects: std entries don't depend on the project, so a second project
  would start warm. Trust is unchanged (the user's own directory and
  salt). Smaller than §4.2 for users and needless once it exists; worth
  reconsidering only if D3120 is no.

### 4.7 Compared

| Option | Who it helps | Saves (editor, cold) | Cost | Risk | Trust |
|---|---|---|---|---|---|
| 4.1 search shares entries | everyone using the editor | the second fill: ~50% | small | low | unchanged |
| 4.2 shipped bundle | installed users | all of it, on their first session | medium | low-medium | extends to "the build that made me" (D3120) |
| 4.3 lazy in the editor | toy projects | little | medium-large | medium | unchanged |
| 4.4 parallel | everyone with a cache | ≤ 2.2x of one fill | medium | medium (memory) | unchanged |
| 4.5 cheaper check | everyone, gates too | unknown until stage 1 | unknown | hashes, pins, D3030 | unchanged |

## 5. Calls I made

- The search sharing the checker's entries (§4.1) is the editor's first
  fix: reversible, already the playground's design, no new trust.
- Lazy loading in the editor is out (§4.3).
- The CLI keeps its own mode (§4.6).
- The shipped bundle holds the editor's and the CLI's modes only, for the
  stacks the installed binary uses; anything else misses and checks.
- Narrowing the key is not reopened (D2560-D2562 stand).

## 6. Measurements for stage 1

All on a release build, from source, with no other lane building, on
Speedwell and again on Overmind; record `uptime` with each, CPU time
(user+sys) as well as wall, and peak RSS (`/usr/bin/time -l` on macOS;
Overmind has no `/usr/bin/time`, use `command time` from Nix's `time`).

1. **Per-file times in each mode.** A small driver example (beside
   `crates/driver/examples/ns_graph.rs`) that makes a session in each of the
   three modes of §2.1, with the editor's and the CLI's stack sizes, loads
   every library file with no cache, and prints
   `stitchwort_elab::timings::report()` (run with `STITCHWORT_TIMINGS=1`).
   Gives: the total per mode, the top ten files, and the slowest
   declarations; answers whether expression types or the stack make the
   editor mode dearer, and whether `Float/Theory` dominates natively.
2. **Each mode alone**, then two at once, to separate contention from cost
   (the SW-2144 numbers were two at once under load).
3. **The std graph's critical path today**: `cargo run --release -p
   stitchwort-driver --example ns_graph -- --std` and
   `dev/parallel-check/model.py` with item 1's times, as SW-1170 did. A
   ceiling still near 2.2x closes §4.4.
4. **The real server, cold** (SW-2120): a copy of `aoc/` with no
   `.stitchwort/cache`, the release `stitchwort lsp` driven by the
   `features` test's messages: time to first diagnostics, then time of the
   first search (`search_at`-style request) and of the first `.`
   completion. Warm, for comparison.
5. **The bundle's size and build time**, for §4.2: the bytes and seconds
   `library_bundle` takes natively with the editor's options, gzipped and
   not.

## 7. Decisions for Matt

- **D3120: ship a prebuilt standard library cache with installed binaries
  (built by the flake, read before the project's cache), trusted like the
  playground's `std.cache` because the build that reads it made it? [rec:
  yes, because it removes the whole first-session wait for users, reuses
  the playground's tested bundle, and adds to the trusted base only the
  build itself, which already produced the binary and std's text it sits
  beside]**
- **D3121: if stage 1 shows std's own critical path allows well over 2.2x,
  build a parallel std fill (threads, one session each) despite D2299?
  [rec: no for now, because SW-1170 measured 2.2x for std alone, the
  workers' memory competes with the editor, and stages 2-4 remove most of
  the wait without it; revisit with stage 1's number]**

## 8. Tickets to file

In order; stages 2 and 3 can run side by side once stage 1 is in (they touch
different code); stage 4 waits for D3120.

1. **Measure the cold std check per file, per mode** (§6). Sonnet, 60 min.
   Absorbs SW-2120. Adds one driver example; tests: builds the example, and
   `task test:one -- fingerprint` only if it touches the driver's sources
   beyond `examples/` (it shouldn't). Writes its numbers into this note's
   §2.2 as "As measured".
2. **Editor searches replay the checker's std entries** (§4.1). Sonnet,
   40 min. `search_session` makes its session with `session_for` natively;
   `cached_memory`'s second fill goes. Tests: `task test:one --` the lsp
   `features` search and completion tests and the `memory` tests, cold
   (`rm -rf target/test-std-cache/*/lsp` first) and warm, with the cold time
   recorded against SW-2144's 30 s.
3. **Cheaper check of the slowest std file(s)**, from stage 1's table.
   Sonnet if it is proof rewriting in std, Opus if the cause is in the
   elaborator (hidden arguments, `cases`, evaluation depth: core language,
   D2506). 60-90 min. Tests: `hash_stability` `prelude`, `task snap:hashes`
   with `NAME=` on the file, `pinned_hashes`, the `std_library` test for the
   file; may absorb SW-985.
4. **Ship a std cache with the installed binary** (§4.2), if D3120 is yes.
   Sonnet, 90 min (near the trust boundary, several crates: driver store,
   CLI command, lsp, flake). Tests: `check_cache`'s bundle test plus a new
   one (a layered store reads the bundle, writes only the directory, and a
   bundle from another build is never read), `task test:one -- lsp` bundle
   tests, and a background `nix build .#stitchwort` checking the bundle
   replays every file (`library_bundle` already fails otherwise).
5. *(Only if D3121 is yes.)* Parallel std fill. Sonnet, 90 min.

## 9. What this note doesn't cover

- The playground (already has its bundle) and the test std cache's fill
  scheduling (SW-1741, SW-2144).
- Project namespaces' cold cost (SW-1195, SW-1237): this note is std only.
- Why a std edit that adds a name re-checks all of std (`library_interface`):
  a narrower interface hash is possible but is a trust question of its own
  (a new name can make a short name ambiguous elsewhere).
