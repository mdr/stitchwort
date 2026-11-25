# Where a cached check's floor goes (SW-4819, SW-4826)

**Status:** Opus lane SW-4819 (with SW-4826), 25 November 2026, 15:06-15:35, on `lane/SW-4819`
at `76522d598` (after SW-4812's std index cache, SW-4813's project scan cache and SW-4820's
skipped fill). Measurement only: no Rust changed. Raw summaries and the script are in
[`SW-4819/`](SW-4819/). It follows [SW-4809](SW-4809-small-proof-profile.md),
[SW-4816](SW-4816-checking-profile-review.md) and the rerun at the end of
[SW-4608](SW-4608-proof-checking-speed.md).

Marks: **[measured]** timed or counted today; **[estimated]** my judgement from the
measurements; **[read]** from the code, not timed.

## In plain words

**The floor** is a `check` of a day's namespaces with every cache warm and nothing to do: what
any check costs after an edit elsewhere. It is 190 ms on 2024 day 2 and 2020 day 18, and
390 ms on 2021 day 15 **[measured]**.

**Day 15's extra 200 ms is one doc link.** `aoc/src/Aoc/Common/Proofs/PrefixSums.sw` line 2
has a doc link, ``([`PrefixSums.blockSum`])``. A namespace whose files have doc links can't be
reported from its cache entry alone, because `W-DOC-LINK` warnings aren't cached (SW-1045)
and are worked out again against the loaded names. So `plan_skips` loads `Aoc.Common.Proofs`,
which loads everything it uses: `Aoc.Common` and 56 library files, 6,491 declarations, all
replayed from the cache. With that one link turned into plain code text the floor fell from
390 ms to 210 ms, and the run loaded no library at all **[measured]**. Nothing in the size of
`Aoc.Common` or the project scales; it is all-or-nothing on that link. 23 AoC days import
`Aoc.Common.Proofs` and pay it; `tools/fmt` has 16 files with doc links, so its floors likely
pay the same **[read; fmt not timed]**.

**The 190 ms every floor pays** is, by stage (profile of day 2, ms per run under the
profiler, which adds about 20%): starting the session, **128**, of which the core prelude
elaborated and kernel-checked again 102, its statement-style sweep 9, its parse 6 and the
std index from its cache 7; reading the project's 633 files, **39**, and the library's 133,
**14**, two thirds of it in `open`; the project scan from its cache, **40**, half of it
recomputing the namespaces' edges; planning the cached namespaces, **7**; the rest, **6**.
Day 18 is the same to within noise.

**What I'd do, ranked by what it saves on the floor:**

1. **Work out doc-link warnings without loading the namespace** (about 180 ms on day 15 and
   every day that reaches a doc link; nothing elsewhere) **[measured]**. Not a trust question:
   warnings only.
2. **Load core from the cache** (SW-4814, held): about 60-80 ms of the 98 ms core costs
   **[SW-4816's estimate; consistent with today's 98 ms]**. **Trust question** (already with
   Matt).
3. **Read the project's and the library's files on several threads**: about 25-35 ms of
   45 ms **[estimated]**. No trust change.
4. **Cheaper project edges**: about 20 ms of the scan's 33 ms **[estimated]**. Beside the
   trust boundary (the edges feed cache keys, SW-4816 finding 7); keyed on content as now.
5. **Skip the core's statement-style sweep** unless library warnings are asked for: about
   7 ms **[measured 9 ms under the profiler]**. No trust change.

With 1, 3, 4 and 5, a floor would be about 120-130 ms on all three days; with 2 as well,
about 50-70 ms **[estimated]**.

**And when library entries do load** (day 15's floor today, and any check after an edit to a
day: the 73-170 ms of SW-4816 finding 5), 160 ms under the profiler for 56 files and 5,300
declarations goes to: admitting the replayed declarations 79 (of which recomputing Prop marks
21, `references` 25), decoding 42, **recomputing library keys 20**, reading the entries 14
**[measured]**. The library keys are recomputed for each file over its whole closure
(quadratic, **[read]**); memoising them saves about 18 ms with no change to any key. The
smaller fixes are in section 4.

## 1. Method

- **Machine:** Speedwell, M1 Pro, 10 cores. **Load:** 5.6 (1-minute) / 5.5 (5-minute) at
  the start; it jumped to 17.8 / 11.5 at 15:11 (other work), and I waited until the 5-minute
  average was under 8 before profiling: **5.30 / 7.94 at the start of the profiles, 4.22 /
  7.52 at their end** ([`loads.txt`](SW-4819/loads.txt)). The plain timings and the doc-link
  experiment ran at a 5-minute load of 5.2-5.5.
- **Binaries:** the worktree's `target/release/stitchwort` (plain, no dev features) for the
  timings; for the profiles the same build with symbols,
  `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only cargo build --release -p stitchwort-cli
  --target-dir target/prof`. Both give the same floors (0.19, 0.39 and 0.19 s).
- **Warming:** from `aoc/`, `STITCHWORT_JOBS=2 check` of each day's namespaces, then the floor
  is `STITCHWORT_JOBS=1 check <namespaces>`: `Aoc.Year2024.Day02 Aoc.Year2024.Day02.Proofs`,
  `Aoc.Year2021.Day15 Aoc.Year2021.Day15.Proofs`, `Aoc.Year2020.Day18
  Aoc.Year2020.Day18.Proofs` (their `Spec` and `Aoc.Common` namespaces come with them). The
  bench's day 15 also names `Aoc.Common.Proofs`, which is already in the closure: same floor,
  0.38-0.40 s **[measured]**.
- **Timings:** `--timings=all`, one run each ([`units-*.txt`](SW-4819/)); wall times with
  `/usr/bin/time`, 3 runs each.
- **Profiles:** `samply record --save-only --unstable-presymbolicate -r 4000` (samply 0.13.1,
  nixpkgs), 5 runs of each floor, summed by [`prof.py`](SW-4819/prof.py) (all threads, idle
  waits dropped: the main thread waiting on the big-stack thread, and the signal thread).
  Summaries: [`profile-d02.txt`](SW-4819/profile-d02.txt),
  [`profile-d15.txt`](SW-4819/profile-d15.txt), [`profile-d18.txt`](SW-4819/profile-d18.txt),
  [`library-load-d15.txt`](SW-4819/library-load-d15.txt),
  [`self-file-reads-d02.txt`](SW-4819/self-file-reads-d02.txt). One sample is 0.25 ms. The
  profiles themselves aren't kept. Under the profiler a 190 ms floor takes about 230 ms, so
  profiled stages are about 20% above wall time; the tables say which they are.
- **The doc-link experiment:** I replaced ``[`PrefixSums.blockSum`]`` with
  `` `PrefixSums.blockSum` `` in `PrefixSums.sw`, warmed day 15 again, timed its floor 3
  times and took its `--timings=all`, then restored the file with `git checkout`, warmed again
  and saw the floor back at 0.39-0.40 s.

## 2. The floor by stage

Profiled, ms per run (mean of 5), and the `--timings` view of the same runs:

| stage | day 2 | day 18 | day 15 | where |
|---|---:|---:|---:|---|
| read the library's 133 files (`load_std_text`) | 14 | 12 | 11 | before the session; 7 of it `open` |
| std name index from its cache (`LibraryIndex::standard`: hash the texts, decode) | 7 | 8 | 7 | |
| core prelude: parse (`IndexedFile::module`) | 6 | 7 | 7 | the index caches names, not the module |
| core prelude: elaborate and kernel-check 585 declarations | 102 | 101 | 100 | `--timings`: 69-77 elab + 19-21 kernel |
| core prelude: statement-style sweep (`binder_sweep`) | 9 | 9 | 9 | every run |
| core prelude: the rest (`install_library` etc.) | 3 | 2 | 2 | |
| read the project's 633 files (`project_sources` › `walk`) | 39 | 32 | 32 | 24 of it `open`, 7 `read` (day 2) |
| project scan from the sketch cache (`Scan::new`, `analyse_scan`, `prepare_analysis`) | 40 | 40 | 40 | of it `namespace_edges_of` 22 |
| plan the cached namespaces (`plan_namespace`: entry heads; day 15 also parses two namespaces' modules) | 7 | 11 | 19 | |
| **load the doc-linked namespaces and their closure** | - | - | **196** | section 3 |
| other (clap, config, report, exit) | 6 | 2 | 5 | |
| **total under the profiler** | **233** | **224** | **427** | |
| **wall, `/usr/bin/time`, 3 runs** | **190-200** | **190** | **380-400** | |
| `--timings`: core (elab + kernel) | 98 | 96 | 92 | |
| `--timings`: outside the units | 91 | 94 | 128 | |

All **[measured]**.

What the stages are, briefly **[read]**:

- **File reads.** `walk` reads every `.sw` file of the project: the scan cache (SW-4813) is
  keyed on each file's text hash, so every file is read whatever is asked. `open` is about
  40 µs a file on this machine; reading is the smaller part. The library's texts are read
  once (`load_std_text`) and hashed for the index key and the library keys.
- **Project edges.** With every sketch from the cache, `analyse_units` still recomputes each
  namespace's edges from the sketches (`namespace_edges_of`), with `format!`-built strings and
  copying: 22 ms, of which formatting and allocation are most.
- **Core.** The same as SW-4809 and SW-4816 found: about 98 ms by the timers, every run. Its
  statement-style sweep (`binder_sweep::sweep_module` over the prelude) is another 9 ms whose
  results are kept only as library warnings (`library_warnings`), which a plain check doesn't
  print.

## 3. Day 15's extra 200 ms (SW-4826)

**The cause [measured, read].** `Session::plan_skips` (`crates/driver/src/project.rs:461`)
leaves a cached namespace out (reports its warnings from the entry, loads nothing) only if its
modules have no doc links:

```rust
Some(warnings)
    if certain && ns.modules().iter().all(|m| m.doc_links.is_empty()) =>
```

`Aoc.Common.Proofs` has one, in `Common/Proofs/PrefixSums.sw` line 2. So it is "loaded", and
`closure(analysis, &loaded)` loads everything it uses. `Aoc.Year2021.Day15.Proofs` imports
`Aoc.Common.Proofs` (`Levels.sw` line 11), so day 15's floor replays:

| what | entries | declarations | nodes | `--timings` ms (elab + kernel) |
|---|---:|---:|---:|---:|
| library files (`std/…`) | 56 | 5,300 | 920,907 | 85.7 + 45.1 |
| `Aoc.Common` | 1 | 709 | 39,771 | 34.8 + 2.6 |
| `Aoc.Common.Proofs` | 1 | 482 | 114,153 | 15.8 + 5.2 |

The 56 library files are 1.6 MB of source. Days 2 and 18 import no project namespace with a
doc link, so their floors replay nothing (their unit tables have only core).

**The profile of that part (day 15, ms per run under the profiler) [measured]:**

| part | ms |
|---|---:|
| `load_libraries` (the 56 library files) | **160** |
| … admit the replayed declarations (`admit_replayed`) | 79 |
| … … `admit_trusted_def` (of which `prop_mark` 21) | 28 |
| … … `references` (a pointer set over each term's DAG; 20 of it hashing) | 25 |
| … … `admit_trusted_group` (of which `admissible` 10.5, `case_only_in_tree` 8) | 20 |
| … decode (`read_nodes` 31, `interface_hash` 3) | 42 |
| … library keys (`library_keys`: blake3 over texts) | 20 |
| … read the entries (`cache_read` 11, `cache::open` 3) | 14 |
| … other (scope retain, tables) | 5 |
| the two project namespaces: admit 14, decode 7, `library_unchanged` 3, other 2 | 27 |
| their statement style (`binder_sweep` over their files) | 8 |
| parsing their modules for it (`OnceLock<Module>`) | 7 |
| planning: more namespaces' heads | 6 |
| **total** | **~210** |

Decode against admit: 49 ms decoding against 93 ms admitting, both counted over library and
project entries; hashing (blake3 for keys, pointer-set hashing in `references`) is about
42 ms of the 210.

**The library keys are recomputed per file [read].** Before each library file loads,
`cache_lookup(f)` calls `library_key(f)`, which is `library_keys(&{f})`: a fresh map, hashing
`f`'s text and, recursively, the text of every file `f` reaches
(`crates/elab/src/cache/mod.rs:754-792`). So each file's text is hashed once for every file
that reaches it. 1.6 MB hashed once is about 1-2 ms; 20 ms is the repetition.

**With the link removed [measured]:** floor 0.21-0.22 s (3 runs), `--timings` wall 204 ms,
unit table core only, outside the units 111 ms. The remaining 15-20 ms over day 2 is planning
five namespaces' heads instead of three and the larger `Aoc.Common` closure's analysis.

## 4. Fixes, ranked by what they save

Savings are per floor, in wall ms **[estimated]** unless marked. "Trust" says whether the fix
changes what a cached run rests on without the kernel's check; those are Matt's questions.

| # | fix (end state) | saves | applies to | trust |
|---|---|---:|---|---|
| 1 | **Doc-link warnings without loading.** Resolve a skipped namespace's links against names known without loading it: the std index's names and the project analysis's declared names (`FileSketch::names`, imports from the sketches), as `doc` and the index already resolve links from syntax (`link_candidates_with_imports`). Then `plan_skips` no longer needs `doc_links.is_empty()`. Needs a test that the name-only resolver gives the same warnings as the loaded one on every link of std, `aoc/` and `tools/fmt`. | **180 [measured]** | day 15, 23 days that import `Aoc.Common.Proofs`, likely `tools/fmt` | none: warnings only |
| 2 | **Core from the cache** (SW-4814). Also removes core's parse (6) and could carry the statement-style sweep. | 60-80 (SW-4816) | every run | **yes**: core joins the trusted cache; needs the M1 key fix first (SW-4816 finding 2) |
| 3 | **Read files on several threads** (project and library), the order of the result unchanged. `open` dominates, and on macOS it overlaps across threads. | 25-35 of 45 | every run | none |
| 4 | **Cheaper project edges**: compute edges without `format!`-built strings (interned names, or keep each sketch's resolved edges in its cache entry), or cache the whole analysis keyed by the hash of all the files' hashes. | ~20 of 33 | every run on a project | beside it: edges feed cache keys (SW-4816 finding 7); stay keyed on content |
| 5 | **Core's statement-style sweep only when library warnings are reported** (it fills `library_warnings`, which a plain check doesn't show), or with core in the cache. | ~7 | every run | none |
| 6 | **Memoise library keys** for the session (one map, filled once, as `library_interface` is "computed once"). Same keys. | **~18 [measured 20 under the profiler]** | every run that loads library entries | none: the keys are the same |
| 7 | **References from the decoder**: record each decoded term's `Def`/`Data` nodes while reading the node table instead of walking the DAG with a pointer set. | ~20 | runs that load entries | none in itself: it orders replay; the kernel's admit must still refuse a reference to a declaration not yet admitted **[read: worth a test]** |
| 8 | **Store Prop marks (and `admissible` results) in the entry** instead of recomputing them on trusted admission. | ~25 | runs that load entries | **yes**: the kernel would take marks from the entry; today it derives them from the (trusted) types |
| 9 | **Faster decode** (`read_nodes`): fewer allocations per node, the node table read in one pass. | ~10-15 | runs that load entries | none if the format's checks stay |
| 10 | **Fewer entry files**: one read per closure, or memory-mapped entries. | ~5-8 | runs that load entries | none, if each entry keeps its own stamp and hash |

Fixes 6-10 together take a 56-file library load from about 130 ms wall to about 60-70 ms
**[estimated]**; that is SW-4816 finding 5's cost on every check after an edit to a day.

## 5. Not done

- No timing of `tools/fmt`'s floor; the doc-link cost there is inferred from its 16 files with
  links.
- No hyperfine; the floors are `/usr/bin/time` runs (3 each) and agree with SW-4818's
  hyperfine medians (187, 193, 406 ms).
- No default-jobs floor: SW-4818 found it equal to one job's.
- The dev build (`validate_marks`) wasn't profiled; this is the plain binary people run.
