# Where loading a project from the check cache spends its time (SW-1199, D2302)

The question (D2302): commands that need the whole project loaded (`test`,
`audit`, `check --index`, `search`, the language server opening aoc) replay
every namespace from the check cache. Where does that time go, and are there
clear, obvious optimisations?

Measured on 4 Nov 2026, 10:50-11:25 GMT, release build of `main` at
2715abfb, on a copy of `aoc/` (207 namespaces) with a warm cache, and
`games/rogue`. The machine was very busy: load average 20 at the start, then
120-155 throughout (`uptime` at the end of the timed runs: 153.86, 129.99,
105.10). So **CPU time (user+sys) is the number to use; wall time is 4-5x
CPU and only noise**. Even CPU time is inflated somewhat under that load
(the Apple cores share caches, and work lands on efficiency cores), so treat
the absolute figures as ±20%; the shares are steadier.

## Summary: the clear optimisations, best saving per effort first

1. **Don't evaluate a replayed declaration's type when it is admitted.**
   - *Problem.* Admitting a cached definition (`admit_trusted_def` →
     `push_def`) still evaluates its type to `Def::ty_value` straight away.
     That is **47-55% of `test` and `check --index`** (1.8 s of 3.3-3.9 s
     CPU) and 38% of `audit` and `search` (about 1.4-1.8 s). Almost all of
     it is a handful of theorems whose *types* run a computation:
     `Aoc.Year2024.Day22.Proofs.digitChangesPossible` (type
     `HoldsDigitChanges (sequencesOf possibleChanges)`, which builds every
     change sequence) is 76% of the slow admissions. Eight
     `Aoc.Year2021.Day0x/Day17.Tests.examplePartN` theorems
     (`solvePart2 exampleGame = Some 1924 := rfl`) take another 20%:
     admitting the type works out the puzzle answer. Stage 3 saw the
     Day22 one (946 ms then) and left it as out of scope.
   - *Change.* Make `ty_value` lazy: evaluate it the first time something
     asks for it, not at admission. Nothing in `test`, `check --index` or
     the language server's warm-up asks for these theorems' type values.
     `search` and `audit` would still force some (`audit.rs:275` forces
     every theorem's type), so they gain less.
   - *Saving.* About 1.5-1.8 s on every whole-project load of aoc: `test`
     3.3 s → about 1.5 s, `check --index` (and so VS Code opening aoc)
     3.9 s → about 2.1 s. Estimated from two independent measurements
     that agree: the sampled profile (push_def's share × the measured CPU)
     and `STITCHWORT_TIMINGS` (kernel time 1.78 s of a 3.55 s run).
     Not measured with a prototype.
   - *Size and risk.* Medium, and in the core: `Def::ty_value` has about
     100 uses (it becomes something like `g.ty_value(id)` with a
     `OnceCell`), and an evaluation error or budget stop then happens at
     the first use instead of at admission. It touches the same core and
     `Globals` code SW-1188 (Globals split 8c) is editing, so it waits for
     it, and it wants a short design note and Opus review (it changes
     when the kernel evaluates). A narrower variant, lazy only for
     replayed declarations (`admit_trusted_def`), keeps the checking path
     unchanged.
   - *Stopgap, aoc only, minutes.* Restating `digitChangesPossible` so its
     type doesn't compute (over an opaque `possibleSequences`, say) would
     save about 1.4 s on every aoc load today. It treats one symptom, and
     the next such theorem has the same problem.

2. **Memoise the axiom walk in `audit`.**
   - *Problem.* `audit` (`audit --no-search`, 4.7 s CPU) spends **35%,
     about 1.6 s**, in `driver::axioms::axioms`, which walks each
     theorem's whole dependency closure from scratch, so shared lemmas
     and the library are walked again for each of the project's theorems.
   - *Change.* Walk each declaration's terms once per audit: a memo table
     of per-declaration results (or the direct references of each
     declaration, then a cheap reachability per root) shared by all the
     theorems in one `audit`.
   - *Saving.* About 1.5 s of `audit`'s 4.7 s (estimated from the profile);
     `task audit` and `audit:touched` gain the same share of their load.
   - *Size and risk.* Small (30-60 lines in `crates/driver/src/axioms.rs`
     and its caller), low risk: the output must be identical, which a test
     over a fixture can show. Runs beside SW-1188 without conflict.

3. **Stop redoing work in `decode` for each namespace** (two small fixes).
   - *Problem.* (a) `Elaborator::decode` builds a path → `DefId` map over
     *every* declaration in the environment, again for each of the 207
     namespaces (quadratic): 3-4%, **about 0.13 s**. (b) It recomputes the
     content hash of each dependency the first time it is named
     (`def_hash`, blake3 over the term): 3-4%, **about 0.13 s**, although
     the entry that admitted the dependency was written knowing it.
   - *Change.* (a) Keep the map in the session, extended as declarations
     are admitted (or built once per load). (b) Store each entry's own
     declarations' hashes in the entry and seed `g.hashes` on admission
     (a cache format bump).
   - *Saving.* About 0.25 s together (7%) on each whole-project load.
   - *Size and risk.* (a) small, low risk, no format change; (b) small to
     medium, low risk (a wrong stored hash makes a dependent miss, not
     pass, provided the seal covers it). `crates/elab/src/cache/mod.rs`.

Smaller ones, each about 0.1 s, listed under §4. **Not worth doing now**:
a cheaper encoding or lazy bodies (reading the 46 MB a whole load needs
costs about 0.06 s of system time, and decoding the terms about 0.25 s;
lazy bodies would save part of the latter at a large cost), and parallel
replay (SW-1170).

## 1. Per command: total CPU and where it goes

Medians of 3 runs (`measure.py`, raw output in
`dev/cache-load-profile/results-2026-11-04.log`); the split is each phase's
share in a sampled profile (samply, one run each) times the measured median.
The profiles' own CPU totals were higher than the timed runs' (samply's
overhead and the load), so only their shares are used.

| aoc, warm | CPU | floor (core, library index) | parse project | read files | decode | admit: type evaluation | admit: rest | side tables | library files (`load_needs`) | command's own work |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| one-line file (the floor) | 0.22 s | 0.21 | 0.01 | – | – | – | – | – | – | – |
| `check` (nothing to re-check, SW-1193) | 0.34 s | 0.16 | 0.09 | 0.06 (207 entry heads) | – | – | – | – | – | – |
| `check --index` | 3.90 s | 0.20 | 0.08 | 0.06 | 0.59 | **1.85** | 0.24 | 0.04 | 0.27 | 0.65 (writing the index) |
| `test` | 3.32 s | 0.19 | 0.10 | 0.05 | 0.54 | **1.83** | 0.24 | 0.00 | 0.24 | 0.40 (look-up of 1,250 cached results, lowering) |
| `audit --no-search` | 4.69 s | 0.17 | 0.09 | 0.05 | 0.49 | **1.82** | 0.22 | 0.01 | 0.24 | **1.65** (axiom walk) |
| `search List.length` | 3.78 s | 0.13 | 0.08 | 0.06 | 0.36 | **1.42** | 0.17 | 0.00 | 0.19 | 0.1 (`Std/Float.sw`, never cached) + the search, 0.02 |
| `run Aoc.Year2025.Day04.main` | 1.54 s | 0.17 | 0.10 | – | 0.02 | – | 0.02 | – | 0.08 | 1.13 (running the program) |

- `library files` (the library files a namespace needs, replayed from their
  own entries) overlaps with the decode and admit columns, which count those
  files' decoding and admission too; the other columns add up to the total
  within the profile's noise.
- `run` loads only the closure of the namespace it runs (5 namespaces), not
  the whole project; its time is the program.
- `search`'s profile was the first `search` on that cache, which also
  elaborated the library files aoc doesn't use, so its shares understate
  the replay columns somewhat; its CPU is from the timed runs, which were
  warm. One
  library file is never cached: `std/Float/Float.sw` ("`Std.Float.mul` isn't
  admitted with a body", `STITCHWORT_CACHE_DEBUG`), about 0.1 s for any
  command that loads every library file.
- `audit` with its counterexample search (no `--no-search`) took more than
  6 minutes under load 150 on its first run and was stopped; that is the
  search, not loading. Whether its results are cached was not checked.
- **The language server opening aoc** was not driven directly. It goes
  through the same `check_project_namespace` replay of every namespace and
  then builds the navigation index, so it should look like `check --index`
  (3.9 s CPU).

**The fixed floor** every process pays (0.22 s CPU, a one-line file): about
0.11 s elaborating the core (503 declarations, `Session::start` →
`elaborate_namespace`) and about 0.11 s building the standard library's
index (`LibraryIndex::build`, which parses all 66 library files; 0.06 s of
that is parsing). Parsing aoc's 207 namespaces adds 0.06-0.10 s.

**Inside the replay** (whole project, `check --index`, in shares of the
whole run): decode 15% (reading term nodes 6%, the path map 4%, dependency
hashes 3%), admission 54% (of which type evaluation 48%, and the rest:
working out groups and references 2%, the kernel's admissibility check and
installing the groups), side tables 1%, navigation walk 0.6%, reading and
checking the entry head 0.1%. `Values::drop` (9%) is part of the type
evaluation: freeing what evaluating `digitChangesPossible`'s type built.

**`check --index`'s own work** (0.65 s, 17%): building and printing the
index JSON. A third of it is `navigation_index`; 0.14 s is
`stitchwort_syntax::docs::docs` lexing and parsing every file again to find
doc comments, although the session parsed them already.

**games/rogue** (3 namespaces, 29 library files), medians of 3: `check`
0.17 s, `check --index` 0.52 s, `test` 0.32 s CPU. With
`STITCHWORT_TIMINGS`, `check --index` spent 85 ms in the kernel of 780 ms
wall: the floor and the library files dominate, and there is no
`digitChangesPossible`. Item 1 does little for rogue; the floor items do.

## 2. Entry sizes, and I/O against decoding

| entries (aoc's cache) | count | total | median | p90 | largest |
|---|---:|---:|---:|---:|---:|
| namespaces | 207 | 36.3 MB | 43 KB | 398 KB | 7.8 MB (`Year2024.Day13.Proofs`) |
| namespaces, with navigation (`+nav`) | 207 | 38.1 MB | 46 KB | 421 KB | 7.8 MB |
| library files | 65 | 9.6 MB | 29 KB | 558 KB | 1.5 MB |
| library files, with navigation | 59 | 10.1 MB | 44 KB | 692 KB | 1.6 MB |

The next largest namespaces: `Day23.Proofs` 3.5 MB, `Day04.Proofs` 2.1 MB,
`Day06.Proofs` 1.7 MB, `2025.Day09.Proofs` 1.5 MB. aoc's sources are 2.8 MB
(with the inputs the tests include), so the entries are about 13 times the
source. A whole-project load reads about 46 MB (48 MB with navigation).

**Reading is decode-bound, not I/O-bound.** The `open`/`read` system calls
for the entries are about 1.5% of a whole load (about 0.06 s, from the page
cache), checking the entries' seals about 0.7%; decoding is 15% and
admission 54%. `test` opens another 1,250 small files, one per cached test
result (`driver::Cache::get`, 4%, about 0.13 s).

## 3. What else was looked at

- **Caching the core's elaboration**: it is about half the floor, 0.11 s.
  A core entry would save maybe 0.08 s per process. Medium effort (the core
  binds the built-ins), and §4's library-index item saves as much for less.
- **Storing evaluated types**: values hold closures and are not
  serialisable as they stand; item 1 (lazy) gets the same saving without a
  new encoding.
- **Lazy bodies / a cheaper encoding**: see the summary; reading term nodes
  is 6% (0.25 s). Not worth it before items 1-3.
- **Repeated work in the profile**: items 2, 3 and the `docs` re-parse in
  §4 are the cases found.

## 4. Smaller optimisations (about 0.1 s each)

| problem | change | saving | size, risk |
|---|---|---|---|
| `LibraryIndex::build` parses all 66 library files in every process | build the index once: at compile time, or as a cache entry keyed by the library digest | 0.1 s of the 0.22 s floor, on every command, every language server start, and every CLI process the test suites start | small-medium, low |
| `check --index` re-lexes and re-parses every file for its doc comments (`docs::docs`) | pass the session's parsed modules (or the doc comments found when parsing) to `index_data_of` | 0.14 s of `check --index` and the language server's index | small, low |
| `test` reads its cached results one file per test (1,250 files) | one results file per namespace | about 0.1 s of `test` | small-medium, low |
| `std/Float/Float.sw` is never cached (`Std.Float.mul` has no body) | let the cache write float primitives as it does other primitives | about 0.1 s for commands that load every library file (`search`) | small-medium, near the kernel's primitives |

## 5. Method

- Build: `nix develop -c cargo build --release -p stitchwort-cli` at
  2715abfb (no debug info; samply reads the symbol table, so inlined
  functions count against their callers).
- Copies: `aoc/` and `games/rogue/` copied to a scratch folder, their
  `.stitchwort/` removed, the cache filled with `check`, `check --index`,
  `test` and `search` once (`--index` and `test` fill their own entries).
  `STITCHWORT_STD_DIR` pointed at the worktree's library.
- Timed runs: `dev/cache-load-profile/measure.py BIN PROJECT 3` runs each
  command in turn, three rounds, and takes CPU from `getrusage` of the
  child.
- Profiles: `samply record --save-only --unstable-presymbolicate -r 2000
  -o P.json.gz -- stitchwort CMD` (samply 0.13.1 from nixpkgs; it works
  headless on this Mac, no `samply setup` needed), summarised by
  `dev/cache-load-profile/analyze.py P.json.gz --match REGEX...`, which
  gives the CPU share of samples with a matching frame on the stack.
  Summaries: `dev/cache-load-profile/profile-*.txt`.
- Slow admissions: `dev/cache-load-profile/slow-admit.patch` (a temporary
  timer around `elab::kernel::admit_trusted_def`, printing declarations
  over 1 ms with `STITCHWORT_SLOW_ADMIT=1`; not on the branch), on a warm
  `test`. Its times are wall under load 140 and so inflated about 3x; the
  ranking is what matters: `slow-admit-2026-11-04.log`.
- `STITCHWORT_TIMINGS=1 check --index` for the per-unit kernel times.

## Unsure

- All savings in the summary are estimates from profile shares, not
  prototypes. Item 1's is the firmest (two tools agree, and the slow
  declarations are named); whether anything else forces those type values
  later in `test` or the language server is from reading the call sites,
  not from running it.
- The absolute CPU figures under load 120-155 are inflated, perhaps by
  20-30% compared with a quiet machine (SW-1193 measured warm `check` at
  0.56 s at load 10-16; plain `check` with nothing to re-check is 0.34 s
  here).
- `audit` with search was not measured, nor the language server directly.
- Whether old builds' entries are evicted: the worktree's own
  `aoc/.stitchwort/cache` held 1.7 GB when it was copied (the fresh one is
  96 MB). Not investigated.
