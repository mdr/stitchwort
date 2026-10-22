# Proposal: a cache of checked declarations across runs

**Status:** Draft 1, 21 October 2026 (SW-215, D276). A design note only:
nothing is built until Matt has reviewed it. Decisions D277–D287 are in the
[table at the end](#decisions). **Decided (21 Oct 2026, Claude, as recommended):** D277–D287.
D277 was then reopened: stage 1 builds option A, with the load arranged so
that skipping the kernel would be one switch. **Stage 1 is built** (SW-240,
22 Oct 2026): see [As built (stage 1)](#as-built-stage-1). **Stage 2 is
built** (SW-245, 22 Oct 2026): see [As built (stage 2)](#as-built-stage-2).

This note can be read without knowing the codebase. The main part takes about
15 minutes. The [appendix](#appendix) has the evidence: the profile, the
inventory of what the elaborator records, and the survey of other systems.

## 1. The problem

`stitchwort check` starts from nothing every time. On the `aoc/` project
(37 source files, 694 top-level declarations, 317 KB of source), every run
parses, elaborates and kernel-checks the whole project. It also re-checks the
standard library files the project uses. Measured on 21 Oct on a loaded
machine (load average about 14; release CLI; §A.1):

| Run | Wall time | Instructions |
|---|---|---|
| `check` on the whole `aoc` project | 2.77 s | 42.2 G |
| `check Aoc.Day05` (one namespace and what it imports) | 0.39 s | 5.9 G |
| `check` on a one-line file (core only) | 0.08 s | 1.1 G |

The VS Code extension runs `stitchwort check --index - --project <root>` in a
fresh process on every save (`editors/vscode/extension.js:46`). Lanes and the
gate check the same unchanged library and examples over and over. A time
audit found that about 40% of agent time goes to builds and tests. The goal
is to stop paying again for work whose inputs haven't changed.

Only test *results* are cached today. `stitchwort test` keeps one file per
test under `.stitchwort/cache/tests/`, named by the compiler version, a
fingerprint of the compiler's source, the evaluation modes and the test's
content hash (`crates/driver/src/driver.rs:497-617`, `crates/driver/build.rs`).
This note adds the same idea for *checking*.

## 2. The key fact that shapes the design

A declaration's content hash (`crates/core/src/hash.rs`) is a hash of its
**elaborated core term**, meaning the output of elaboration. It covers the
kind, the type, the body, the theorem and instance flags, and, through
references, everything the declaration depends on. It leaves out the
declaration's own name, binder names, source locations and the `fold` flag
(`hash.rs:28-33`, `globals.rs:57-65`).

So **the content hash can't be the lookup key for skipping elaboration**,
because we only know it after elaborating. A cache that saves elaboration
time has to be found from what we have *before* elaborating: the source text
and what it imports. This is how Lean, Agda, Idris 2 and Coq all work. Each
stores one compiled file per source module and reuses it while the module's
source and its imports are unchanged (§A.4). Unison is the exception. It
avoids the problem by storing code only as already-checked, hashed
definitions, and you edit through its tool rather than as text files.

The content hash still has two uses. It checks that a cached entry's imports
are the ones we now have. And the existing test cache keeps working
unchanged, because a declaration loaded from the cache has the same core term
and therefore the same hash.

## 3. What a cache hit lets us skip (soundness first)

The pipeline has two steps. The **elaborator** turns source into a complete
core term, which is untrusted. The **kernel** then checks that term
(`define_group` and friends in `crates/core/src/check.rs:1106-1520`; the
elaborator's module header says "every declaration it produces is then
re-checked by the kernel"). A cache hit can skip:

- **A. Elaboration only.** We load the cached core terms and hand them to the
  kernel exactly as the elaborator would. The kernel re-checks every one,
  including termination.
- **B. Elaboration and the kernel.** We load the cached terms and mark them
  admitted without checking them.

**Option A adds nothing to what must be trusted.** The kernel already treats
the elaborator's output as a suggestion. A cached term is just another
suggestion. A corrupted file, a bug in the cache's encoder or decoder, or a
file from someone else's machine can cause a confusing error, but never an
accepted false theorem. The worst outcome is a stale *answer*, such as an
error or a name resolved the old way, never an unsound one (§3.2).

**Option B makes the cache part of the trusted base.** That means the cache
files, the code that reads them, and the completeness of the key. It also
needs a new kernel entry point, "admit without checking", which is exactly
the kind of API a small trusted kernel shouldn't have. Lean takes this route
for imports. It doesn't re-check `.olean` files when importing them, and
offers `lean4checker`/`leanchecker`, and now `lake check`, to replay them
through the kernel when you want assurance. Coq has `coqchk` for the same
reason (§A.4).

**How much does B save on top of A?** A sampling profile of a full `aoc`
check (two runs, §A.1) puts kernel admission at **about 19%** of the work.
The other ~81% is elaboration, including loading standard library files
(~13%). So A removes most of the cost and B only the last fifth.

**Recommendation (D277): build A.** Revisit B only if measurements after
stage 2 show the kernel re-check dominating warm runs. If B is ever built, it
should be limited to local interactive runs, with the gate always running the
kernel.

### 3.1 Threat model

| Threat | Under A | Under B | Mitigation (both) |
|---|---|---|---|
| Cache file corrupted on disk, half-written, or two writers at once (VS Code and a CLI run) | Kernel rejects it, or it's a stale answer | Could admit a wrong term | Write to a temporary file, then rename. A checksum over the body. A bad entry is treated as a miss and rewritten. |
| Compiler or kernel changed, so an old term would now be rejected | Kernel re-checks, so the new rule applies | Old term admitted | Every key includes the compiler fingerprint (already in `build.rs`) plus `Cargo.lock`, so any compiler change starts a fresh cache |
| A dependency changed | Kernel re-checks against the new dependency | Admitted against the old one | Key includes the dependencies' keys (§4.2). Each reference records the content hash it expects, and a mismatch is a miss. |
| Different natives, compact text or limits | Re-checked | Wrong mode admitted | Modes and limits are in the key, as for tests (`driver.rs:528-536`) |
| A cache copied from elsewhere (another machine, a committed `.stitchwort`, a download) | Sound; may be stale if keys collide by accident | Trusting a stranger's proof | Never read caches you didn't write: a per-machine random salt in the cache directory's header. Mainly matters for B. |
| Someone malicious who can write to your project folder | Can't forge a proof | Can | Out of scope. They could also edit your source. |
| The key misses an input that affects elaboration | Stale but sound answer | Stale and possibly unsound | Conservative key (§4.2), a differential test (§5.4), and `--no-cache` |

### 3.2 What "stale but sound" means

Suppose the key forgot some input, such as a file read by `include`. Then a
namespace could be loaded as it was elaborated last time, even though fresh
elaboration would now give something different: a different instance chosen,
a different error. The kernel still checks whatever is loaded, so nothing
false gets proved, but `check` could disagree with `check --no-cache`. The
defence is a key that errs towards re-elaborating, plus the differential test
in §5.4.

## 4. Granularity, keys and invalidation

### 4.1 Per namespace, not per declaration

The unit is **one project namespace**: all its files, elaborated together by
`elaborate_namespace` (`crates/elab/src/module.rs:208`). For the standard
library it is **one library file**, the unit lazy loading already uses
(`crates/elab/src/library.rs`). This matches how projects are already loaded.
`load_analysis` elaborates one namespace at a time in dependency order, and a
namespace with errors already stops its dependents (`E-NAMESPACE-FAILED`). It
also matches every system surveyed in §A.4.

Per declaration would need, for each declaration, a record of everything its
elaboration looked at. That means every name lookup, every instance searched,
every dot-notation candidate, and `auto` attempts, each recorded so a later
run could tell whether that context changed. That is a large and fragile
addition. Within one namespace, the cheaper and more useful form of
per-declaration reuse is in memory: keep the elaborated state and re-elaborate
from the first changed declaration onward. Lean's language server works this
way. That belongs to the future language server (SW-31), not to an on-disk
cache.

### 4.2 The key

A namespace's key is a hash, computed before elaborating it, of:

1. the compiler fingerprint (`STITCHWORT_FINGERPRINT`, extended to cover
   `Cargo.lock`), the crate version and a cache format version;
2. the modes and limits that change results: natives, compact text,
   `numbers_as_succ`, the step and depth limits, `rewrite_budget`,
   `instance_budget`, and `uniform_operators`;
3. the namespace's name and, for each of its files in order, the path and the
   full text;
4. the path and text of every file it reads with `include` (found by parsing,
   before elaboration);
5. the sorted list of all namespace names in the project, plus
   `stitchwort.yaml` (elaboration reads `project_namespaces`,
   `project_prefixes` and `project_names`, `crates/elab/src/lib.rs:122-127`);
6. the keys of the namespaces it imports, and of the library files they and it
   load, in canonical order.

Item 6 makes this a chain of hashes, like a Merkle tree or Lake's trace
files. An edit anywhere changes the key of that namespace and of everything
that depends on it, and of nothing else. Any change to the source text, even a
comment, re-elaborates that namespace. That is necessary anyway, because its
spans, diagnostics and navigation data have moved.

### 4.3 When the source changes but the hash doesn't

Suppose a comment is added to `Aoc.Common`. Its core terms and content hashes
don't change, but its key does, so it is re-elaborated. Under §4.2 its key
change also re-elaborates everything that imports it, which is wasted work.
The refinement, called **early cutoff** (D280, a later stage), keys a
dependent on its dependency's **output**, not its source. The output is the
content hashes, names, flags and side tables it exports. A comment-only edit
then stops at `Aoc.Common`.

One catch: navigation data records the *span* of each reference's target
directly (`Noted::target`, `crates/elab/src/nav.rs:61-68`). With early
cutoff, a dependent's cached go-to-definition targets would point to old
positions in the edited file. So the cache must store targets by declaration
and look up their spans when loading. That is easy to do from the start.

### 4.4 Interaction with lazy library loading

Library files load on demand, in an order that depends on what the program
uses, so a declaration's `DefId` (a position in `Globals.defs`) differs from
run to run (`globals.rs:203-205`, `library.rs`). A cache entry therefore can't
store `DefId`s. It stores references by full path (`Std.List.length`) together
with the content hash it expects. On load, each reference is resolved in the
current session, its hash is compared (a mismatch is a miss), and it gets the
current `DefId`. Loading an entry for a library file can trigger loading the
files it depends on, cached or not, just as elaborating it would.

### 4.5 Interaction with the test cache

None needed. Tests are found from the loaded program and hashed by content
(`driver.rs:648-700`), and a cached namespace gives the same core terms and
the same hashes. So a warm `stitchwort test` skips both elaboration and
running the tests. Today it skips only the running.

## 5. What an entry holds, and how it is loaded

### 5.1 Contents

Elaborating a namespace changes much more than `Globals.defs`. The appendix
(§A.2) lists every piece of state. An entry must hold everything that later
namespaces, tests, extraction, diagnostics and the navigation index read:

- **Kernel declarations**, in admission order: each definition's
  `name`/`path`, type and body (core terms), theorem, instance and `fold`
  flags, `export` and validators, and group membership. Each data type's
  parameters, indices, constructors, sort, `record` and `auto_params` flags,
  field validators and group. Builtins and registry entries the namespace
  registers (only the core does this).
- **Elaborator tables**, keyed by the declarations above: the scope entries it
  adds, records (projections), interfaces, instances (including the `valid`
  flag, which the hash doesn't cover), abilities, `data_owners`,
  `no_eq`/`no_show`/`no_ord` reasons, `helper_keys`, lifted helpers with their
  spans, equation lemmas, and tests (`TestDecl`).
- **Source-bound data**: warnings, as diagnostics with spans, replayed on a
  hit; and the navigation records (`nav::Recorder`), with targets stored by
  declaration (§4.3).

Spans hold a `FileId`, which depends on the order files were added to the
`SourceMap`. So they are stored as (file path, byte range) and turned back
into the current run's `FileId` when loaded. `Value`s (`ty_value`), the hash
table, erasure data and similar caches are not stored. They are recomputed.

**Only namespaces with no errors are cached** (D284). A namespace with errors
is usually the one being edited, its dependents are skipped anyway, and
replaying errors would add a second way to produce every error message.

### 5.2 Loading is replay

An entry is loaded by **replaying** it through the same functions the
elaborator uses: `declare_*` and `define_*` for the kernel, which re-checks
(option A), and the same insertion functions for each side table. It is not
loaded by patching tables directly. So a loaded namespace goes through the
same consistency checks as an elaborated one. Lean loads imported modules the
same way: each "environment extension" in an `.olean` is replayed into the
importing environment.

### 5.3 Format

The format is our own compact binary encoding, written with a work list the
way the hasher walks terms, not with serde. There are three reasons:

1. Terms nest more deeply than recursion can follow. The hasher and the
   checkers already avoid recursion for this reason (`hash.rs:39-43`), but
   serde's derived code is recursive and would overflow the stack on deep
   terms.
2. It keeps serde derives out of `stitchwort-core`, the trusted crate. Today
   no type there can be serialised (§A.2, item 5).
3. Terms share subterms through `Rc`. A hand-written encoder can keep the
   sharing, or at least decide about it, where serde would silently copy
   shared subterms.

An entry is a header, then the body, then a checksum. The header holds the
format version, the key, the machine salt and the dependency list with
expected hashes. Entries are written atomically. A small `stitchwort cache
dump` that prints an entry would help debugging (implementation detail).

### 5.4 The differential test

The main protection against both stale answers and loading bugs is a test
that checks every example file and the `aoc` project twice: fresh, and from a
warm cache. It compares a canonical dump of the results: declarations, side
tables, diagnostics and the navigation index. Any table the encoder forgets
shows up as a difference. The same test runs whenever someone adds a new side
table to the elaborator, which is the main long-term maintenance risk (§8).

## 6. Where it lives and how big it gets

**Location (D281).** Entries live in the project's
`.stitchwort/cache/check/`, next to `tests/`. Library-file entries live there
too, keyed like the rest. A user-level cache (`~/.cache/stitchwort`) for the
standard library is not worth having yet. The fingerprint changes with every
build of the compiler, and every lane builds its own, so a shared cache would
rarely hit. Revisit when there are releases.

**Size (estimates, not measured; no serialiser exists yet).** The standard
library is 13 files, 323 KB of source and about 1,114 top-level declarations.
`aoc` is 317 KB and 694. Elaborated core terms are bigger than source because
of implicit arguments, lifted helpers, derived instances and equation lemmas.
With an encoding that keeps sharing, my estimate is **2–10× the source**, so
roughly 1–3 MB each for the library and for `aoc`. That is small for disk and
for read time. The peak memory of a full `aoc` check (112 MB, against 24 MB
for the core alone) bounds the whole elaborated state from above. Stage 0
(§7) prints the real figures.

**Eviction (D283).** The test cache shows what happens without eviction.
`aoc/.stitchwort/cache/tests` in the main checkout holds 1,256 files from 20
different compiler builds (5 MB on disk, mostly 4 KB blocks of
six-byte files). For the check cache:

- When an entry for namespace N is written, delete N's older entries.
- On the first write by a new fingerprint, delete entries of other
  fingerprints older than a day. Two worktree binaries may share one project
  folder, hence the grace period.
- Apply the same two rules to the test cache.

## 7. Integration

| Where | What happens |
|---|---|
| `stitchwort check`, `test`, `run`, `build`, `eval` | Use the cache by default. `--no-cache` ignores it and doesn't write. `--cache-dir` as for `test`. (D285) |
| VS Code extension | No change needed: it calls the CLI, and each fresh process now reads the cache. The `--index` output must come out the same from cached namespaces (§5.1), which the differential test covers. |
| Playground | No persistent cache (D287). Each check runs in the worker, and the standard library could later be kept in memory between checks (SW-185 option a). IndexedDB isn't worth it: a playground project is small, and the site must stay static. |
| `cargo test`, the examples snapshots, `dev/t` lanes, the benchmark | Never use it. Tests exist to exercise the elaborator and the kernel, and the benchmark counts their steps. The only exception is the differential test (§5.4), which uses the cache on purpose. |
| The gate | Doesn't use the cache (D286). Its CLI runs pass `--no-cache` or use a throwaway cache directory, and the differential test runs as part of it. |
| Lanes running `stitchwort check` on `aoc` | Benefit directly. Each worktree has its own project folder, so lanes don't share entries, and nothing goes stale across lanes. |
| Future language server (SW-31) | The same entries as the starting point when it opens a project. In memory, per-declaration re-elaboration within the edited namespace (§4.1). |
| SW-185 (cache the checked core) | Stage 1 below covers the on-disk part for library files. Sharing the checked core between sessions inside one process (the test runner, the playground) stays SW-185's question. The core itself costs about 0.08 s per process (1.1 G of the 42.2 G instructions for `aoc`), so it is not a priority for the CLI. |

## 8. Expected speedups

The estimates are from the profile in §A.1. Elaboration is about 81% of a
full `aoc` check (library loading about 13%, inside that), and kernel
admission about 19%. The last column is what stage 2 measured
([As built (stage 2)](#as-built-stage-2)), on a faster tree than §A.1's:
`--no-cache` is the "today" of that column, 1.65 s instead of 2.8 s.

| Scenario | Today | With option A (estimate) | Measured (stage 2) |
|---|---|---|---|
| Full `aoc` check, nothing changed (VS Code save with no edit, gate-style re-run) | 2.8 s | **0.6–0.8 s**: kernel ~0.5 s, plus core 0.08 s, plus reading and decoding | **0.65 s** (1.65 s with `--no-cache`); kernel 0.44 s of it |
| Edit one leaf namespace (such as `Aoc.Day07.Proofs`) | 2.8 s | ~0.7 s, plus that namespace's own elaboration (a whole day's namespace is ~0.3 s) | 0.68 s (a comment in `Aoc/Day05/Day05.sw`, which re-elaborates `Aoc.Day05` and the two namespaces that use it) |
| Edit `Aoc.Common`, which everything imports | 2.8 s | 2.8 s (all dependents re-elaborate); with early cutoff (D280) and a comment-only edit, ~0.7 s | 1.08 s (a comment; not everything imports it, and `Aoc.Day04.Proofs`, one of the two big ones, doesn't) |
| A first run, cold | 2.8 s | 2.8 s plus writing entries (estimate 2–5%) | 1.76 s, 6% more than `--no-cache` |
| (For comparison) option B, nothing changed | 2.8 s | ~0.15–0.25 s | not built; about 0.2 s by the timings (the 0.65 s less the kernel's 0.44 s) |

So option A gives about **4×** on warm whole-project checks, and B about
**10–15×** (as estimated; stage 2 measured 2.5× for A, from a faster
starting point). The first step is A. It is sound by construction, and the extra
gain from B is worth deciding on only after real numbers.

A side finding from the profile: `elab::lift`, which lifts local definitions
and `match` into helpers, accounts for about **43%** of all samples in both
runs. That is more than twice the kernel. A separate look at it could speed
up cold runs too (it should become its own ticket; not part of this design).

## 9. Stages

Each stage is separately mergeable and useful on its own.

0. **Measure.** Add a `STITCHWORT_TIMINGS` environment variable that prints,
   per namespace and library file, elaboration time, kernel time and core
   term sizes (node counts). It confirms §6 and §8 before anything else is
   built. Small.
1. **Library files.** Write the encoder, the decoder and replay for one unit,
   and use them for standard library files only. Their keys are simple
   (fingerprint, modes, file, dependencies). Add the differential test. This
   saves the ~13% library share on every project run and shows the
   replay design works. It is also SW-185's on-disk option.
2. **Project namespaces.** Merkle keys (§4.2), warnings and the navigation
   index replayed, eviction (also for the test cache), and `--no-cache` on
   `check`, `run`, `build` and `eval`. This is where `check` on `aoc` drops to
   well under a second.
3. **Editor.** Nothing in the extension itself. Check that VS Code's save
   loop gets the speedup, and combine it with namespace-scoped checks
   (SW-214).
4. **Optional.** Early cutoff (D280). Then re-measure and decide about option
   B (D277).

## 10. Risks

- **Forgetting a table.** The elaborator keeps about 20 side tables keyed by
  load-order ids (§A.2). A new feature that adds one and forgets the cache
  makes cached runs differ from fresh ones. *Mitigation:* the differential
  test fails, and replay goes through the normal insertion functions.
- **An incomplete key gives stale answers.** *Mitigation:* the conservative
  key, the differential test, `--no-cache`, and a gate that never uses the
  cache. It stays sound under option A.
- **Load-order ids.** Remapping `DefId`s, `DataId`s, ability indices and
  `FileId`s is where bugs would live. *Mitigation:* store paths and hashes,
  never ids, and check each reference's hash when loading.
- **Maintenance cost.** Every change to `Term` or a side table touches the
  encoder. *Mitigation:* the format version is part of the key, so no
  migration is ever needed. Old entries are simply misses (no backwards
  compatibility, as elsewhere).
- **Confusing behaviour while developing the compiler.** The fingerprint
  covers the sources, so a rebuilt compiler always starts fresh. A `cargo
  run` from a dirty tree is no different.
- **Disk growth.** Eviction (§6).

## As built (stage 1)

SW-240, 22 October 2026. Standard library files are cached. Project
namespaces are not yet (stage 2).

### What there is

- **The code.** `crates/elab/src/cache/` encodes, reads and replays one
  library file's entry. `codec.rs` is the byte format, `mod.rs` the entry,
  the key and the replay, and `dump.rs` the canonical dump for the
  differential test. `crates/driver/src/check_cache.rs` is the directory
  that keeps the entries. Nothing was added to `stitchwort-core`.
- **The hook.** `load_library_file` (`library.rs`) computes the file's key,
  tries the entry, and on a miss elaborates the file as before and then
  writes the entry. Nothing else in the elaborator knows about the cache.
- **The format** (D282) is our own. Variable-length integers, a string
  table, a file table, then a table of term nodes, each written after the
  nodes it points to. So writing walks a term with a work list and reading
  is one loop, and neither recurses. A subterm shared through an `Rc` is
  written once and read back shared. The header holds a magic number, the
  format version (`FORMAT`, now 2), the key, the directory's salt and the
  dependencies with their expected content hashes. A BLAKE3 checksum of
  everything comes last.
- **The key** (§4.2) is a BLAKE3 hash of: the compiler version and the
  build fingerprint (which `build.rs` now also takes over `Cargo.lock`),
  the format version, the modes and limits (natives, compact text,
  `numbers_as_succ`, the four limits, `rewrite_budget`, `instance_budget`,
  `uniform_operators`, and whether navigation is recorded), the core's
  text, the file's path and text, and the keys of the files it needs.
- **References** to declarations outside the entry are by full path, with
  the content hash they must have. A path that names two declarations
  can't be written (the file is then not cached). Spans are written as
  (file path, start, length).
- **Where.** `.stitchwort/cache/check/` in the project folder (D281). For a
  single file it is `.stitchwort/cache` in the current folder, as for the
  test cache. `--cache-dir` works for every command. An entry's file name
  is `{fingerprint}-{unit}-{key}`, where the unit is the library file
  (`std.List.Sort`) with `+nav` when navigation is recorded. The salt is
  in `check/header`, made the first time.
- **Writing** goes to a temporary file in the same folder, which is then
  renamed.
- **Eviction (D283)** for the check cache: writing an entry deletes the
  unit's other entries from the same build, and the first write of a run
  deletes other builds' entries that are more than a day old. The test
  cache's eviction is left for stage 2.
- **Commands (D285).** `check`, `test`, `run`, `build` and `eval` use the
  cache. Each has `--no-cache` and `--cache-dir`. For `test`, `--no-cache`
  turns off both caches.
- **Tests (D286).** A `Session` has no cache unless `use_check_cache` is
  called, and only the CLI calls it. So `cargo test`, the snapshots,
  `dev/t` and the benchmark run without it. The CLI tests that start the
  binary pass `--no-cache`. One test, `the_cache_is_in_the_project_folder`,
  uses the default cache in its own temporary project on purpose.

### Loading is replay, and the kernel checks everything

`Elaborator::admit_replayed` is the one place a replay reaches the kernel.
It calls `declare_def`, `mark_folded`, `mark_instance`,
`declare_indexed_data_group`, `mark_auto_params`, `define_group` and
`define_data_group`, each as its own operation with its own limits, as
elaborating a component does. Option B would replace that one function.
There is no "admit without checking" in the kernel.

**Library built-ins** (added after SW-241 made 18 `Int` and `Text`
natives `Home::Library`, bound when `std/Int/Basics.sw` or
`std/Text/Basics.sw` loads). An entry lists the built-ins its declarations
are bound to (kind, place, name; `FORMAT` 2). Replay binds each
declaration as it becomes final through `bind_builtin_def` and
`bind_builtin_data`, the functions elaborating the prelude or a library
file binds through, and the result must be the entry's list, or it is a
miss. Undoing a refused replay also forgets those bindings
(`Registry::forget_from`). A file that binds a core built-in (one that may
register a native with the evaluator) or a primitive still can't be
cached; none does.

After the kernel, the side tables go in through the same insertion
functions elaboration uses: `Scope::insert` and `mark_member` for names,
and the records, interfaces, instances, owners, `no_eq`/`no_show`/`no_ord`,
abilities, lifted helpers and local definitions' keys. When navigation is
on, the references, local variables' types, uses, binders and record
fields recorded in the file go in too.

If anything in an entry doesn't fit, it is a miss and the file is
elaborated. That covers a bad checksum, another key or salt, a dependency
whose path or hash differs, and anything malformed. The whole body is read
and checked before anything changes. If the kernel refuses a declaration,
everything the replay added is removed again first.

### What turned out differently

1. **The order of the kernel calls is worked out, not recorded.** The
   entry holds the final declarations, not a log of the elaborator's calls.
   Replay declares them in their original order. A data group goes where
   its `defs_before` and `datas_before` say. Each group is defined as soon
   as everything its terms refer to is final. That is never later than the
   elaborator defined it, so every declaration finds what it needs. The
   kernel gets the terms it checked the first time, not the elaborator's
   originals. It accepts them, and the differential test shows it gives
   back the same terms.
2. **Side tables are found by comparing before and after.** Before a file
   loads, the cache notes the sizes of the tables and copies the name
   table. Afterwards, what is new is the file's. The one exception is new
   names. `Scope` keeps a log of them while a file loads (`ScopeOp`), since
   the order constructors are added in decides the order of
   `followers`.
3. **Some loads can't be cached, and are just elaborated.** That happens
   when a declaration isn't final, when something is exported or has
   validators, when a core built-in or a primitive is bound, when a test
   is kept, when an
   older instance or table row changed, or when a path names two
   declarations. Today no library file hits any of these, and the
   differential test checks that.
4. **Navigation is in stage 1.** Library files record navigation (the
   editor shows their references when you open one), so an entry has to
   hold it. Entries with and without it are separate units, so the editor
   and the command line don't evict each other's.
5. **Warnings aren't stored.** A library file's warnings were never
   reported (`load_library_file` drops them), so there is nothing to
   replay.
6. **The navigation index can't be compared directly.** When two
   references share a span, the index names the symbol after whichever
   comes first in a hash map. Six runs of `stitchwort check --no-cache
   --index -` on one file named one symbol `Std.Ord.%equal` or
   `Std.Ord.equal`, with either of two types. So the dump compares what
   navigation recorded,
   which the index is made from. That is a separate bug in the index,
   outside the cache.

### The differential test (§5.4)

`crates/driver/tests/check_cache.rs` loads a source fresh, then twice
through a new cache, cold and then warm. It compares a canonical dump of
the elaborator: every definition and data type with all flags, terms,
names and spans, the registry, the whole name table (with followers,
namespaces, the library root and members), every side table, the
library's load order, and what navigation recorded, plus the diagnostics.
It also checks that the cold run wrote an entry for every library file it
loaded, and that the warm run loaded every one from the cache.

- Always: the whole library loaded up front, with and without navigation,
  and every eighth example (files and projects) with navigation.
- Slow tier: every example, and `aoc` with and without navigation (about
  20 s in all).
- Also: a corrupt entry and a cut-short one are misses and get rewritten;
  entries copied from another cache directory are misses (salt); an entry
  under another file's key is a miss; navigation has entries of its own;
  writing deletes the unit's older entries and keeps another build's
  recent ones; a library file that runs out of resources (E-RESOURCE) is
  marked loaded but gets no entry (`cache_after` sees `ok` false), so the
  next run elaborates it again.

I checked by hand that it catches a forgotten table: taking out the replay
of lifted helpers, of members, or of local variables' types makes it fail.
Taking out `no_eq` doesn't, because no library type has a row in it.

### Measurements

Release CLI, wall time, median of 7 runs, with the three kinds of run taken
in turn. The machine was loaded (load average 7–15). `STITCHWORT_TIMINGS`
(SW-239) wasn't on main yet.

| Run | `--no-cache` | Cold (writing) | Warm |
|---|---|---|---|
| `check` one line, core only | 0.094 s | 0.093 s | 0.094 s |
| `check` one line using `Std.List.sort` | 0.258 s | 0.271 s | 0.141 s |
| `check` on `aoc` | 1.910 s | 1.936 s | 1.624 s |
| `run Aoc.Day04.main` | 0.611 s | 0.654 s | 0.424 s |

On `aoc` the warm run saves about 0.29 s, 15%, which matches the library
share in §A.1. Writing the entries costs about 1–7% on a cold run. A
program that loads no library file doesn't change.

Most of a warm load is the kernel checking the declarations again. For the
one-liner, timing replay by hand gave these figures:

| File | Read and check the header | Dependencies | Decode | Kernel | Side tables |
|---|---|---|---|---|---|
| `Nat/Arith.sw` | 0.06 ms | 0.2 ms | 0.5 ms | 6.3 ms | 0.01 ms |
| `List/Toolkit.sw` | 0.06 ms | 0.3 ms | 0.4 ms | 9.3 ms | 0.02 ms |
| `List/Sort.sw` | 0.17 ms | 0.5 ms | 1.2 ms | 23.8 ms | 0.02 ms |

So option B would save most of what is left of a warm library load.

**Sizes.** An entry is 5.5 KB (`Fin`) to 368 KB (`List/Sort`, 5.4 times
its source). The nine files `aoc` loads take 831 KB. That is within the
estimate in §6.

## As built (stage 2)

SW-245, 22 October 2026. Project namespaces are cached too. The kernel
still checks every declaration loaded (option A; D277 stays open, and
`Elaborator::admit_replayed` is still the one place to change for B).

### What there is

- **The hook.** `elaborate_namespace` (`crates/elab/src/module.rs`) asks
  the cache for a project namespace's key. If there is one, it tries the
  entry, and on a miss elaborates as before and writes the entry if there
  were no errors (D284). Single files that aren't in a project are not
  cached, only the library files they load.
- **The key** (D279) is a BLAKE3 hash of: the compiler build, the format
  (`FORMAT`, now 3), the modes and limits, a hash of the whole library's
  text, the namespace's name, a hash the driver makes of its sources, and
  the name and key of every namespace it depends on, in canonical order.
  That last part is the Merkle chain. The driver's hash
  (`Session::namespace_sources`, `crates/driver/src/project.rs`) covers
  each of the namespace's files (its name, such as `aoc/src/Aoc/Day05/Day05.sw`,
  and its text), the sorted names of all the project's namespaces, and
  `stitchwort.yaml`. The whole library is in the key rather than the
  files the namespace loads, because which files those are is only known
  once its names are resolved; the build fingerprint covers the library
  anyway.
- **What an entry holds**, besides what a library file's holds: the
  namespace's tests (with the two sides of a comparison), its warnings
  (code, message, labels and notes), what it needs from the library (the
  files and the fields of its dot calls, as the dependency pass found
  them), the files it `include`d with a hash of each one's text, and the
  names it declared before its library files loaded. A namespace that
  exports something to JavaScript, or has validators, isn't cached (none of
  the examples or `aoc` does).
- **Files.** Spans name their file as `std:List/Sort.sw` or as
  `project:src/Aoc/Day05/Day05.sw`, the path in the project.
- **Navigation targets by declaration** (§4.3). A reference whose target
  is in another unit's file (another namespace's, or the library's) keeps
  the key of the declaration it leads to, and replay looks up where that
  declaration is now. A target in the unit's own files is kept as a span.
  Library entries do the same.
- **Eviction (D283)** as for library files: one entry per unit, which is
  `ns.Aoc.Day05` (or `ns.Aoc.Day05+nav`). A whole-project check and a
  namespace-scoped one give a namespace the same key, so they share
  entries and don't evict each other's.
- **The test cache** now does the same. A result's file name has the test
  (a short hash of its namespace and name) after the build and modes, and
  writing a result deletes that test's other results for the same build
  and modes. The first write of a run deletes other builds' results more
  than a day old.
- **Timings.** `STITCHWORT_TIMINGS` shows a namespace from the cache as
  `Aoc.Day05 (cached)`. The library files it loads are rows of their own,
  as before.
- **`stitchwort test`** from a warm cache loads every namespace from the
  check cache, and the tests' content hashes are the same, so every
  result comes from the test cache: nothing is elaborated or run.

### Replay does what elaborating does, in the same order

Loading a namespace has to leave the session exactly as elaborating it
would, and the order things happen in shows. When a namespace's names are
added decides the order of `followers` (constructors found by their short
name), and a library file that loads in the middle adds its own. So replay
follows elaboration step by step (`replay_namespace` in
`crates/elab/src/cache/mod.rs`):

1. Read the entry's header and the part replay needs first, and read each
   included file again to check its hash. Nothing has changed yet: any
   problem so far is an ordinary miss.
2. Set up the namespace as `elaborate_namespace` does, walk its syntax for
   navigation, and add the names it declared before its library files
   loaded, as elaboration's first pass does.
3. Load the library files it needs, through the same `load_needs` call
   with the same needs. Which files that loads depends on what is loaded
   already, and this way it is the same as elaborating would load in this
   run. (Those files usually come from their own entries.) The needs
   themselves don't depend on what was loaded when the entry was written:
   a name in a library file counts whether or not that file is loaded
   (SW-255, below).
4. Read the rest of the entry, find its dependencies by path and check
   their hashes, then admit its declarations and fill in its tables, as
   for a library file. Then the rest of its names, its members, tests and
   navigation references.

A problem found after step 2 has begun is a "late miss": the namespace is
then elaborated from where replay stopped (the walk isn't done twice, and
loading the needs again does nothing). Its first pass claims again, in the
same place, the names replay declared in step 2 (`replayed_names`), rather
than finding them taken. That is still checked by the kernel, and the
differential test checks the result is the same as a fresh run's (with a
test hook that makes every replay fail late). It should be rare: the key
covers what those steps read, but not which library files the run loaded
before (see below). The statistics count late misses, and the
differential tests check there are none.

**SW-255: one cache, different targets.** `stitchwort check` (the whole
project) and then `stitchwort run Aoc.Day07.main` from the same cache
reported every name of `Aoc.Day07` as defined twice (days 3, 4, 6 and 7).
Two faults together:

1. The needs an entry kept depended on what was loaded when it was
   written. The dependency pass noted a library file only for a name that
   was still pending, so in a whole project check, where earlier days had
   already loaded `std/Fin/Fin.sw` and `std/Vec/Vec.sw`,
   `Aoc.Day07`'s entry didn't list them. `run` checks only `Aoc.Day07` and
   what it imports, so replay didn't load them, and the entry's
   dependency `Std.Fin` wasn't there: a late miss. Now a name in a loaded
   library file counts too (`note_library_use`, by `LibraryIndex::owner`),
   and loading skips what is loaded, so elaborating loads what it did.
2. After a late miss, the names replay had declared were still there, so
   elaborating found each one taken (`E-DUPLICATE`, "first defined here"
   at the same place). Now the first pass claims them again, as above.

Fixing either one fixes the command; both are fixed. The canonical dump
also now shows a navigation reference noted while its library file was
pending as what its name is at the end, which is how the index reads it,
since whether the file had loaded by then depends on what else the run
loaded.

What the namespace adds is found by comparing before and after, as for a
library file, with one more snapshot: the names present when the
namespace starts, the names after its first pass, and everything else
once its library files have loaded. The new names are written in the
order of their short names' `followers`.

### Differences from the plan

1. **Included files are checked, not keyed.** §4.2 item 4 put their text
   in the key, found by parsing. Instead the entry lists the files
   `include` actually read (a hook in `read_include`), with a hash of
   each, and replay reads them again. That checks exactly what was read
   without a second pass over the syntax. Adding or removing an `include`
   changes the source text, so the key changes anyway.
2. **The library files are in the key as a whole** (see the key above).
3. **Navigation's walk is repeated, not stored.** The outline, local
   variables and binders, and record fields come from walking the syntax,
   which replay does again. Only references and local variables' types,
   which elaboration finds, are stored.
4. **Warnings are stored**, for namespaces (stage 1 had none to store).
5. **The navigation index is compared directly.** SW-244 made it
   deterministic, so the stage 1 workaround (comparing what navigation
   recorded instead) is no longer the only check.
6. **A fix found on the way.** The canonical dump asked the registry about
   library built-ins whose file hadn't loaded, which a debug assertion
   refuses; and the differential test's temporary folders could collide
   when two threads read the clock at once.

### The differential test

- `crates/driver/tests/check_cache.rs` compares the canonical dump (now
  with tests' sides and `globals.module`) and the diagnostics, fresh
  against cold and warm. It checks that the warm run loaded every
  namespace the cold run wrote, that no namespace was uncacheable, that
  there were no late misses, and that an accepted project had a namespace
  from the cache. Always: every eighth example, files and projects, with
  navigation. Slow tier: every example with navigation, and `aoc` with and
  without.
- New there: an edit to a namespace re-elaborates it and what uses it and
  nothing else (Merkle); a namespace with errors isn't written; a changed
  included file is a miss; a new namespace or a changed `stitchwort.yaml`
  is a miss for every namespace.
- Added for SW-255: one target writes the cache and another reads it (the
  whole project, then one namespace, and the other way round), on a small
  project with `Tests` namespaces, giving what the reader gives without a
  cache, with every namespace both checked from the cache and no late
  miss; in the slow tier, every `aoc` namespace on its own from the whole
  project's entries; and a replay made to fail late gives the fresh
  result.
- `crates/cli/tests/check_cache.rs` runs the built command. What
  `stitchwort check --index - --project P` prints (the index, the
  diagnostics and the exit status) is byte for byte the same with
  `--no-cache`, cold and warm: always for every fourth example project,
  and in the slow tier for all of them and for `aoc`, both the whole
  project and `Aoc.Day05` on its own (the editor's save path) from the
  whole project's entries. Also: a warm `stitchwort test` reports every
  result from the cache and every namespace `(cached)`. And (SW-255)
  `check`, `check B`, `run`, and `test` in pairs, sharing one cache, each
  print what they print with `--no-cache`.
- `crates/cli/tests/aoc_answers.rs` also runs every day from the cache a
  whole project `check` wrote.
- `crates/cli/tests/caching.rs`: the test cache's eviction.

### Measurements

Release CLI, wall time, median of 7 rounds, each round taking every kind
of run in turn, on a copy of `aoc` with its own cache folder. The machine
was loaded (load average 14 to 26), so the absolute times are rough.

| Run | `--no-cache` | Cold (writing) | Warm |
|---|---|---|---|
| `check` on `aoc` | 1.654 s | 1.758 s | **0.649 s** |
| `check`, after a comment in `Aoc/Day05/Day05.sw` | | | 0.679 s |
| `check`, after a comment in `Aoc/Common/Range.sw` (`Aoc.Common`) | | | 1.081 s |
| `run Aoc.Day04.main < inputs/day04.txt` | 0.570 s | | **0.204 s** |
| `check --index - --project aoc` (VS Code, opening) | 1.841 s | | **0.766 s** |
| `check --index - --project aoc Aoc.Day05` (VS Code, each save) | 0.332 s | | **0.207 s** |
| the same, after a comment in `Aoc/Day05/Day05.sw` | | | 0.207 s |

Where a warm whole-project check goes (`STITCHWORT_TIMINGS`, three runs:
0.63 s, 0.63 s, 0.70 s wall): the kernel re-checking everything is 435 to
493 ms; the core prelude about 60 ms; parsing and printing about 60 ms;
reading and decoding the entries the rest (130 to 144 ms of "elab",
including the core). The two big proof namespaces are most of the kernel
time: `Aoc.Day02.Proofs` 188 ms and `Aoc.Day04.Proofs` 145 ms. So option
B (D277) would take a warm check from about 0.65 s to about 0.2 s.

A namespace-scoped warm check (`Aoc.Day05`, 0.17 s with timings on) is
now mostly fixed costs: the core (about 60 ms) and parsing the whole
project (about 60 ms).

**Sizes.** `aoc`'s namespace entries take 5.0 MB (5.3 MB with
navigation), from 432 KB of source. Most of it is the two big proof
namespaces: `Aoc.Day02.Proofs` 2.4 MB and `Aoc.Day04.Proofs` 1.4 MB. The
`Tests` namespaces are 80 to 95 KB each, since they hold the puzzle input
they `include`. With the library files' entries, a cache with and without
navigation comes to 12.4 MB.

## Decisions

| ID | Question | Recommendation |
|---|---|---|
| D277 | When we reuse a cached result, do we still run the kernel's check on it? | [**Yes.** We skip only elaboration (option A), so a cache file can never make a false proof accepted. Skipping the kernel too (option B) would save about another fifth of the time. Reconsider that only after stage 2's measurements, and then only for local interactive runs, with the gate always checking.] |
| D278 | What unit is cached? | [**One project namespace, and one standard library file.** Not single declarations. Reusing single declarations is a job for the future language server, in memory.] |
| D279 | What decides whether a cached namespace is still valid? | [A hash, computed before elaborating, of: the compiler build (including `Cargo.lock`), the modes and limits, the namespace's files and their text, files it `include`s, the list of project namespaces and `stitchwort.yaml`, and the same hash of everything it imports. Any edit re-checks that namespace and everything that uses it.] |
| D280 | Should a comment-only edit in a namespace avoid re-checking the namespaces that use it ("early cutoff")? | [**Later, stage 4.** It needs dependents keyed by what a namespace *produces*, not its text, and navigation targets stored by declaration (planned from the start).] |
| D281 | Where are cache files kept? | [**In the project**, under `.stitchwort/cache/check/`, next to the test cache. No shared per-user cache until there are compiler releases.] |
| D282 | What file format? | [**Our own compact binary encoding**, not serde, written with a work list like the hasher, with a format version, a checksum and atomic writes.] |
| D283 | How do old cache files get cleaned up? | [Keep only the newest entry per namespace, and drop entries from other compiler builds (after a day's grace). Apply the same rule to the test cache, which today keeps everything (1,256 files from 20 builds in `aoc`).] |
| D284 | Are namespaces with errors cached? | [**No.** Only namespaces that check without errors. Their warnings and navigation data are stored and replayed.] |
| D285 | Is the cache on by default? | [**Yes**, for `check`, `test`, `run`, `build` and `eval`, so VS Code and lanes get it without changes. `--no-cache` turns it off.] |
| D286 | Do the gate and the test suites use it? | [**No.** Tests and the benchmark must exercise the checker. The gate runs without the cache, plus one differential test that checks fresh and cached results are identical.] |
| D287 | Does the playground get a cache? | [**No persistent one.** At most, later, the standard library kept in memory between checks in the worker (SW-185).] |

---

## Appendix

### A.1 Measurements (21 Oct 2026)

The machine was loaded (load average 13.8–15.6; other lanes running), so
treat the absolute times as rough and the proportions as the useful part. The
release CLI at the main repo's `target/release/stitchwort` predates the
`Option` rename (SW-210), so I measured the `aoc` tree as of commit `512bed0`,
the last commit before the rename, exported to a scratch folder.

`/usr/bin/time -l`:

| Command | real | max RSS | instructions retired |
|---|---|---|---|
| `check` (whole `aoc` project) | 2.77 s | 112 MB | 42.2 G |
| `check Aoc.Day05` | 0.39 s | 44 MB | 5.9 G |
| `check` one-line file | 0.08 s | 24 MB | 1.1 G |

**Profile.** I used `/usr/bin/sample` at 1 ms over a whole-project `check`,
twice. Each line counts the samples under the outermost matching frame, as a
share of the checking thread's samples. The sampler attached about 50 ms in,
so the core prelude is mostly missing; it is about 0.08 s on its own.

| Frames | Run 1 (3,325 samples) | Run 2 (2,270 samples) |
|---|---|---|
| `elaborate_namespace` (all project work) | 3,324 (100%) | 2,246 (99%) |
| Kernel admission: `core::check::{define_group, define_def, define_data_group, define_ctors, declare_*}` | 638 (19.2%) | 422 (18.6%) |
| Any `core::check::{infer, check, check_type}`, including calls from the elaborator | 737 (22.2%) | 445 (19.6%) |
| `load_libraries` (lazy standard library files) | 433 (13.0%) | 291 (12.8%) |
| `elab::lift` | 1,410 (42.4%) | 991 (43.7%) |
| `elab::rewrite` | 274 (8.2%) | 190 (8.4%) |

The kernel admission frames include re-checking library files as they load.
Content hashing didn't appear at all (`check` doesn't hash).

The sizes in §6 come from `cat` and `grep -cE '^\s*(def|theorem|data|instance|interface|record|test|ability|lemma)\b'`
over `crates/elab/src/std` and `aoc/src`. The test cache figures in §6 come
from `ls` and `du` on `/Users/matt/repos/misc/funlang/aoc/.stitchwort/cache`.

### A.2 What elaborating a declaration records

This is a survey of `crates/core/src/globals.rs` and `crates/elab/src/lib.rs:110-267`
and the modules they point to. Everything below is keyed by position in
`Globals.defs` and `Globals.datas`, so it depends on load order.

- **`Def`** (`globals.rs:26-70`). Hashed: type, body, theorem, instance.
  Not hashed: `name`, `path`, `fold`, `span`, `arity` (derived), `group`
  (hashed only as structure). `export` and `validators` are set after
  admission (`check.rs:2129`).
- **`Data`** (`globals.rs:105-151`). Hashed: path, parameters, indices, sort,
  constructors with names and fields, `record`, and `auto_params` when set.
  Not hashed: `defs_before` and `datas_before` (load-order counters for
  positivity), field validators, span.
- **`Builtins` and `Registry`.** Natives, primitives and compact-text ids,
  keyed by `DefId`, set while the core loads.
- **Elaborator tables:**
  - `scope` (names to `Global`, with spans);
  - `records`;
  - `interfaces`;
  - `instances` (with a `valid` flag that isn't hashed);
  - `data_owners`;
  - `abilities` (indexed by position: `Global::Ability(usize)`);
  - `no_eq`, `no_show` and `no_ord`;
  - `helper_keys`;
  - `lifted` (with spans);
  - `namespace_defs` (`DefId` ranges);
  - `prelude_defs`;
  - `tests` (`DefId` and span);
  - `nav` (all span-based; `Noted::target` is a span, `nav.rs:61-68`);
  - warnings.
- **Transient**, not cached: metas, obligations, the per-module state,
  per-declaration scratch state, and recomputable caches (`ty_value`,
  hashes, erasure, `result_heads`).
- **Serialisation today:** none. The only serde use is reading
  `stitchwort.yaml` (`crates/driver/src/project.rs:589`).
- **`Term`** (`crates/core/src/term.rs:82-133`) has 19 variants. It uses `Rc`
  sharing, contains `Loc(Span, …)` nodes, and holds `Nat` as `Rc<BigUint>`. It
  holds no `Value`s. `Meta` never reaches the kernel.

### A.3 Why not key by content hash after all?

One could elaborate everything, compute each declaration's content hash, and
skip only the *kernel* for hashes already admitted. That is the
"`Unison`-style" reading of the ticket. It only saves the ~19% kernel share,
and it is exactly option B's trust problem: a "this hash was admitted" record
is a trusted claim. It is the wrong half of the cost to save.

### A.4 How other systems do it

- **Lean 4.**
  - Each module compiles to an `.olean`, and importing loads it **without
    re-checking it in the kernel**. The Lean reference says the check marks on
    imported code mean something only if you "trust the authors of the
    imported libraries… that they performed this check".
  - `lean4checker` (now `leanchecker`, bundled from v4.28) "replays them
    through the kernel". With `--fresh` it replays imports too. It "trusts
    that the `.olean` files are structurally correct".
  - For hostile input, the "gold standard" is *comparator*: build in a
    sandbox, export, and replay outside it.
  - Lake decides whether to rebuild from trace files: hashes of inputs and
    dependencies, compared with the stored trace.
  - Sources: https://lean-lang.org/doc/reference/4.29.0/ValidatingProofs/,
    https://github.com/leanprover/lean4checker,
    https://lean-lang.org/doc/api/Lake/Build/Common.html
- **Agda.**
  - Each module has an `.agdai` interface file in `_build/VERSION/` under the
    project root, so "different directories are used for different versions of
    Agda". "An external module is loaded by loading its interface file". The page
    doesn't say whether it is re-checked; I assume not, since that is the
    point of the file.
  - `--ignore-interfaces` re-type-checks everything.
  - Sources: https://agda.readthedocs.io/en/latest/tools/interface-files.html,
    https://agda.readthedocs.io/en/latest/tools/command-line-options.html
- **Idris 2.**
  - Each module has a `.ttc` file in `build/ttc`.
  - Whether to rebuild was decided by modification time. A PR added
    source-hash checking behind `-Xcheck-hashes`, mainly to speed up CI.
  - Source: https://github.com/idris-lang/Idris2/pull/1535
- **Coq/Rocq.**
  - Each file has a `.vo` file, loaded without re-checking.
  - `coqchk` is a standalone checker. It re-type-checks the logical content of
    `.vo` files and their dependencies, but not notations or implicit
    arguments. It exists because `coqtop` "can load custom tactics" so "it
    cannot be guaranteed that the produced compiled libraries are correct", and
    to make sure a third-party library "was not forged".
  - Source: https://rocq-prover.org/doc/V8.19.0/refman/practical-tools/coq-commands.html
- **Unison.**
  - "Each Unison definition is identified by a hash of its syntax tree", so
    "we can parse and typecheck definitions once, and then store the results
    in a cache which is never invalidated."
  - This works because the codebase is a store of checked definitions, not
    text files.
  - Source: https://www.unison-lang.org/docs/the-big-idea/

**What we take from them.** All of them cache per module, keyed by source and
imports. All of the proof assistants trust their cache files on import and
offer a separate full re-check for assurance. Under option A we re-check on
every load, which is stronger than any of them by default. It is affordable
because the kernel is only about a fifth of our cost.

### A.5 As measured (stage 0)

Stage 0 is built: `STITCHWORT_TIMINGS=1` makes the CLI print, per unit (the
core prelude, each library file, each project namespace, in load order),
elaboration time, kernel admission time and core term size to stderr
(`crates/elab/src/timings.rs`). Elaboration time excludes both the kernel
time and the library files loaded inside the unit. Kernel time is the time
inside the elaborator's calls to the kernel's `declare_*` and `define_*`
functions (wrappers in `crates/elab/src/kernel.rs`; the core crate has no
timing code). It doesn't include the `infer` and `check` calls the elaborator
makes along the way, so those count as elaboration. Nodes are tree nodes of
the types and bodies (for data types: parameters, indices, field types and
results), not counting source-location wrappers; a shared subterm counts each
time it appears. Declarations are defs and data types, the generated ones
too. With the variable unset, a full `aoc` check took 1.84 s and 1.80 s,
against 1.85 s for the main checkout's binary, so the overhead is below the
noise.

Release build, `aoc` as of this commit, load average about 8, so trust the
proportions more than the milliseconds. Times in ms. Three runs of the full
check agreed within about 5%; the table uses the first.

| Command | wall | elab | kernel | outside the units | nodes | decls |
|---|---|---|---|---|---|---|
| `check` (whole `aoc`) | 1,894 | 1,289 | 532 | 74 | 1,101,469 | 2,204 |
| `check Aoc.Day05` | 516 | 329 | 151 | 37 | 298,011 | 1,271 |
| `check` one-line file | 70 | 39 | 12 | 18 | 21,680 | 432 |
| `run Aoc.Day04.main` | 563 | 254 | 75 | 235 (the program running) | 124,529 | 1,186 |

Where the full check's time and terms come from:

| Part | elab | kernel | nodes | decls | source |
|---|---|---|---|---|---|
| core prelude | 46 | 14 | 21,678 | 431 | |
| 13 library files loaded | 314 | 146 | 293,289 | 847 | 259 KB |
| 16 project namespaces | 928 | 371 | 786,502 | 926 | 318 KB |

`aoc` loads 13 of the library's files: 259 KB of the 323 KB in §6.

**What differs from §6 and §8.**

- **The kernel share is bigger.** Admission is 29% of unit time (532 of
  1,820 ms), not the ~19% of §A.1, and elaboration is 71%, not ~81%. This
  counts only the declare and define calls, so it is a lower bound on all
  kernel work. §8's warm-run estimate (kernel about 0.5 s for the whole
  project) agrees with the measured 0.53 s.
- **The library share is bigger.** Library files are 460 ms of 1,820 (25%),
  not ~13%, and the core prelude adds 60 ms. For a small target the library
  dominates: `check Aoc.Day05` spends 418 of 480 ms in library files (87%),
  and `run Aoc.Day04.main` 267 of 328 ms (81%). Stage 1 (library files
  only) is therefore worth more than §9 says. If replay re-admits the
  library in the kernel (137 ms for Day 5), `check Aoc.Day05` would take
  about 0.23 s instead of 0.52 s, and Day 4's `run` about 0.36 s instead of
  0.56 s, of which 0.23 s is the program.
- **The cost is concentrated.** `Aoc.Day02.Proofs` (537 ms, 437k nodes) and
  `Aoc.Day04.Proofs` (487 ms, 230k nodes) together are 1,025 ms of 1,820:
  56% of all unit time. The other project namespaces are each under 120 ms
  (`Aoc.Day07.Proofs` is the next, 120 ms). So §8's "edit one leaf
  namespace, ~0.7 s" holds for most namespaces but not these two, where it
  is about 1.2 s even with a perfect cache.
- **One library outlier.** `std/Mod/Mod.sw` is 12 KB of source, 167,748
  nodes (14 per source byte) and 146 ms, with kernel time equal to
  elaboration time (74 and 73 ms), where 30% is usual. Worth a look as its
  own ticket, separate from the cache.
- **Parsing and printing are small.** The time outside the units (the core
  load counts as a unit) is 74 ms of 1,894 (4%). The timings don't split
  `elab::lift`, which §8 put at 43% of samples; it is inside elaboration.

**Term size as a guide to entry size (§6).** 259 KB of library source
produced 293k nodes (1.1 nodes per source byte), and 318 KB of `aoc` 787k (2.5
per byte). The two big proof namespaces are 85% of `aoc`'s nodes (666k) from
168 KB of source (4 per byte); the rest of `aoc` is 120k nodes from 150 KB
(0.8 per byte). No serialiser exists yet, so entry size in bytes is still
not measured. If a node encodes in 2 to 4 bytes before any sharing, the
library comes to 0.6 to 1.2 MB and `aoc` to 1.6 to 3.1 MB, with most of
`aoc` in two entries (1.3 to 2.7 MB of it). That is the same order as §6's
1 to 3 MB, and probably an overestimate once the encoding shares subterms:
these counts are trees, and the full check peaks at 112 MB in memory. Disk
and read time stay fine even if the two proof entries come to a megabyte or
more each.

To reproduce, run `STITCHWORT_TIMINGS=1 stitchwort check` in `aoc/`. Any
command works; the table goes to stderr.
