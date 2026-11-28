# A faster warm `search`: caching what it rebuilds each run (SW-4947)

**Status:** design note, 27 November 2026, for Matt's decisions. Nothing is
built. Questions D3768 (trust) and D3769 (leaving the project out) are at
the [end](#6-decisions-for-matt). I read the code at `1d18e5445` and ran
only the release CLI from `main`, a few warm searches. A claim with a
file:line is one I read; **[inferred]** marks reasoning I didn't confirm by
reading every caller.

## 1. In short

**The problem.** A warm `stitchwort search` takes 1.49 s on std alone and
2.25 s in `aoc/` with `--in Std` (SW-4935, measured, best of 3), against
0.34 s for `check` of a one-line file. SW-4935's profile of the std-only
search puts the time in work every search redoes from scratch:

| Share | What | Seconds (of 1.49) |
|---|---|---|
| 34% | the core's and library's deferred equations, made again (3,009 definitions from 897 keys) | 0.51 |
| 19% | replaying std's 10,479 other definitions from the check cache | 0.28 |
| 14% | re-elaborating `Float.sw` (SW-1204, its own lane) | 0.21 |
| 11% | each candidate's `type_index` | 0.16 |
| under 1% | comparing, ranking and printing | under 0.015 |

In `aoc/`, loading the project adds about 0.76 s more (2.25 − 1.49 s,
measured), even with `--in Std`.

**The change.** Three caches and one skip, none of which changes a result:

1. Keep each library file's deferred equations in the check cache, in an
   entry of their own beside the file's, replayed as the file's entry is
   (§2).
2. Keep the part of `type_index` that costs (the folded read-back) with
   those equations, and memoise it in the session (§3).
3. Under `--in Std`, load the project only when the query names something
   the project declares; read the project through the scan cache when it
   is loaded (§4).

**What it should do** (estimated from the profile, §5): std-only
1.49 → about 0.92 s, and about 0.72 s once SW-1204 lands; Matt's
`aoc/ --in Std` 2.25 → about 0.94 s (0.74 s). A search that does need the
project: 2.38 → about 1.63 s. In the language server (SW-4945) a held
session pays the equations and the index once, so every search after the
first is the comparison alone, tens of milliseconds.

## 2. The deferred equations

### 2.1 What happens today

The core's and library's definitions don't get their equations
(`f.eq1`, `f.eq2.ifTrue`, …) when they load: `defers_equations`
(`crates/elab/src/equations.rs:6311`) puts them off, because made eagerly
they cost every run (+11% of a small program's steps). They are made on
demand (`ensure_equations_of`, `equations.rs:6334`): for a program that
names one (`load_needs`, `crates/elab/src/library.rs:1234`), for a library
file's own proofs while it loads (`ensure_loading_file_equations`), and all
at once for commands that list them, `generate_deferred_equations`
(`equations.rs:6412`). That one walks the core and every loaded file in
load order and makes the equations of each non-theorem, non-instance
definition with arms. Its callers:

- `search` (`crates/driver/src/search.rs:590`),
- `search --at` (`crates/driver/src/search_at.rs:792`, `:795`),
- `doc` (`crates/driver/src/doc.rs:1249`),
- tests (`crates/driver/tests/proofs/function_equations.rs`,
  `function_induct.rs`, `library/search_bench.rs`).

None of what it makes is kept: an on-demand equation runs as a nested unit
(`in_library_file`, `library.rs:1632`, through `enter_nested_unit`), and
the cache writes only whole library files and project namespaces
(`namespace_parts` refuses a namespace during which "a nested unit ran part
way through", `crates/elab/src/cache/mod.rs:1683`). The one exception
already shows the shape of the fix: equations that a file's own proofs name
are made inside that file's unit, so they are in its entry, and
`ensure_equations_of` finds them already in scope after a replay ("Made
with the definition already", `equations.rs:6362`).

### 2.2 The entry

**One entry per library file `F`, "the equations of `F`"**, unit name
`eqs.<F's unit>` beside `cache_unit(F)` (`cache/mod.rs:796`). It holds,
for each key of `F` whose equations `generate_deferred_equations` would
make and that `F`'s own entry doesn't already hold, one **segment**:

- the declarations making that key's equations made (the `f.eqN`
  theorems, the `.or` and `.ifTrue` variants, `f.induct` where made, and
  their helpers), with a dependency header of their own: every definition
  and data type they name, by full path and content hash (the `Dep`
  triples entries already use, `cache/mod.rs:107`);
- the side tables it wrote: `equations_done`, `equation_skips`, the
  induction notes (`induct::no_equations`), and the names it declared with
  their followers' order, captured by the same journal write set
  (`write_set`) that a library file's entry is encoded from, not by a hand
  list. A segment is a unit as far as the journal is concerned: making one
  key's equations under a capture, as `in_library_file` already runs it,
  and encoding what that unit wrote.

Segments rather than one block per file because a session may have made
some of `F`'s equations already (a project namespace that needed
`List.length.eq2`, `load_needs`), and those must be skipped, not made
twice; and so that a later `check` could take just the keys it needs
(§2.5).

**The key** is `F`'s library key (`library_key`, `cache/mod.rs:807`),
which covers `F`'s path and text and the keys of every file it needs,
together with the entry format, `modes()` and the navigation tag, as the
file's own key is. The keys whose equations it holds are a function of
`F`'s text, so they are covered. **The stamp** must be exact: this build,
this kernel side, this core digest and library interface, no carried-over
hit (as the core's entry is, `cache/core_entry.rs:1`).

**Who writes it.** A session that ran `generate_deferred_equations` with
the cache on and got no error: after each file's equations are made, its
entry is written if it was missing. So the first warm search (or `doc`)
after a std edit makes them as today and writes them; the next replays.

### 2.3 What replay checks before admitting a segment

So that a replayed equation is admitted exactly as a freshly made one
would be, in the same session state:

1. **The entry fits.** Checksum, salt, format, exact stamp and key, as for
   any entry; else a miss, and the key's equations are made fresh.
2. **`F` is loaded** in this session, from its entry or from source (its
   key is the same either way).
3. **The key isn't done**: not in `equations_done`, and its first
   equation's name not in scope (the two checks `ensure_equations_of`
   makes, `equations.rs:6335`, `:6362`). A done key's segment is skipped.
4. **The definition is there and final**: `lookup_def(key)` finds it and
   its state is `Final` (`equations.rs:6348`), as fresh generation
   requires.
5. **Every dependency in the segment's header** is in the session with the
   recorded content hash. This is what ties a cached `f.eq2` to this
   session's `f`: the kernel accepted that theorem, with that proof,
   against definitions with exactly these hashes. A segment whose `f` has
   changed can't be admitted, whatever the key says.
6. **Admission** goes through `admit_replayed` (`cache/mod.rs:4660`), the
   one place replayed declarations reach the kernel, on the trusted path
   (the question in D3768), or on its re-checking path, where the kernel
   checks every type and proof again (`hit.recheck`,
   `cache/mod.rs:4647`). A refusal undoes the segment (`forget_since`),
   counts `Stats::refused`, and the key's equations are made fresh.
7. **Order.** Segments are replayed in the order fresh generation makes
   them (the core, then `lib.order`, then each file's keys in source
   order), so each equation gets the DefId it would have had. Nothing the
   search prints depends on DefIds (ranking ends with the full name,
   `crates/elab/src/search.rs:692`), but `doc` output and the out-of-budget
   list follow load order, and keeping it costs nothing.

Whether an item is a generated equation (`Item::generated_equation`,
`search.rs:500`) is read from its name, so it needs nothing extra.

### 2.4 What it saves, and who else benefits

Replaying 10,479 definitions takes 0.28 s (19% of 1.49 s, measured), about
27 µs each. The equations' 3,009 definitions at that rate are about
0.08 s, against 0.51 s to make them: **about −0.43 s a search
(estimated)**, on the trusted path. On the re-checking path, the kernel's
share of the 0.51 s isn't known: the profile doesn't split elaboration
from checking. Stage 1 can measure both paths, since both exist.

The same saving goes to `doc` (std's reference pages list every equation)
and `search --at`. The language server's held session makes them once per
session already (`equations_done` makes a second call free), so it gains
only at start and after a std edit.

Built (SW-4954, 27 Nov 2026), as above, plus one check: a segment must
mark its own definition done, since which segment is filed under which
definition is only the container's word. Measured: warm `search --in Std
'() → {Parse Char} Int'` 1.27 s → 0.79 s, `doc Nat.gcd` 1.56 s → 1.10 s,
results byte-identical; the first search after a change writes the
entries (1.65 s once). The installed bundle (SW-2163) doesn't carry them
yet: its recorder loads the library without making the equations.

### 2.5 Not proposed: `check`'s on-demand equations

A project namespace that names a std equation makes it on demand at every
replay (`load_needs` runs before replay, `cache/mod.rs:1848`). The same
segments could serve it. Not proposed now: aoc/ and tools/fmt name one std
equation between them (a rough grep for qualified `X.f.eqN` names; implicit uses not counted), so the saving is probably small (not measured),
and it would put cached equations under proofs that `check` reports as
checked. Revisit if a project's profile shows it.

### 2.6 Rejected: holding the equations in the file's own entry

Making all of `F`'s equations when its entry is written, so the entry
carries them, would serve `check` too, but every check that replays `F`
would then replay 29% more std declarations (3,009 on 10,479) for
equations it rarely uses, undoing what `defers_equations` exists for. A
separate entry is read only by the commands that list them.

## 3. `type_index`

Each candidate's index (`Elaborator::type_index`, `search.rs:1458`) is the
definitions and data types its type names, syntactically (`constants`,
`data_types`, `search.rs:785`, `:795`: cheap) and after evaluating the
type and reading it back folded (`eval` and `quote_folded`: the 11%). It
is computed for every candidate `--in` keeps (`search_candidates`,
`search.rs:1394`), 14,000-odd for std.

**Making it lazy doesn't help** [inferred]: the filtered pass needs the
pattern's constants to be a subset of the index, and most candidates fail
that test, which is exactly when the folded half has to be computed to be
sure. A candidate whose syntactic index already passes could skip it, but
those are the few.

**Persist the folded half, and memoise it.**

- *In the session*: a memo on the elaborator from an item's content hash
  (`def_hash`, `data_hash`, the type's hash for a theorem's conjunct) to
  the extra definitions and data types the folded read-back adds. Two
  types with the same content hash have the same dependencies, so the same
  fold. This serves the language server (SW-4945): its held session
  computes each index once.
- *On disk*: with each equation segment, and in a small section of the
  equations entry for `F`'s other declarations, the extra names as full
  paths (usually none: folding mostly finds what is written). Replay
  resolves them to ids through one path map built per session. The memo
  above is filled from them.
- *The gluing switch* (`self.gluing()`) changes the fold; it is in
  `modes()`, so in the key [inferred: confirm in stage 2].

Saving: about −0.14 s a search (0.16 s, less about 0.02 s to read and
resolve the names, estimated). A differential test compares every std
candidate's index from the entry with a fresh one.

## 4. Leaving the project out

### 4.1 What happens today

`search` in a project (`crates/cli/src/main.rs:4805`) parses every
project file (`analyse`, `main.rs:4889`), loads every namespace
(`load_analysis` with `Target::Everything`, `main.rs:4901`), then the rest
of std (`load_all_libraries`, `main.rs:4919`), and searches with
`Scope::Project(names)`, which adds `import N (..)` for each namespace
after `import Std (…)` (`search.rs:594`). With `--in Std` the
project's declarations aren't candidates (`in_namespaces`, `search.rs:62`),
but a pattern still sees the project's names.

That matters. In a probe project declaring `type Pair = | MkPair (n: Nat)`
and `def length (p: Pair): Nat` (run with `main`'s release CLI):

| Query, `--in Std` | With the project | Std alone |
|---|---|---|
| `length (_ ++ _)` | `length` is the project's: `E-TYPE-MISMATCH` | `length` is a named hole: 111 matches |
| `Pair → Nat` | `E-ARITY` (std's `Pair` wins the clash) | `E-ARITY` |

So a naive skip changes results, and the rule must cover lowercase names,
which would otherwise become holes.

### 4.2 The rule

Load the project only if one of these holds; otherwise search std alone:

1. `--in` is absent, or names a namespace that isn't `Std` or under it.
2. Some name in the query (the pattern and the mentions, with every
   segment of a qualified name) is a segment of a name the project
   declares, or of one of its namespaces' paths. The declared names come
   from the scan (`Scan::new`, `crates/driver/src/project.rs:1203`, the
   cached per-file `FileSketch`, `crates/elab/src/project/sketch.rs:30`):
   `declared` (each declaration's name, its members, a record's fields)
   and the namespace line. Equation names (`f.eq2`) and local definitions
   (`t.go`) aren't in `declared` (`sketch.rs:254`), but their first
   segment is, so comparing every segment covers them.

`"text"` parts are left out of the test: they filter candidates by name,
and the candidates are std's either way.

### 4.3 Why the results are then identical

With no query name reaching a project declaration, the project can change a
search only through something the query doesn't name:

- **Instances.** An instance must be declared with its interface or its
  type (`E-INSTANCE-ORPHAN`, docs/syntax.md:865), so a project instance is
  on a project type or a project interface, which a query naming only std
  types and interfaces can't select. A hole's type is settled only by
  what the query names.
- **Syntax.** The operator set is fixed (docs/syntax.md:43): a project
  can't change how a pattern parses.
- **Std itself.** Search loads all of std either way; equations are made
  in each file's own scope, "whoever asks" (`equations.rs:6383`); doc
  summaries come from std's text; a std result's import line doesn't look
  at the scope (`import_line`, `search.rs:1063`).
- **Order.** Std's files load in another order without the project, so
  DefIds differ; ranking ends with the full name (`search.rs:692`), so the
  order of results doesn't. Two lists follow candidate order: the
  out-of-budget warning's names and the internal-error list. Stage 4 sorts
  both by name, so they don't either.

What does change: the "the project doesn't check" summary on stderr
(`unchecked_summary`, `main.rs:4906`) can't be printed for a project that
wasn't checked. Analysis errors (a namespace clash) still are, since the
scan's analysis still runs (`analyse_scan`, `project.rs:1326`), and the
search log's namespace list is the same. That is D3769.

The differential test: `--json --limit 100000` byte-identical with and
without the skip, in `aoc/` and in a probe project with the shadowing
cases above (`length`, `Pair`, a project constructor, a qualified
`Probe.Types.length`), on SW-4935's six queries.

### 4.4 Reading the project through the scan

When the project is loaded, `search` still parses every file
(`analyse`), where `check` reads the cached scan and parses only the
namespaces it checks (`load_project_sources_for`, `project.rs:90`,
SW-4813). Using the scan in `search` (and in `audit`, `main.rs:5108`, and
`load_main`, `main.rs:3588`, which do the same) saves the parse: 175 to 207 ms in
aoc/ (measured for `check` in SW-4813). It is needed for §4.2 anyway.
Measured once built (SW-4953, 27 Nov 2026): no saving in `search` or
`audit` (3.03 s and 3.05 s; 5.65 s and 5.57 s, within noise). `search`
loads every namespace, and a namespace the scan only sketched is parsed
when it loads, so the parse moves rather than goes. The saving comes with
§4.2's project skip.

## 5. Estimates and the end state

Shares and the 1.49 s, 2.25 s and 2.38 s baselines are measured
(SW-4935); the savings are estimated from them as shown.

| Change | Saves | Basis |
|---|---|---|
| Equations from the cache (trusted) | −0.43 s | 0.51 s made, less 0.08 s replay at the measured 27 µs a definition |
| Folded type index from the cache | −0.14 s | 0.16 s, less about 0.02 s to read |
| Skip the project (`--in Std`) | −0.76 s in aoc/ | 2.25 − 1.49 s, measured |
| Scan instead of a full parse | −0.18 s when the project loads | SW-4813's measurement for `check` |
| `Float.sw` from the cache (SW-1204, separate) | −0.21 s | 14% |

| Case | Today (measured) | End state (estimated) | With SW-1204 |
|---|---|---|---|
| std only, `--in Std` | 1.49 s | 0.92 s | 0.72 s |
| aoc/, `--in Std` (Matt's) | 2.25 s | 0.94 s | 0.74 s |
| aoc/, a query naming project types | 2.38 s | 1.63 s | 1.43 s |
| language server, after its first search | (not built) | tens of ms | |

What is left of the std-only 0.72 s is replaying all of std (0.28 s), the
session's start and the process. Below that needs search to load less
than all of std, which changes what it can find; not proposed.

## 6. Decisions for Matt

**D3768: trust cached equations as other cached std declarations are?**
[rec: yes, the trusted path]

- *The problem*: every warm search and `doc` spends about half a second
  (0.51 s, measured) re-making std's 3,009 equation definitions.
- *The change*: keep them in the check cache and replay them without the
  kernel checking them again, as every cached std theorem has been since
  D1660. The alternative is replaying them through the kernel's checking
  calls: elaboration is skipped but every proof is checked again, saving
  less (not measured: the profile doesn't split the two).
- *The risk, plainly*: if the cache key misses an input, or the encoder
  has a bug, a search could list, and `search --at` could check a
  suggested proof with, an equation this build would have stated
  differently or not made, and no kernel would have checked it in this
  run. The dependency hashes (§2.3, 5) mean it can only be one this
  build's kernel accepted against exactly these definitions. That is the
  same exposure every cached std theorem has today, caught the same way:
  `--no-cache` checks everything, `Stats::refused` counts refusals, and a
  differential test compares cached and fresh output.
- *What it should do*: −0.43 s a search (estimated), for `search`,
  `search --at` and `doc`. `check` is left as it is (§2.5).

**D3769: under `--in Std`, leave the project out when no query name can
reach it?** [rec: yes]

- *The problem*: in a project, `search --in Std` loads every namespace
  (0.76 s in aoc/, measured) only so that a pattern can name project types.
- *The change*: load it only when a name in the query is one the project
  declares (§4.2); otherwise search std alone. Results are identical
  (§4.3), including patterns like `List Point → Nat`.
- *The one visible difference*: when the project is left out, a project
  namespace that doesn't check is no longer reported on stderr under
  `--in Std`; analysis errors still are.
- *What it should do*: Matt's `aoc/ --in Std` search from 2.25 s to about
  1.5 s with this alone, about 0.94 s with §2 and §3 (estimated).

## 7. Plan

Estimates are agent time, from similar past lanes: SW-4814 (the core's
entry, Opus, 46 min against 60), SW-4812 (name index cache, Opus, 23 min),
SW-4813 (the scan, Sonnet, about 30 min with review fixes), SW-4935 (this
profile, Opus, 22 min).

| Stage | Lane | Model | Estimate | Needs |
|---|---|---|---|---|
| 1 | The scan in `search` and the other two `analyse` callers (`audit`, `load_main`) (§4.4); `--json` identical in aoc/ | Sonnet | 20 min | nothing |
| 2 | The equations entry, segments, replay checks §2.3, writing from `generate_deferred_equations`; differential test (std `search --json` and `doc` cached against `--no-cache`, `refused` 0; a changed dependency hash is a miss) | Opus | 50 min | D3768 |
| 2r | Review of stage 2's trust argument and key | Fable | 20 min | stage 2 |
| 3 | The folded index: memo by content hash, its section of the equations entry, the per-candidate differential test | Sonnet | 30 min | stage 2 |
| 4 | The project skip (§4.2), the out-of-budget and internal-error lists sorted by name, the probe-project differential test | Sonnet | 30 min | stage 1, D3769 |

Stages 1 and 2 can run together (one is the CLI, the other the cache);
4 follows 1, as both edit `search` in `main.rs`. Each lane measures before
and after (warm, best of 3) and logs it in docs/performance/log.md.

**Other lanes.** SW-4944 is changing search's matching in
`crates/driver/src/search.rs`; only stage 4 touches that file (the query's
names, the two sorted lists), so it should follow SW-4944. SW-4945's
language server search keeps a session: stage 3's memo lives on the
elaborator, and stage 2's entries are read through the same store, so
both serve it without a separate design.
