# Proposal: the elaborator's state, by lifetime

**Status:** Draft 1, 3 November 2026 (SW-1137, D2250). A design note only:
nothing is built until Matt has decided. Written at `b9627b79`. It builds
on the architecture review's issue 2, §4 and step 8
([architecture-review.md](../research/architecture-review.md)). Claims about
the code were checked by reading it. Measurements say what was run and where;
estimates are marked as estimates. The benchmark is in
[elaborator-state/bench/](elaborator-state/bench/) (a standalone crate, not a
workspace member).

## 1. Summary

**The problem.** The `Elaborator` has 116 fields, 47 of them `RefCell`, plus
22 fields of `Globals` and about a dozen thread-locals and process globals.
Six mechanisms walk that state, and each keeps its own list of fields:
undoing a failed attempt (`undo::Snapshot`), per-declaration cleanup
(`clear_metas`, called from about 65 sites, plus other clears), a library
file loaded in the middle of a unit (`library::Context`), rewinding (`rewind::Mark`), the
check cache (`cache/mod.rs`'s `Before`, `encode`, `decode`, `replay_tables`)
and the canonical dump (`cache/dump.rs`). Only rewinding is checked by the
compiler. So a new table can be wrong in five ways the compiler doesn't see.
SW-1128 was one (three tables missing from cache and dump). SW-1135 is
probably another (`equations_done`), and this note finds one more
(`total_rows`, §2.5). SW-1129 is the same class: state kept outside the
object, which no mechanism sees.

**Recommendation (the end state).**

1. **Lifetime components.** The `Elaborator` is made of nine structs, one
   per lifetime: `Options`, `Kernel` (today's kernel half of `Globals`),
   `Tables`, `Session`, `Unit`, `Decl`, `Attempt`, `Caches` and
   `Presentation`. A field's lifetime decides which struct it is in. Each
   mechanism is a method that destructures its component exhaustively, so a
   new field doesn't compile until every mechanism says what it does with it
   (this is the review's §4 proposal).
   Two mechanisms stop being lists altogether. Per-declaration cleanup
   becomes `self.decl = Decl::default()`, and a library load in the middle of
   a unit becomes `mem::replace(&mut self.unit, ..)`.
2. **A few table kinds, each with its policy built in.** The checked tables
   are not stored as bare `HashMap`s. Each is one of four kinds:
   `GrowVec` (grows only, indexed by load order: marked by length),
   `OwnedBy<Id, V>` (rows written only by the unit that declares the id:
   rewound by cutting at an id, encoded as the rows at or past the unit's
   start, and the "an older row changed" check is built into the type),
   `Logged<K, V>` (any row may change: an undo log like `nav::Logged`), and
   `Derived` (a cache: cleared, never encoded). A table states its kind
   once, where it is declared. The kind supplies mark, rewind, which rows to
   encode, and the dump of the whole table.
3. **No persistent data structures as the general representation.** The
   measurements (§5.2) show what they cost: a lookup in a 30,000-row
   name-keyed map takes 1.3-2.8 times as long with `imbl` or `rpds` as with
   today's `HashMap`, and an indexed read from a persistent vector takes 10
   times as long as from a `Vec`. The workflows we have don't need what
   persistence buys, which is many live versions branching from each other.
   They mark and rewind in stack order, and undo logs serve that for a
   fraction of the time and memory (§5.2: 7 MB against 68 MB for `imbl` and
   341 MB for today's copies, for 200 marks of a table growing to 30,000
   rows).
4. **One shared, frozen library base** (later, behind a measurement). This is
   for the workflows that do need two live states: the proof-action search's
   second session, the tests' repeated library loads (SW-1109), and
   parallel namespaces some day. Once the library is loaded, its state is
   frozen into an `Rc` that sessions share, and each session writes only to
   its own overlay. This is Lean's staged map (`SMap`) and Idris 2's staging
   area, applied at the one place where a fork is needed.
5. **No session state outside the object.** `unify.rs`'s seven thread-locals
   go into `Attempt`. `queue.rs`'s 26 counters and `unify::MET_UNFILLED` go
   into a `Stats` struct in `Session`, and the kernel's rejection log into a
   test hook on the session. What stays process-wide is listed, with the
   reason (§2.8).

**What it costs at run time:** nothing measurable on a check (an
estimate from §5.2; it doesn't change any lookup). A language
server's marks get cheaper in both time and memory (§4.3). **What it fixes as
a class:** the next table of any of the four kinds can't skip cache, dump or
rewind. A table that doesn't fit a kind needs a hand-written impl, and the
compiler forces that impl to exist.

**Migration:** ten steps (0-9), each one lane, each keeping `main` working and
covered by the differential tests `crates/driver/tests/rewind.rs` and
`check_cache.rs` (§7). **Decisions for Matt:** §8.

## 2. Workflows over the state

The terms used below:

- A **unit** is what is elaborated as one piece and cached as one entry: a
  standard library file or a project namespace.
- A **mark** is a value from which a mechanism can later restore the state.
- **Stack order** means a mark is only restored while no older mark has
  been restored since it was taken.

### 2.1 Speculative attempts (`undo.rs`)

*What it is.* `transaction`/`attempt` runs one way of elaborating something
and undoes it if it fails, so that another way can be tried. There are 126
call sites in elab (`transaction(`, `attempt(`, `Snapshot::take`).
*How often:* not measured (no counter exists). It happens on every
application with an expected type, every dot call, every literal default,
every instance search step and every `auto` alternative. The estimate is
thousands of snapshots for a heavy declaration and about 10^5 to 10^6 for an
AoC check. *Latency:* has to be close to free. A snapshot today is 18
integers, and a restore costs O(the changes made since).

*What it needs.* Every piece of inference state is restored: metavariable
solutions (`Globals::meta_trail`), metavariables created since, and 15
per-attempt tables (obligations, row metas, drafts, local keys, meta names,
goals, branch errors, `W-NO-EFFECT` warnings and so on). The queue has its
own log. Resource budgets and `instance_steps` are deliberately *not*
restored ("steps spent aren't refunded").

*What goes wrong today.*

- The list is kept by hand. `Snapshot` names 18 things; the `retain` calls
  in `restore` name 9 more maps keyed by metavariable (3 of them in
  `Globals`). A new per-attempt table that isn't added leaks out of undone
  attempts, and nothing fails to compile.
- `unify.rs`'s thread-locals (`POSTPONED`, `RIGID_DIVERGENCE`,
  `AWAITED_HELPERS`, `SOLVING_ARGUMENTS`, `LOSSY`, `PENDING`, `WAITING`)
  live outside the object. Only `LOSSY` is restored, and only because
  `restore` remembers to call `unify::forget_lossy_since`. The others are
  dynamically scoped flags, and they are correct only because each
  function that sets one also resets it. `RIGID_DIVERGENCE` is read and
  reset by `take_rigid_divergence` before and after a body (`lib.rs:2797`,
  `:2807`). A flag set inside an undone attempt survives the undo. That
  may be intended (any such meeting in the body counts), but nothing says
  so, and a nested session on the same thread (§2.7) would see the outer
  one's flag.
- `dot_failed` is keyed by `(call, metas.len(), trail.len())`, which stands
  for "the same metavariable state". That holds only while lengths identify
  a state, which a restore followed by new work breaks (a new trail with
  the same length). This is plausible but unverified; it is a cache, so the
  worst case is a missed retry, not an unsound result.
- Several `restore` steps are `retain` over a map keyed by metavariable,
  which is O(table size), not O(changes). The maps are per-declaration and
  small, so this is not a measured problem.

### 2.2 Per-declaration cleanup

*What it is.* Before each declaration, everything left by the previous
one is emptied. `clear_metas` clears 20 things. Other code clears
`local_keys` (4 sites), `local_helpers` (6 sites), `lambda_warnings` (by
`take`) and `branch_errors`. `clear_metas` itself is called from about 65
sites in 17 files.

*What it needs.* Every per-declaration field must be empty at the start of a
declaration and at every mark. *What goes wrong:* four tables are undone by
`Snapshot` but not cleared by `clear_metas` (`goals`, `lambda_warnings`,
`local_keys`, `branch_errors`). Each is emptied somewhere else, by code
that has to remember to do it. `char_patterns`/`char_proofs` are never
emptied except by rewind, and grow over the whole session. Nothing asserts
"empty" at a mark except `metas.is_empty()`.

### 2.3 A library file loaded inside a unit (`library.rs`)

*What it is.* A library file can be loaded while a project namespace is
being elaborated. `library::Context` saves the current unit's
`module`, `namespace_root`, `globals.module`, imports, `file_mode`,
`loading_prelude`, `warnings` and `lambda_warnings`, elaborates the library
file, and puts them back. *What it needs:* everything scoped to "the unit
being elaborated" is swapped. *What goes wrong:* it is one more hand-written
list. It is written out twice (`library.rs:1149` and `:1231`), and the next
per-unit field must be added to both.

### 2.4 Rewind: language server and cancellation (`rewind.rs`, `driver/src/live.rs`)

*What it is.* `LiveProject` loads every library file, takes a base mark, and
then takes one mark before each namespace it checks. All of them are kept
(`Step::mark`). For `aoc` that is 207 marks. After an edit, it rewinds to the
mark before the first changed namespace. A check cancelled from another
thread rewinds to the mark taken before it (`cancellable_at`). *Order:*
strictly stack order (`Mark`'s doc says so, and `Globals::rewind` asserts
it). *Latency target:* under 20 ms to cancel (language-server.md §7), and
an edit loop of tens of milliseconds per namespace.

*What it needs.* After a rewind, checking the same text again gives what a
fresh session gives: the same canonical dump, hashes, index and diagnostics.
`rewind.rs` tests exactly that.

*What goes wrong today.*

- **Mark memory.** About 15 tables are copied into every mark: `scope` (all
  its maps), `module`, `instances`, `library`, `helper_keys`, the three
  project tables, `namespace_sources`/`keys`, `replayed_names`,
  `include_locations`, `warnings`, `dot_heads`, `dot_failed`,
  `local_helpers`. The language server keeps a mark per namespace, so the
  memory these copies hold grows with the number of namespaces times the
  size of the tables: quadratic in the project. This is the SW-1052 failure
  (8 of 13 GB of an editor session was copies of `nav`), fixed then for
  `nav` alone. *Estimate:* `scope.entries` alone is a 15,000-30,000-row
  `String`-keyed map for `aoc` (8,780 project symbols in its index plus the
  library). In the benchmark (§5.2), 200 marks of a map of that shape
  growing to 30,000 rows hold 341 MB. In `LiveProject` every mark also
  copies the whole library's names, which are loaded before the base mark,
  so the benchmark understates. Together with the other maps,
  `LiveProject` on `aoc` plausibly holds several hundred MB in marks.
  This is not measured; see finding F3.
- **Mark time.** 1.9 ms per mark when measured (language-server.md, "As
  built", on a smaller `aoc`). The bench's copy of a 30,000-row map takes
  0.9 ms. Acceptable at namespace granularity, but never per declaration.
- A rewind restores some per-declaration fields by copying (`recursion`,
  `local_helpers`) even though they should be empty at every mark. This is
  harmless, but it hides the field's real lifetime.

### 2.5 Check cache: encode and replay (`cache/mod.rs`)

*What it is.* After a unit checks without errors, the cache encodes what
the unit added, as a delta against a `Before` snapshot. Declarations are
written by path and content hash, never by load-order id, so the entry can
be replayed into a session whose ids differ. Replay admits the declarations
through trusted admission and extends each side table (`replay_tables`).
*How often:* once per unit per run (289 units in an `aoc` check). Encoding
cost scales with the unit; replay cost is per entry.

*What it needs.* For every table that a later unit reads, three things: the
rows this unit added, an assurance that it changed no older row (or a way to
encode that change), and a way to rebuild the rows on replay with ids
re-mapped. *What goes wrong today:*

- The encoder and decoder are about 1,350 hand-written lines
  (`encode` 1167-1820, `decode`/`replay_tables` 2280-2970), one block per
  field, with no structural link to the tables. SW-1128: `no_finite`,
  `no_decide` and `generated_alls` were rewound but not encoded, so a
  replayed namespace made a later one elaborate differently. SW-1135:
  `equations_done` is in the same position (unconfirmed).
- **New probable instance: `total_rows`** (`lib.rs:634`). It records the
  definitions re-checked with total row variables (D1215). It is rewound by
  `DefId` but neither encoded nor dumped. Later units read it:
  `check.rs:2867` adds a note ("takes only total callbacks") to an error at
  a call, and `nav.rs:1097` adds a line to the hover type. After a replay,
  both would be missing for a definition in a replayed namespace.
  Unconfirmed; finding F1.
- `Before` copies `scope.entries` and `helper_keys` for every unit. That is
  another full copy of the largest table, 289 times in an `aoc` check (an
  estimated 0.5-1 ms each from the bench, so 0.1-0.3 s of a 69 s check).
- The "older rows unchanged" check (`by_data`, `instances`) is a run-time
  comparison of lists. Adding a new by-data table to it is also a step done
  by hand.

### 2.6 Canonical dump (`cache/dump.rs`)

*What it is.* A text of everything later code reads, compared between a
fresh session and one loaded from cache (`check_cache.rs`) or rewound
(`rewind.rs`). It is deliberately written separately from the encoder, so
that a field the encoder gets wrong shows up as a difference. *What it
needs:* every table that a later unit reads. *What goes wrong:* it is a
hand-written list too. `equation_skips` is encoded but not dumped, so a bug in
how it is encoded can't be seen. `total_rows` and `equations_done` are in
neither. The dump only covers what someone remembered to add.

An important point for §4.2: the dump prints the **whole live table**, while
the encoder selects a **delta**. If both came from one declaration of the
table's kind, the test would still compare two independent things: the
replayed state against the fresh state, where the fresh one is the
reference. A delta selected wrongly, or a row that decodes wrongly, still
shows up as a difference. What such generation *would* mask is a table
missing from the mechanism altogether, which is why every table must
declare a kind, and why `Tables::dump` destructures `Tables`.

### 2.7 A second session, and forks

- **Proof-action search** (`driver/src/search_at.rs:1556-1569`). It builds
  two fresh `Session`s, one to search and one to check candidates, and each
  loads the file and the library. The second session exists because
  checking a candidate must not disturb the first. *What it needs:* a cheap
  copy of a loaded state. *Today:* `Session` isn't `Clone`, so it pays a
  second library load. The two sessions share one thread, so the
  thread-locals and the queue's counters are shared between them (SW-1129).
- **Tests loading std** (SW-1109). `eager_for_stack` costs about 9 CPU-s per
  load; 136 tests in 17 binaries do it, about 1,220 CPU-s per daily tier.
  Nextest runs a process per test, so sharing within a process doesn't
  help. What would help is either a state that can be loaded from disk faster
  than elaborating the library (or replaying its 82 cache entries), or fewer
  processes. *What it needs from
  the state:* serialising the whole state, or a frozen base (§4.5).
- **Parallel elaboration of independent namespaces** (possible future). This
  would need the shared state to be `Send + Sync` (terms are `Rc` today, so
  that is a core-wide change), a fork per worker, and a merge of each
  worker's additions. The check cache's id-independent entry *is* a merge
  format: a worker's namespace could be replayed into the main session like
  a cache hit. Nothing in this note blocks that, and the frozen base is
  its prerequisite.
- **Playground** (wasm worker). Single-threaded. It cancels by ending the
  worker. It needs only what the CLI needs, within a smaller memory budget.
- **REPL / `eval`.** Expressions are elaborated after a file, against its
  final scope. `standalone_inputs` numbers them. Nothing extra is needed.

### 2.8 State outside the object

| Where | What | Lifetime it really has | Proposed home |
|---|---|---|---|
| `unify.rs` thread-locals (7) | `POSTPONED`, `RIGID_DIVERGENCE`, `AWAITED_HELPERS`, `SOLVING_ARGUMENTS`, `LOSSY`, `PENDING`, `WAITING` | per attempt or the dynamic extent of a call | `Attempt` (`LOSSY` as a trail; the others as fields set by a guard) |
| `unify::MET_UNFILLED` (atomic) | count over the process | per session statistic | `Session::stats.met_unfilled` (the `Unifier` holds `&Stats`) |
| `queue.rs` (26 atomics) | postponement counters, read by tests and `STITCHWORT_TIMINGS` | per session statistic | `Session::stats` (`Elaborator::queue_counts()`); `STITCHWORT_TIMINGS` sums the sessions of the process as each `Stats` is dropped (`timings::add_queue_counts`) |
| `kernel.rs` `RECORDING`, `REJECTIONS` | the kernel's refusals, for the fuzzer | per session, test only | a test hook on the session |
| `timings.rs` `STACK`, `DECLS`, `ROWS`, `DECL_ROWS`, `START` | profiler | process | stays: it measures time spent, rewound work included (as documented) |
| `core::reference` `EQUAL_CALLS`, `value.rs` `PENDING`, `RUNS` | evaluator scratch, test counter | dynamic extent of one evaluation | stays in core (no session meaning) |
| `library::STANDARD`, `std_dir::STD`, `LazyLock` names (`omega`, `ring`, `module.rs`) | constants | process | stays |

## 3. Inventory

Appendix A classifies all 116 `Elaborator` fields. Each row gives the field's
pattern today (in the review's notation: **U** undo, **C** `clear_metas`,
**R** rewound by mark copy or length, **r** rewound by emptying, **s**
ignored by rewind as a setting, **E** mentioned in `cache/mod.rs`, **D** in
the dump), its proposed component, its kind, and a flag where its lifetime
is unclear or mixed. Appendix B does the same for `Globals`. In summary:

| Component | Fields | Lifetime | Mark | Encoded |
|---|---:|---|---|---|
| `Options` | 15 | the session, fixed at construction | none (part of the cache key) | key only |
| `Kernel` (from `Globals`) | 5 of `Globals`' 22 | grows with each unit | lengths | yes (declarations) |
| `Tables` | 21 (+1 unclear) | grows with each unit; read by later units | per kind (§4.2) | yes, per kind |
| `Session` | 14 | project and run bookkeeping | undo log or small copy | no |
| `Unit` | 10 (+2 unclear) | the unit being elaborated | swapped on a nested library load; empty at marks | no |
| `Decl` | 23 (+2 unclear) | one declaration (or group) | `Default` at each declaration; asserted empty at marks | no |
| `Attempt` | 18 (+ 8 from `Globals`, + 7 thread-locals) | one declaration, with speculative sub-scopes | trail / lengths | no |
| `Caches` | 6 (+ `Globals::hashes`) | any; derivable | cleared or cut by id | never |
| `Presentation` | 2 (+ `goals`, shared with `Attempt`) | the session (nav, goals shown, logs) | `nav::Logged` | nav only |

**Fields flagged** (lifetime unclear or mixed; each is a question for the
lane that moves it, not a known bug):

- `total_rows`: read by later units; neither encoded nor dumped (F1).
- `equations_done`: SW-1135.
- `equation_skips`: encoded, not dumped (F2).
- `signature_matches`: written when a declaration's type is elaborated and
  read when its body's matches are lifted. Rewind clears it entirely, and it
  is never encoded. Is it per declaration (then `Decl`) or does a later
  declaration read it (then a table)?
- `pending_run_bodies`: run bodies waiting for their helper to be final.
  They are drained by `lift.rs:1412` and rewound by id. Can one cross a unit
  boundary?
- `tuple_matches`: "a log that only grows", read for termination errors.
  Rewound but not cached. Does a later unit's error ever explain a match
  from an earlier one?
- `char_patterns`, `char_proofs`: emptied only by rewind. They grow over the
  session and survive undone attempts. Probably per declaration.
- `omega_for_auto`: set per module (`module.rs:360`), but rewind treats it as
  a setting.
- `recursion`, `local_helpers`: copied into every mark, though they should
  be empty between loads.
- `Globals` as a whole: one struct of three lifetimes (review issue 3).

## 4. The recommended design

### 4.1 Components

```text
Elaborator
├── options: Options          settings and test switches, set before the first load; cache_key()
├── kernel:  Kernel           (Globals' Env half) defs, datas, builtins, registry, unfinished
├── tables:  Tables           checked tables later units read (scope, records, instances, ...)
├── session: Session          project tables, include files, cache bookkeeping, stats (Stats: the queue's and the unifier's counters)
├── unit:    Unit             module state, namespace root, imports, file mode, warnings
├── decl:    Decl             per-declaration scratch (Default)
├── attempt: Attempt          MetaStore (Globals' meta half) + per-attempt tables + unify state + instance_steps
├── caches:  Caches           derivable memo tables
└── present: Presentation     nav recorder, goal snapshots, counterexample log
```

Each component lives in `elab/src/state/`; its fields are `pub(crate)` (`Options`' are public, for hosts and tests). The
mechanisms become methods with exhaustive destructuring:

| Mechanism | Who implements it | Shape |
|---|---|---|
| Undo an attempt | `Attempt::mark()` / `restore(m)` | trail lengths; `restore` destructures `Attempt` |
| Per-declaration cleanup | `Decl`, `Attempt` | `*decl = Decl::default(); attempt.reset()`; nothing to list |
| Nested library load | `Unit` | `let saved = mem::take(&mut self.unit); …; self.unit = saved` |
| Rewind | `Kernel`, `Tables`, `Session`, `Unit`, `Presentation`, `Caches` | each `mark()`/`rewind(&m)`; `Elaborator::Mark` is a tuple of them. A `Unit` mark keeps a copy of the fields that outlive a unit (the last module, the namespace root, warnings, file mode); `Session`'s copies the bookkeeping a later load can change and leaves its counters. `Decl` is asserted empty at a mark and reset on rewind; `Attempt` is reset. `Options` is left alone |
| Encode / replay | `Tables` (and `Kernel` for declarations) | `Tables::encode(&self, since: &TablesMark, w)` destructures `Tables`; each field's kind does the work |
| Dump | `Tables`, `Kernel`, `Presentation` | `dump(&self, out)` destructures each |
| Cache key | `Options` | `cache_key()` destructures `Options` and gives the settings part of `Elaborator::modes()`; the rest of the key's text is the kernel's native switches and the navigation tag |

The `Ctx<'e>` hub stays as it is: `cx.e.attempt.obligations` instead of
`cx.e.obligations`. The `RefCell`s stay where code with `&Elaborator`
mutates them. They move from `Elaborator` onto the component's fields, so
the count doesn't change. Interior mutability isn't the problem; the
missing lifetime is.

### 4.2 Table kinds

Every `Tables` field is one of four kinds. Each kind is a small generic type
in `state/table.rs`:

| Kind | Type | Invariant | Mark / rewind | Encode (delta since mark) | Fields today |
|---|---|---|---|---|---|
| Grows only, by load order | `GrowVec<T>` | push only | length / truncate | rows past the mark's length | `tests`, `abilities`, `lifted`, `equations_done`, `tuple_matches`, (`namespace_defs`) |
| Owned by an id | `OwnedBy<Id, V>` | a row for id `i` is written only while the unit that declared `i` is elaborated: `insert` asserts `i >= unit_start` | id cut (`retain(i < mark)`) | rows with `i >= start`, ids written as path + hash | `records`, `no_eq`, `no_show`, `no_ord`, `no_finite`, `no_decide`, `generated_alls`, `interfaces`, `data_owners`, `match_columns`, `total_rows`, `equation_skips` |
| Any row may change | `Logged<K, V>` | none | undo log (`nav::Logged`, generalised): O(1) mark, O(changes) rewind | rows changed since the mark: the log *is* the delta | `scope` (its maps), `instances`, `helper_keys` |
| Derived | `Derived<T>` | correct if emptied at any time | cleared, or cut by id | never | `result_heads`, `performs`, `cong_candidates`, `decision_order`, `dot_heads`, `dot_failed` |

A table that fits none of these implements the `Table` trait itself. The
compiler then forces each method to exist. `Scope` is the main candidate: it
is a struct of maps, and the cache encodes it from the log of scope
operations `cache_before` starts (`ScopeOp`). With `Logged` inside `Scope`,
that log and the undo log become the same thing.

`OwnedBy`'s assertion turns a check that `encode` makes by hand at run time
("a row for an older data type changed") into an invariant that every write
upholds. It also catches the bug at its source, the write, in every test
rather than only in a cached run.

How a kind serves each mechanism:

```rust
trait Table {
    type Mark;
    fn mark(&mut self) -> Self::Mark;
    fn rewind(&mut self, m: &Self::Mark);
    /// What a unit added since `m`, by path and hash (cache/codec's Refs).
    fn encode_since(&self, m: &Self::Mark, e: &mut Encoder) -> Result<(), String>;
    fn replay(&mut self, rows: Decoded<Self>, ids: &IdMap);
    /// The whole table, canonically: written independently of the codec.
    fn dump(&self, out: &mut String);
}
```

`encode_since` and `dump` for `GrowVec<T>` and `OwnedBy<Id, V>` are written
once per kind, generic over a row trait (`Row: Encode + Decode + Dump`). The
row trait is implemented per row type. Its `dump` stays independent of its
`encode` (one writes text, the other bytes through `codec`), as the
review asked. §2.6 explains why generating which rows are dumped and which
are encoded from the kind doesn't weaken the differential test.

**No macro.** A `macro_rules!` or derive could generate the
`Tables` struct and its impls. It would save about 100 lines, but it would
hide the exhaustive destructuring that is the point, and a proc macro would
add a crate to the build (SW-1091 found none today). Plain structs, plain
destructuring, generic kinds.

### 4.3 Data structures: what each lifetime uses

| Lifetime | Structure | Mark cost | Why not persistent |
|---|---|---|---|
| `Kernel` defs/datas | `Vec`, by id | a length | eval indexes `defs` on every unfolding: `imbl::Vector` reads take 12-20 ns against 1-1.5 ns (§5.2) |
| `Attempt` metas + trail | `Vec` + trail of old solutions | a length | eval reads metas constantly; the trail is O(1) to mark and O(changes) to undo, which persistence can't beat |
| `Tables` | four kinds (§4.2) | O(1) | rewinds are in stack order (§2.4); logs serve that with 7 MB where `imbl` holds 68 MB (§5.2) |
| `Session` | small maps, `Logged` where copied today | O(1) | as above |
| `Unit`, `Decl` | plain fields | none: empty at every mark | not marked |
| `Caches` | `HashMap`/`Vec` | none: cleared or cut by id | not marked |

**What changes at run time** (estimated from §5.2 and §2):

- A check: no change in lookups. `Logged` adds one `HashSet` insert and one
  `Vec` push per *first* write of a key after a mark. Outside a language
  server no marks are taken and nothing is logged (as `nav::Logged` does
  today). The `Before` copies of `scope.entries` per unit (§2.5) go, which
  saves an estimated 0.1-0.3 s of a 69 s `aoc` check.
- A language server: marks go from O(tables) (about 2 ms and megabytes
  each) to O(1). Rewind costs O(changes since the mark). The bench's
  version of this: 0.8-4 ms against 0.8-3 ms for putting a copy back.
  Marks' retained memory drops from an estimated hundreds of MB to tens
  (§5.2's 341 MB → 7 MB for one map).

### 4.4 How it addresses SW-1128, SW-1135 and SW-1129 as a class

- **SW-1128 / SW-1135 / F1.** Each was a table rewound correctly but
  forgotten by encode and dump. After step 5 of §7, a table in `Tables` has a
  kind, and `Tables::encode`/`dump`/`rewind` each destructure `Tables`. A
  new field can't compile until every mechanism handles it, and for a
  table of a known kind the handling is supplied by the kind. A new table
  can still be put in the wrong component, say `Session` when later units
  read it. That is a design error the review of a diff can see ("does a
  later unit read this?"), and the component's doc comment asks it.
- **SW-1129.** Thread-locals and process counters become fields of
  `Attempt` and `Session`, so two sessions on one thread no longer share
  them. Every mechanism sees them because they are in the destructured
  structs.
- **The class in general.** Per-declaration and per-unit state can no
  longer leak, because it is rebuilt by `Default` instead of cleared by a
  list. Caches can be shown to be caches by a test mode that clears
  `Caches` before every declaration and compares the dump (§7 step 4).

### 4.5 Forks: the frozen library base

Some workflows need two live states that share a past: the proof-action
search's second session, an in-process std snapshot (SW-1109), parallel
namespaces. Persistent structures are the general answer to that, but §5.2
prices them at 1.3-10 times today's lookup costs, everywhere, for workflows
that fork in one place: after the library has loaded.

**The proposal.** A `Session` can be frozen after its library is loaded.
`Kernel` and `Tables` move into an `Rc<Frozen>`, and the session continues
with an empty overlay over it. A lookup tries the overlay and then the base.
For `Vec`s indexed by id, ids below the base's length go to the base (one
comparison). For maps, the overlay is probed first and then the base. An
overlay row can shadow a base row (inferred: the cache's check that an
instance's `(def, valid)` didn't change suggests rows can change), which Lean's
`SMap` forbids but we would allow: the overlay is always probed first.
Forking is `Rc::clone` plus an empty overlay. Rewinding to the base is
dropping the overlay. That replaces `LiveProject`'s base mark too, since the
library is already loaded before it.

**Costs.** Estimated: one extra branch per id lookup and one extra probe per
miss in name lookups (a miss is 17-31 ns in §5.2). Unmeasured. *Benefits:*
the search's second session is free, and a test binary can build one
`Frozen` and fork it per test. That doesn't help under nextest's process per
test, but it combines with SW-1091's "fewer test binaries" or with
serialising `Frozen` to disk, which is a cache entry for the whole library.
It is also the shape that parallel namespaces would need, with `Arc` instead
of `Rc`.

**Why it is later, and gated.** It touches every lookup in `Kernel` and
`Tables`, which is hot code. The components and kinds of §4.1-4.2 come first
and are worth having on their own. The frozen base should start only after a
measurement shows the fork's value (the search's second-session cost, and
SW-1109's per-load cost after the components land).

### 4.6 Interaction with the `Globals` split (review issue 3, step 9)

`Globals` today is `Kernel` (defs, datas, builtins, registry, unfinished),
a cache (`hashes`), a backend side table (`erasure`), the unit's
`module`, `Attempt`'s meta store (metas, meta_trail, frozen_metas, lifted_calls, unfilled_placeholders, placeholder_syntax,
waiting_literals, print_labels, meta_epoch), and session or operation state
(budget, transparent, glue, failed_mentioned, apart_sets). This note's
components are the destination of that split:

- the private kernel `Env` is `Kernel`'s content;
- the `MetaStore` the review proposes is the core of `Attempt`, which owns
  the trail and so `undo` and `clear_metas`;
- `erasure` and `Data::js` become `OwnedBy<DataId, _>` tables, keyed by data
  type and encoded by kind, instead of kernel fields.

**Order:** move the elaborator's own `Attempt` fields into `Attempt` first
(step 1). The meta store's move out of `Globals` (review step 9) then becomes
moving 9 fields into a struct that already exists. Its hard part is how
`eval` reads solutions (a `&dyn MetaLookup` or a store argument), and that
is review step 9's design question, not this note's.

### 4.7 Interaction with persistence of std (SW-1109)

The check cache already serialises every library file's delta by path and
hash, so a whole-library snapshot exists today as the set of those entries.
`Session::eager_for_stack` doesn't use it: `Session::start` sets no check
cache, so each of those tests elaborates the library (about 9 CPU-s,
SW-1109). Giving those sessions a cache directory would turn that into a
replay, which still admits every declaration and rebuilds every table
(not measured here). Two ways to go further, both enabled by this design:

1. *In a process:* fork a `Frozen` base (§4.5). It is free, but only within
   one process.
2. *On disk:* serialise `Frozen` itself (ids and all, since it is the base
   every session starts from, so id independence isn't needed), and load it
   by bulk deserialisation without admission. This is Lean's `.olean`
   approach. With table kinds, the serialiser is generic per kind, just as
   `encode_since` is. Its soundness story is the same as stage 3's trusted
   replay (D1660). It is a separate design note if SW-1109 wants it.

## 5. Options considered, with costs

### 5.1 The options

| | Option | Fixes "forgotten in a mechanism" | Mark cost | Lookup cost | Forks | Effort |
|---|---|---|---|---|---|---|
| a | Lifetime components, exhaustive destructuring | yes, for the five lists (compile time) | unchanged | unchanged | no | L (incremental) |
| b | Persistent maps and vectors throughout (`imbl`/`rpds`) | partly: a mark is one clone of the whole state, so rewind can't forget a field, but encode and dump still can | O(1) | 1.3-2.8× (maps), ~10× (vectors) | yes, any shape | L, plus a dependency, plus a performance risk in eval |
| c | Hybrids: lengths for grow-only, id cuts, undo logs where copied today | no, on its own | O(1) | unchanged | no | M |
| d | Derived policies: table kinds (or a registry) supply rewind, encode, dump | yes, for tables of a known kind | per kind | unchanged | no | M, on top of a |
| e1 | A registry of tables (Rocq's `Summary`, Lean's env extensions): each table registers freeze/unfreeze/export functions at run time | yes, if registering is the only way to create a table | per table | an indirection per access (extension index) | yes (freeze = copy all registered) | M; loses static types unless generic |
| e2 | Query-based incremental (salsa) | n/a: replaces the mechanisms | n/a | memo lookups | yes | XL: elaboration's side effects (metas, lifting, generated helpers) don't fit pure queries; language-server.md §2 already reached this conclusion |
| e3 | Frozen base + overlay (Lean's `SMap`, Idris 2's staging) | no | O(1) for the base | one extra branch or probe | yes, at the base | M-L, later |

**Recommended: a + c + d now, e3 later behind a measurement.** b is rejected
as the general representation. e1 is a + d done at run time instead of
compile time. It suits Rocq and Lean, where plugins add tables the core
doesn't know about. We have no plugins, so the compile-time version is
strictly better: no indirection, and an omission is a compile error rather
than a test failure.

### 5.2 Measurements

`docs/proposals/elaborator-state/bench/` (from that folder: `nix develop
<repo root> -c cargo run --release`; about 6 s). It was run on this Mac on 3 November 2026 at
a load average of 20-37 (other lanes were running), best of 3 per cell, two
runs. The rows below are from the first run. Where the two runs disagreed by
more than 30% the range is given. Keys are shaped like scope keys
(`Aoc.Year2024.Day06.Proofs.lemma123`), values are 24 bytes like `(Global,
Span)`, the hasher is `stitchwort_core::collections`' Fx-style hasher for
all three maps, and the persistent maps use `Rc` pointers (archery `RcK`).
Bytes are live heap bytes from a counting allocator.

**Hash maps keyed by name.** ns per operation; "mark" is a clone:

| map | rows | insert | hit | miss | mark (clone) | heap / row | write just after a mark |
|---|---:|---:|---:|---:|---:|---:|---:|
| std `HashMap` | 1,000 | 83 | 18 | 16 | 25 µs | 134 B | 96 |
| `imbl` 7.0.2 | 1,000 | 79 | 30 | 27 | ~0 | 270 B | 121 |
| `rpds` 1.2.1 | 1,000 | 134 | 34 | 21 | ~0 | 184 B | 169 |
| std `HashMap` | 10,000 | 71 | 22 | 19 | 0.26-0.52 ms | 115 B | 149 |
| `imbl` | 10,000 | 58 | 29 | 18 | ~0 | 139 B | 229 |
| `rpds` | 10,000 | 145 | 45-86 | 27 | ~0 | 200 B | 213 |
| std `HashMap` | 30,000 | 85 | 37-87 | 17 | 0.9-1.6 ms | 143 B | 407 |
| `imbl` | 30,000 | 109 | 102 | 31 | ~0 | 247 B | 568 |
| `rpds` | 30,000 | 191 | 129-149 | 34 | ~0 | 185 B | 242 |
| std `HashMap` | 100,000 | 111 | 121-188 | 26 | 3.5-4.2 ms | 100 B | 1,339 |
| `imbl` | 100,000 | 199 | 176-235 | 24 | ~0 | 285 B | 592 |
| `rpds` | 100,000 | 359 | 263-293 | 43 | ~0 | 197 B | 287 |

At the sizes that matter (10,000-30,000 rows), a persistent map's hit costs
1.3-2.8 times as long, and it needs 1.3-2 times the memory per row. A miss
costs about the same. (The std map's "write just after a mark" grows with
size because of cache misses in a freshly cloned table.)

**A language server's marks.** 200 marks, one per namespace, all kept, each
namespace adding `rows/200` names. "Build + marks" is the total time to
grow the table and take every mark. "Rewind" puts back the middle mark:

| rows | how | build + marks | memory held | rewind to the middle |
|---:|---|---:|---:|---:|
| 30,000 | copy at each mark (today's scope) | 82 ms | 341 MB | 0.8-1.3 ms |
| 30,000 | `imbl`, clone at each mark | 18 ms | 68 MB | 0.06 ms |
| 30,000 | undo log (`nav::Logged`) | 5 ms | 7 MB | 0.8-1.0 ms |
| 100,000 | copy | 324-336 ms | 1,157 MB | 3.1-3.5 ms |
| 100,000 | `imbl` | 71-87 ms | 222 MB | 0.16-0.19 ms |
| 100,000 | undo log | 16-19 ms | 21 MB | 4.1-5.5 ms |

A persistent map's marks are not free in memory. Each namespace's writes
copy a path of 64-wide nodes, and every mark keeps its own paths alive. The
undo log keeps one entry per changed key. Rewinding is where persistence
wins (O(1)), but a rewind of a few ms is within the language server's
budget, while 341 MB is not.

**Vectors indexed by id** (96-byte rows, like `Def`):

| rows | `Vec` push | `Vec` get | `imbl::Vector` push | `imbl::Vector` get |
|---:|---:|---:|---:|---:|
| 10,000 | 2.9 ns | 0.7 ns | 8.2-8.8 ns | 12-13 ns |
| 100,000 | 8.8-9.8 ns | 1.5-1.7 ns | 8.9-9.1 ns | 19.7-24.3 ns |

`Globals::def` and `metas` are read on every unfolding and every
metavariable lookup in eval. A tenfold read cost there is not a candidate.

**Sizes from `aoc`** (release CLI from `main`, `check --no-cache` in this
worktree's copy, `STITCHWORT_TIMINGS=1`): 289 units (82 library files, 207
namespaces), 14,950 declarations, 51.5 s of elaboration and 16.8 s of
kernel time, 68.7 s wall, 1.59 GB peak resident. `check --index` reports
8,780 project symbols and 289,715 references. The postponement counters
(`queued 1257, resumed 1095, …`) are those `queue.rs` keeps as globals.
What I didn't count: rows per table and snapshots per check (no counter
exists; F4).

**Crate survey** (crates.io API, 3 Nov 2026; docs.rs for `imbl`):

| Crate | Latest | Last release | Notes |
|---|---|---|---|
| `im` / `im-rc` | 15.1.0 | April 2022 | Unmaintained (no release in 4.5 years); superseded by `imbl` |
| `imbl` | 7.0.2 | September 2026 | Maintained fork of `im`. HAMT `HashMap`, B+tree `OrdMap`, RRB `Vector`; generic over `Rc`/`Arc` via `archery` (`GenericHashMap<K, V, S, P>`); the docs say its `HashMap` is "nearly as fast" as std, which §5.2 measures as 1.3-2.8× on hits at 10,000-30,000 rows |
| `rpds` | 1.2.1 | May 2026 | Maintained. HAMT `HashTrieMap`, red-black `RedBlackTreeMap`, `Vector`, `List`; `Rc` by default, `Sync` variants. Slowest inserts here, but the cheapest write just after a mark |
| `archery` | 1.2.3 | August 2026 | Pointer abstraction both use |

If a persistent map is ever wanted (for example, if forks turn out to be
needed somewhere other than at the library base), `imbl` with `RcK` is the
choice: it is maintained, the fastest of the two on reads and inserts, and
has `Rc`/`Arc` behind one type parameter.

### 5.3 How other systems do this

- **Lean 4.** Everything is persistent. `MetavarContext`'s declarations are
  `PersistentHashMap`s, and `Meta.SavedState.restore` restores "the
  backtrackable parts of the state". Its source documents which caches
  survive a restore, and how a cache that does survive is made consistent
  with a rolled-back environment ([Meta/Basic.lean][lean-meta]). The
  environment's constants are a staged map, `SMap`: "store imported entries
  into a hashtable and local entries into a persistent hashtable"
  ([SMap docs][lean-smap]). Lookups are correct "only if we never overwrite
  map₁ entries using map₂". Elaborator tables live in **environment
  extensions**, each registered with `addImportedFn`/`addEntryFn`/
  `exportEntriesFn`, so each declares once how it is imported and exported
  ([EnvExtension docs][lean-ext]). That is option d, done at run time.
  The language server snapshots "the entire state after each command", and
  its doc says "because of Lean's use of persistent data structures,
  incremental reuse of fully elaborated commands is easy". Reuse is
  decided by syntax, because "there is no cheap way to check whether the
  `Environment` is unchanged" ([Language/Lean.lean][lean-lang]).
  *Lesson:* the per-table export policy and the explicit "what survives a
  restore" list are the parts that carry over. Persistence throughout is
  affordable for Lean because its runtime does destructive updates on
  unshared values; Rust's `Rc` structures pay the path copies we measured.
- **Agda.** `TCState` is split by lifetime into `PersistentTCState` ("not
  reverted when an error is thrown or the state is reset"), `PreScopeState`
  ("frozen after scope checking") and `PostScopeState` (metas, constraints,
  signature, warnings), with lenses into each ([Monad/Base.hs][agda]). That
  is option a in Haskell. Which parts `localTCState` reverts was not
  confirmed from the part of the source I read.
- **Idris 2.** The global context is a mutable array. While elaborating
  inside a `branch`, writes go to a persistent `staging` map instead, and
  `commitCtxt` copies the staging area into the array when the outermost
  branch commits (`addCtxt`, `branchCtxt`, `commitCtxt` in
  [Core/Context.idr][idris]). That is a mutable base with an overlay for
  speculation: the shape §4.5 proposes for forks.
- **Rocq.** Every global table is registered as a *summary* with freeze and
  unfreeze functions ("the declaration of global tables, which will be kept
  in synchronization during the various backtracks"). Its value "should be
  pure and marshallable", and `frozen` is "a snapshot of the states of all
  the registered tables" ([library/summary.mli][rocq]). That is a run-time
  registry (e1). Marshallable values are what let Rocq's document manager
  keep states per sentence.
- **rust-analyzer / salsa.** Inputs are set from outside, and tracked
  functions are memoised with the inputs they read, re-used when those
  haven't changed ([salsa overview][salsa]). Not a fit for an elaborator
  whose results include side effects on a shared environment
  (language-server.md §2 made the same call).
  
[lean-meta]: https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Basic.lean
[lean-smap]: https://florisvandoorn.com/LeanCourse24/docs/Lean/Data/SMap.html
[lean-ext]: https://lean-lang.org/doc/api/Lean/EnvExtension.html
[lean-lang]: https://github.com/leanprover/lean4/blob/master/src/Lean/Language/Lean.lean
[agda]: https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Monad/Base.hs
[idris]: https://github.com/idris-lang/Idris2/blob/main/src/Core/Context.idr
[rocq]: https://github.com/rocq-prover/rocq/blob/master/library/summary.mli
[salsa]: https://salsa-rs.github.io/salsa/overview.html

## 6. What this doesn't change

- Load-order ids and rewinding to the first changed namespace stay
  (review §3.2): marks remain at namespace granularity.
- `Ctx<'e>` and `RefCell`-based mutation through `&Elaborator` stay.
- The cache format's design stays: paths and hashes, Merkle keys, trusted
  replay. Moving encoding into table kinds is expected to give identical
  bytes for existing tables (it is a refactor), so `FORMAT` only needs a
  bump where a fix adds a table.
- No `Rc` → `Arc` change.

## 7. Migration

Each step is one lane and keeps `main` working. The differential tests are
the safety net throughout: `crates/driver/tests/rewind.rs` (rewound vs
fresh), `check_cache.rs` (replayed vs fresh) and `hash_stability.rs`. Each
lane runs the targeted tests named and leaves the merge tier to the
orchestrator.

| # | Step | What it fixes | Tests |
|---|---|---|---|
| 0 | **Close the known gaps first.** Reproduce and fix F1 (`total_rows`) and SW-1135 (`equations_done`) like SW-1128; add `equation_skips` to the dump (F2) | the instances | the SW-1128-style tests in `check_cache.rs`, `test:one` on each |
| 1 | **`Attempt`.** Move the 18 per-attempt fields and `unify.rs`'s thread-locals into `state::Attempt`. `Snapshot` becomes `Attempt::mark`/`restore` with exhaustive destructuring; `clear_metas` becomes `Attempt::reset` | undo/cleanup lists; SW-1129's thread-locals | elab's `undo` unit tests, `postponement.rs`, `rewind.rs` |
| 2 | **`Decl` and `Unit`.** Per-declaration scratch into `Decl` (reset by `Default`); per-unit fields into `Unit`, with `library::Context` replaced by a swap. Resolve the flagged fields' lifetimes as they move | per-declaration and nested-load lists | `std_library.rs`, `rewind.rs`, `namespaces.rs` |
| 3 | **`Options` and `Session`.** Settings and test switches into `Options` with `cache_key()`; project and cache bookkeeping into `Session`; `queue.rs`'s counters and `MET_UNFILLED` into `Session::stats`. `include_files` and `core_link_names` are set by the host after the session is built, so they go to `Session`, not `Options` | SW-1129's globals | `postponement.rs`, `check_cache.rs`, `rewind.rs` |
| 4 | **`Caches`**, plus a test switch that clears `Caches` before every declaration; the rewind test runs a sample with it | proves the caches are caches | `rewind.rs` with the switch, on its normal-tier sample |
| 5 | **Table kinds and `Tables`.** `GrowVec`, `OwnedBy`, `Derived`; move the `Tables` fields; `Tables::{mark, rewind, encode_since, replay, dump}` destructure exhaustively. Encoded bytes unchanged (no `FORMAT` bump) | SW-1128's class | `check_cache.rs`, `rewind.rs`, `hash_stability.rs` (bytes unchanged) |
| 6 | **`Logged` for the copied tables.** `Scope`'s maps, `instances`, `helper_keys` and `Session`'s copied maps become undo-logged; `Mark` stops copying; `Before` stops copying `scope.entries`. Measure `LiveProject` memory on `aoc` before and after (F3) | mark memory and time | `rewind.rs` (`STITCHWORT_SLOW=1` once, with Matt's approval), `navigation.rs` |
| 7 | **`Presentation`.** `nav`, `goal_snapshots`, `counterexample_log` | last loose fields | `navigation.rs`, `search_at.rs` |
| 8 | **The `Globals` split** (review step 9, its own design note): the meta store into `Attempt`, `Env` private as `Kernel`, `erasure`/`js` as `OwnedBy` tables | review issue 3 | per that note |
| 9 | **Frozen base** (optional, after measuring): its own short design note with the fork's measured value | SW-1109, search's second session | per that note |

Steps 1-4 are independent of each other once step 1's module skeleton
(`state/`) exists, but they all edit `lib.rs`, so they run one after
another (CLAUDE.md: lanes on the same area don't run side by side). Steps 5
and 6 touch `cache/` and `rewind.rs` and also run one at a time.
*Estimate:* steps 0-7 take about 8 lanes of 1-3 hours each.

## 8. Decisions for Matt

1. **The end state:** lifetime components (§4.1) plus table kinds (§4.2),
   with persistent data structures *not* used as the general
   representation. *Rec: yes.*
2. **No dependency on `imbl`/`rpds` now.** Revisit only if a fork is needed
   somewhere the frozen base can't serve. *Rec: yes.*
3. **Encode and dump supplied by a table's kind**, with the dump printing
   the whole live table and the encoder the delta (§2.6 argues the
   differential test keeps its power), instead of keeping the dump
   hand-written field by field. *Rec: by kind.*
4. **No macro** (neither `macro_rules!` nor a proc macro) for the
   components: plain structs and exhaustive destructuring. *Rec: yes.*
5. **Session counters** (`queue.rs`'s 26, `MET_UNFILLED`) become per-session
   `Stats`, and tests read them from the session. *Rec: yes.*
6. **A "clear caches before every declaration" test switch**, run by
   `rewind.rs` on its normal-tier sample. *Rec: yes.*
7. **The frozen library base** (§4.5) is the fork mechanism for SW-1109
   and the search's second session: a design note after steps 1-6 and a
   measurement. *Rec: yes, later.*
8. **Order with the `Globals` split:** this note's step 1 (`Attempt`)
   before review step 9, so that the meta store moves into a struct that
   already exists. *Rec: yes.*
9. **Step 0 first:** file and fix F1 and SW-1135, and fix F2, before the
   restructuring, so that the refactor starts from a dump that covers every
   table. *Rec: yes.*

## 9. Findings worth filing

- **F1.** `total_rows` (D1215's re-checked definitions) is rewound but
  neither cached nor dumped. Later units read it (`check.rs:2867` note,
  `nav.rs:1097` hover). Probably drops the note and the hover line after a
  replay. Reproduce like SW-1128.
- **F2.** `equation_skips` is encoded but not in the canonical dump, so the
  differential test can't see an encoding bug in it.
- **F3.** `LiveProject` keeps a full copy of `scope`, `module`, `instances`,
  `library` and about ten more tables in each namespace's mark: estimated
  hundreds of MB on `aoc` (207 marks), SW-1052's failure for the tables it
  didn't fix. Measure the language server's resident memory on `aoc` after
  a full check.
- **F4.** No counter for snapshots per check or rows per table. Add them
  to `STITCHWORT_TIMINGS`' summary (cheap), so that the cost claims here can
  be checked.
- **F5.** Plain `aoc` `check --no-cache` peaks at 1.59 GB resident (68.7 s
  wall) on `main` today. language-server.md §3.4 measured 162 MB on a
  smaller `aoc`. It may only reflect the project's growth, but it is worth a
  look (`STITCHWORT_TIMINGS` has no memory column).
- **F6.** `library::Context`'s save and restore are written out twice
  (`library.rs:1149`, `:1231`).
- **F7.** `unify::RIGID_DIVERGENCE` survives an undone attempt within a
  body (it is reset only around the body, `lib.rs:2797`/`:2807`). It may be
  intended; decide and document it when step 1 moves it.

## Appendix A: the `Elaborator`'s fields

Pattern today: **U** in `undo::Snapshot`/`restore`; **C** in
`clear_metas`; rewind: **R** restored from the mark (copy or length),
**r** emptied or cut by id, **s** ignored as a setting; **E** mentioned in
`cache/mod.rs` (encoded, decoded, or used as cache bookkeeping); **D** in
the canonical dump. Generated from the source at `b9627b79` and corrected
by hand where a regex missed (`records` is dumped).

| Field | Today (U C R E D) | Component | Kind | Note |
|---|---|---|---|---|
| `globals` | `-CRED` | Kernel / Attempt | split (review step 9) | mixed: kernel env + metas + backend facts |
| `tests` | `--RED` | Tables | grow |  |
| `sides_capture` | `--r--` | Decl | scratch |  |
| `scope` | `--RED` | Tables | logged | copied per mark and per cached unit (Before) |
| `namespace_root` | `--RE-` | Unit | swap |  |
| `project_namespaces` | `--R--` | Session | set once | copied per mark; set by the host per project |
| `project_prefixes` | `--R--` | Session | set once | copied per mark |
| `project_names` | `--R--` | Session | set once | copied per mark |
| `namespace_defs` | `--RED` | Tables | grow (by namespace) |  |
| `prelude_defs` | `--R-D` | Tables | set once | dumped, not encoded: set before any unit |
| `file_mode` | `--R--` | Unit | swap |  |
| `include_files` | `--RE-` | Session | host-provided | set by the host as it loads a project or a file on its own (`include_from`, `include_in_folder`), so it is not an option; copied per mark |
| `include_locations` | `--RE-` | Session | logged |  |
| `next_include_location` | `--R--` | Unit | swap |  |
| `obligations` | `UCr--` | Attempt | trail |  |
| `row_metas` | `UCr--` | Attempt | trail |  |
| `row_constraints` | `UCr--` | Attempt | trail |  |
| `queue` | `UCr--` | Attempt | trail (own log) |  |
| `awaiting_helpers` | `UCr--` | Attempt | trail |  |
| `defaulted` | `UCr--` | Attempt | trail |  |
| `defaulted_records` | `UCr--` | Attempt | trail |  |
| `char_patterns` | `--r--` | Decl | scratch, keyed by span | kept across the attempts at a declaration; an undone attempt keeps its rows |
| `char_proofs` | `--r--` | Decl | scratch, keyed by span | as `char_patterns` |
| `loading_prelude` | `--RE-` | Unit | swap | read by 19 modules as a mode flag |
| `rewrite_budget` | `--sE-` | Options | setting |  |
| `library` | `--RE-` | Session | logged (load states) | copied per mark |
| `library_tests` | `--sE-` | Options | setting |  |
| `core_link_names` | `--s--` | Session | dynamic extent | set by the host around the core's load and cleared after, so not an option; `None` at every mark |
| `abilities` | `--RED` | Tables | grow |  |
| `limits` | `--sE-` | Options | setting |  |
| `numbers_as_succ` | `--sE-` | Options | setting |  |
| `module` | `--RE-` | Unit | swap | copied per mark; ItemInfo per item of the unit |
| `warnings` | `--RE-` | Unit | swap | copied per mark |
| `lambda_warnings` | `U-r--` | Attempt | trail | set aside beside the `Unit` by a library load |
| `branch_errors` | `U-r--` | Attempt | trail |  |
| `arm_reach` | `--r--` | Decl | scratch |  |
| `no_propagation` | `--r--` | Decl | dynamic extent | a Cell counter set and reset around a call |
| `bare_rows_pure` | `--r--` | Decl | dynamic extent |  |
| `late_literals` | `--r--` | Decl | dynamic extent |  |
| `dot_heads` | `--R--` | Caches | cache | copied per mark; keyed by addresses within a source epoch |
| `source_epoch` | `--s--` | Session | counter | ignored by rewind (never reused) |
| `dot_failed` | `--R--` | Caches | cache | keyed by meta-state lengths: valid only while those identify a state |
| `condition` | `--r--` | Decl | dynamic extent |  |
| `app_expected` | `--r--` | Decl | dynamic extent |  |
| `decreasing` | `--r--` | Decl | dynamic extent |  |
| `recursion` | `--R--` | Decl | dynamic extent | empty at a mark (asserted) |
| `records` | `--rED` | Tables | owned by DataId |  |
| `no_eq` | `--rED` | Tables | owned by DataId |  |
| `no_show` | `--rED` | Tables | owned by DataId |  |
| `no_finite` | `--rED` | Tables | owned by DataId | SW-1128 (fixed) |
| `no_decide` | `--rED` | Tables | owned by DataId | SW-1128 (fixed) |
| `no_ord` | `--rED` | Tables | owned by DataId |  |
| `generated_alls` | `--rED` | Tables | owned by DataId | SW-1128 (fixed) |
| `drafts` | `UCr--` | Attempt | trail |  |
| `standalone_inputs` | `--s--` | Session | counter | ignored by rewind |
| `glue` | `--s--` | Options | setting | not in `cache_key()`: glued and unglued evaluation might give a library file different terms (unchecked) |
| `arounds` | `--r--` | Decl | dynamic extent |  |
| `lifted` | `--RED` | Tables | grow |  |
| `match_columns` | `--rED` | Tables | owned by DefId |  |
| `pending_run_bodies` | `--r--` | Decl | queue across a group | drained when helpers are final |
| `owner` | `--r--` | Decl | dynamic extent |  |
| `body_type` | `--r--` | Decl | dynamic extent |  |
| `local_keys` | `U-r--` | Attempt | trail | cleared at 4 sites besides rewind |
| `preadmitted` | `--r--` | Decl | scratch |  |
| `signature_matches` | `--r--` | Decl | per declaration key | kept between type and body; never encoded |
| `owner_unfolding` | `--r--` | Decl | dynamic extent |  |
| `owner_helpers` | `--r--` | Decl | scratch |  |
| `local_helpers` | `--R--` | Decl | scratch (per group) | empty at a mark (asserted) |
| `helper_keys` | `--RED` | Tables | logged | copied per mark and per cached unit |
| `local_metas` | `UCr--` | Attempt | meta-keyed |  |
| `meta_names` | `UCr--` | Attempt | trail |  |
| `operator_dictionaries` | `UCr--` | Attempt | meta-keyed |  |
| `local_dictionaries` | `UCr--` | Attempt | trail-keyed |  |
| `local_defaults` | `UCr--` | Attempt | meta-keyed |  |
| `goals` | `U-r--` | Attempt / Presentation | trail |  |
| `goal_snapshots` | `--r--` | Presentation | log |  |
| `proof_holes` | `UCr--` | Attempt | meta-keyed |  |
| `parameter_metas` | `UCr--` | Attempt | meta-keyed |  |
| `hole_log` | `--s--` | Decl | dynamic extent | ignored by rewind (only set inside one rewrite) |
| `cong_candidates` | `--r--` | Caches | cache |  |
| `result_heads` | `--r--` | Caches | cache (by DefId) |  |
| `decision_order` | `--r--` | Caches | cache |  |
| `performs` | `--r--` | Caches | cache (by DefId) |  |
| `total_rows_only` | `--r--` | Decl | dynamic extent |  |
| `total_rows` | `--r--` | Tables | owned by DefId | **gap**: read by later units (check.rs note, nav hover) but neither encoded nor dumped |
| `interfaces` | `--RED` | Tables | owned by DataId |  |
| `instances` | `--RED` | Tables | logged | copied per mark; an older row may change (valid flag) |
| `data_owners` | `--rED` | Tables | owned by DataId |  |
| `instance_steps` | `-Cr--` | Attempt | budget, keyed by meta | reset with the metas; deliberately not refunded when an attempt is undone |
| `instance_budget` | `--sE-` | Options | setting |  |
| `uniform_operators` | `--sE-` | Options | setting |  |
| `instance_waits` | `--s--` | Session | statistic |  |
| `in_instance_signature` | `--r--` | Decl | dynamic extent |  |
| `nav` | `--RED` | Presentation | logged (nav::Logged) |  |
| `check_cache` | `--sE-` | Options | setting (host) |  |
| `cache_stats` | `--sE-` | Session | statistic |  |
| `namespace_sources` | `--RE-` | Session | logged | copied per mark |
| `namespace_keys` | `--RE-` | Session | logged | copied per mark |
| `namespace_capture` | `--rE-` | Unit | swap |  |
| `skip_navigation_walk` | `--rE-` | Unit | swap |  |
| `omega_for_auto` | `--s--` | Unit | per module | carried into and out of a nested library load, and not rewound: a library file's value is what the next module's code sees until it sets its own (SW-1150) |
| `replayed_names` | `--RE-` | Session | logged | copied per mark |
| `fail_replays_late` | `--sE-` | Options | test switch |  |
| `recheck_namespaces` | `--s--` | Options | test switch |  |
| `include_trace` | `--rE-` | Unit | log |  |
| `library_digest` | `--sE-` | Session | computed once |  |
| `counterexample_runner` | `--s--` | Options | setting (host) |  |
| `no_counterexamples` | `--s--` | Options | test switch |  |
| `untimed_counterexamples` | `--s--` | Options | setting |  |
| `counterexample_log` | `--s--` | Session | log | grows forever; ignored by rewind; goes to `Presentation` in step 7 |
| `tuple_matches` | `--R--` | Decl | scratch | read only for termination errors; empty at a mark |
| `leaf_log` | `--r--` | Decl | scratch |  |
| `arm_probe` | `--r--` | Decl | scratch |  |
| `equation_skips` | `--rE-` | Tables | owned by DefId | encoded but **not dumped** |
| `local_asts` | `--r--` | Decl | scratch |  |
| `equations_done` | `--R--` | Tables | grow | **gap** SW-1135: rewound, neither encoded nor dumped |

## Appendix B: `Globals`' fields (`crates/core/src/globals.rs`)

| Field | Today | Component | Kind / note |
|---|---|---|---|
| `defs`, `datas` | grow; rewound by length; encoded by path and hash | `Kernel` | `Vec` by load order |
| `builtins`, `registry` | rewound by their own marks (`BuiltinsMark`, `forget_from`) | `Kernel` | per-id side tables |
| `unfinished` | rewound | `Kernel` | owned by id |
| `hashes` | rewound | `Caches` | content hashes, derivable |
| `erasure` | rewound | `Tables` | backend fact, `OwnedBy<DataId, _>` (review issue 3) |
| `module` | in `GlobalsMark`; swapped by library loads | `Unit` | |
| `metas`, `meta_trail`, `frozen_metas`, `lifted_calls`, `unfilled_placeholders`, `placeholder_syntax`, `waiting_literals`, `print_labels`, `meta_epoch` | undone by `Snapshot`, cleared by `clear_metas`; ignored by rewind (empty at marks) | `Attempt` (the meta store) | trail |
| `budget` | reset by rewind; holds the cancel flag | `Session` | operation budget and cancellation |
| `glue`, `transparent` | dynamic extent; `glue` in `GlobalsMark` | `Decl` | set by guards |
| `failed_mentioned` | in `GlobalsMark` | `Decl` | **unclear**: a flag rewound like a table |
| `apart_sets` | kept by rewind ("only lives while a case is checked") | `Decl` | |
