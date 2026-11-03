# Proposal: the elaborator's state, by lifetime

**Status:** Draft 2, 3 November 2026 (SW-1137, D2250; revised for the
external review by SW-1169, D2281). Steps 0-5 are built. Step 6 is specified
in §4.8 and waits for Matt's decisions there (§8, D2283-D2287). §4.9 says
what the design keeps open for parallel checking, and §10 answers the review
([elaborator-state-review.md](../reviews/elaborator-state-review.md)) point
by point. Draft 1 was written at `b9627b79`; draft 2's claims about the code
were checked at `ed1d472c`. It builds
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
   rewound by cutting at an id, encoded as the rows of the unit's own
   declarations, and the "an older row changed" check is built into the
   type; draft 2 checks ownership by a unit tag per declaration, §4.8.4),
   `Logged<K, V>` (any row may change: an undo log like `nav::Logged`,
   whose log is also the index of what a cache entry holds, §4.8.3), and
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
  is intended (SW-1147): the flag only triggers a second check of a body
  that failed, with the divergence total, so an extra trigger costs time
  and cannot change what is accepted, while restoring it on undo could
  skip a needed second check. It is documented on the field, with a test
  in `undo.rs`. And a nested session on the same thread (§2.7) would see the outer
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
  a cache hit. §4.9 lists what it would need and the constraints this
  design adopts so as not to block it.
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
| `Caches` | 6 (+ `Globals::hashes`) | any; derivable | the dot-call tables copied; the rest cut by id or emptied | never |
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
├── caches:  Caches           derivable memo tables; clear() empties all of them
└── present: Presentation     nav recorder, goal snapshots, counterexample log
```

Each component lives in `elab/src/state/`; its fields are `pub(crate)` (`Options`' are public, for hosts and tests). The
mechanisms become methods with exhaustive destructuring:

| Mechanism | Who implements it | Shape |
|---|---|---|
| Undo an attempt | `Attempt::mark()` / `restore(m)` | trail lengths; `restore` destructures `Attempt` |
| Per-declaration cleanup | `Decl`, `Attempt` | `*decl = Decl::default(); attempt.reset()`; nothing to list |
| Nested library load | `Unit` | `let saved = mem::take(&mut self.unit); …; self.unit = saved` |
| Rewind | `Kernel`, `Tables`, `Session`, `Unit`, `Presentation`, `Caches` | each `mark()`/`rewind(&m)`; `Elaborator::Mark` is a tuple of them. `Caches`' mark copies `dot_heads` and `dot_failed` (keyed by addresses within a source epoch); its rewind cuts `result_heads` and `performs` to the definitions that remain and empties `cong_candidates` and `decision_order`. A `Unit` mark keeps a copy of the fields that outlive a unit (the last module, the namespace root, warnings, file mode); `Session`'s copies the bookkeeping a later load can change and leaves its counters. `Decl` is asserted empty at a mark and reset on rewind; `Attempt` is reset. `Options` is left alone |
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
| Grows only, by load order | `GrowVec<T>` | push only | length / truncate | rows past the mark's length | `tests`, `abilities`, `lifted`, `equations_done`, `equation_skips` |
| Owned by an id | `OwnedBy<Id, V>` | a row for id `i` is written only while the unit that declared `i` is elaborated: `insert` asserts it (draft 1: `i >= unit_start`; draft 2: `owner(i) == current unit`, §4.8.4) | id cut (`retain(i < mark)`) | the rows of the unit's own ids, written as path + hash | `records`, `no_eq`, `no_show`, `no_ord`, `no_finite`, `no_decide`, `generated_alls`, `interfaces`, `data_owners`, `match_columns`, `total_rows` |
| Any row may change | `Logged<K, V>` | every write goes through its methods (§4.8.5) | undo log (`nav::Logged`, generalised): O(1) mark, O(changes) rewind (§4.8.2) | the log is an index of the keys the unit wrote; the entry holds each key's current value or its removal (§4.8.3) | `scope` (its maps), `instances`, `helper_keys` |
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

**As built (step 5, SW-1165).** `state/table.rs` has `GrowVec<T>` and
`OwnedBy<I, V>` and the trait, adapted to the codec as it is:

```rust
trait Table {
    type Mark;
    type Rows;                     // what an entry holds of it, read back
    fn mark(&self, ids: Ids) -> Self::Mark;      // Ids: how many defs, datas
    fn rewind(&mut self, m: &Self::Mark);
    fn encode_since(&self, m: &Self::Mark, e: &mut Encoding) -> Result<(), String>;
    fn decode(b: &mut Body) -> Read<Self::Rows>; // ids already mapped by `Body`
    fn replay(&mut self, rows: Self::Rows);
    fn dump(&self, name: &str, out: &mut String);
}
```

Reading is split from replaying because a replay must change nothing until
the whole entry has been read and the kernel has admitted its
declarations. A row implements `Codec` (`encode`, `decode`; in
`cache/rows.rs`) and `Dump` (in `cache/dump.rs`), separately. An `OwnedBy`
id is a `DataId` or a `DefId` (written by `Encoding::data`/`def`, so by
path and hash). `state/tables.rs` has `Tables`, its `Mark` (which is also
the check cache's `Before` for the tables) and `Delta` (what an entry holds,
read). `Tables::{begin_unit, mark, rewind, encode_since, replay, dump}`
destructure `Tables`, and `decode` builds `Delta` whole. The entry format
puts two parts that aren't tables in the middle of them: the side facts of
the unit's declarations (fields' and parameters' defaults, update display,
`js_repr`) after `records`, and the namespace's extensions before `tests`.
So `encode_since` and `decode` take those two parts as closures, and the
bytes are unchanged (no `FORMAT` bump). That was checked: every entry for
`aoc`, the roguelike and six example projects, 382 in all, written by the
build before the change and by the build after it, is byte for byte the
same apart from the key and the checksum, which depend on the build's
fingerprint. The earlier build's entries, given the new build's key, all
load as hits.

`OwnedBy::insert` (and `remove`, which `no_ord` uses) asserts that the id
is at least the start of the unit being elaborated. `elaborate_namespace`
sets that start, and a nested library load sets it for the library file
and puts the outer unit's back. A mark keeps it. It holds for every test
run (elab's lane, `check_cache`, `rewind`, `hash_stability`,
`postponement`, `namespaces`) and for checks of `aoc` and the roguelike.
`encode_since` still checks that no row for an older id was added, which
replaces the cache's `by_data` comparison and now covers `match_columns`
and `total_rows` too. That check only fails if the assertion has been
bypassed, or if a unit's start isn't where its cache `Before` was taken.
*(Draft 2.)* The second case is real: a project namespace's floor is set
before the library files it needs load inside it, and its `Before` after
them. So the floor doesn't stop the namespace writing a row for one of
those files' declarations, and the count check catches a new row there but
not a changed one. §4.8.1 has the code path, and §4.8.4 replaces the floor.
*(Step 6a.)* The floor is gone: `insert` and `remove` take the session's
`Owners` and assert `owner(id) == current unit` (§4.8.9).

Differences from the sketch above:

- `equation_skips` is a `GrowVec`, not `OwnedBy`. It has several rows per
  definition, kept in order, and the entry always held "the rows pushed
  since", so the format needed no change. A rewind now truncates it to its
  length instead of keeping the rows for older definitions. A truncated
  table is what a fresh session had at the mark; the two differ only if a
  unit pushes a row for an older definition.
- `generated_alls` is cut by its key, the data type, and no longer also by
  its value, the `All` definition. The `All` is always defined in the
  data type's own unit.
- `tuple_matches` is in `Decl` (step 2), and `namespace_defs` isn't a
  `GrowVec`: it is a map from each namespace to its range of definitions,
  set when the namespace is done. It is in `Tables`, copied at a mark, and
  not in an entry: a namespace's replay sets its range from the definitions
  it admits. `prelude_defs` is in `Tables` too: set once, dumped, never in an
  entry.
- `instances` and `helper_keys` (`Logged`) are in `Tables` with
  hand-written handling: copied at a mark, an entry holds the rows the copy
  doesn't have, and the "an instance from before changed" check stays.
  The `Before` of a cache entry now copies the whole `InstanceInfo` rather
  than `(def, valid)`. That costs little, since instances are few, and the
  comparison is still on `(def, valid)`. `scope` stays on the `Elaborator`
  until step 6: its entry is written from `cache_before`'s operation log, in
  the names section before the tables, and `Before` copies only its
  `entries`.
- No `Derived<T>`: none of Appendix A's `Derived` tables belongs in
  `Tables`, and step 4 put all six in `Caches`.
- The dump prints each table on its own, sorted by id for `OwnedBy`. Before,
  the keyed tables' lines were sorted together. Two `GrowVec`s whose order
  nothing reads, `equation_skips` and `equations_done`, are dumped sorted,
  as they were before. A cached run may push their rows in another order.

### 4.3 Data structures: what each lifetime uses

| Lifetime | Structure | Mark cost | Why not persistent |
|---|---|---|---|
| `Kernel` defs/datas | `Vec`, by id | a length | eval indexes `defs` on every unfolding: `imbl::Vector` reads take 12-20 ns against 1-1.5 ns (§5.2) |
| `Attempt` metas + trail | `Vec` + trail of old solutions | a length | eval reads metas constantly; the trail is O(1) to mark and O(changes) to undo, which persistence can't beat |
| `Tables` | four kinds (§4.2) | O(1) | rewinds are in stack order (§2.4); logs serve that with 7 MB where `imbl` holds 68 MB (§5.2) |
| `Session` | small maps, `Logged` where copied today | O(1) | as above |
| `Unit`, `Decl` | plain fields | none: empty at every mark | not marked |
| `Caches` | `HashMap`/`Vec` | the two dot-call tables are copied; the rest are cut by id or emptied at a rewind | `Caches::mark` |

**What changes at run time** (estimated from §5.2 and §2):

- A check: no change in lookups. `Logged` adds one stamp comparison and,
  for a key's first write in a segment, one `Vec` push (§4.8.2). A check
  without the check cache (`--no-cache`, the playground) opens no
  checkpoint and logs nothing. A check with the cache logs inside each
  unit's transaction and drops the log when the transaction ends, so the
  log never holds more than one unit's writes (§4.8.2's pruning rule;
  draft 1 said nothing was logged outside a language server, which
  contradicted using the log for cache entries). The `Before` copies of
  `scope.entries` per unit (§2.5) go, and so do the namespace's copies of
  the scope's key set and members (`start_keys`, `start_members`,
  `cache/mod.rs:432-433`). That saves an estimated 0.1-0.3 s of a 69 s
  `aoc` check, against the logging's cost; §4.8.7 measures both.
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
*(Draft 2.)* Reading the code, an instance's `valid` flag is set only by
`validate_instance` (`interfaces.rs:590`), called from `after_definition`
(`lib.rs:2771`) for the instance's own definition, so in its own unit.
No later unit changes an older row of `instances` today, and the cache
refuses an entry in which one did. So a frozen base could forbid shadowing,
as `SMap` does, if §4.8.4's ownership check covers `instances` too. That is
for the frozen base's own note.
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

### 4.8 Step 6, specified (draft 2)

This section is what step 6's lanes implement. It answers the review's
three blocking points (checkpoint lifecycle, which writes belong to which
entry, ownership) and its two high ones (tests, measurements). Where it
decides an implementation detail it says so; the end-state choices are
D2283-D2287 in §8.

#### 4.8.1 What the code does today

**The ownership floor and the count check (review Q2).** For a project
namespace A, in order:

1. `elaborate_namespace` calls `tables.begin_unit(self.ids())`
   (`module.rs:241`): every `OwnedBy` table's floor is the number of
   declarations before A.
2. `elaborate_namespace_untimed` collects A's names (`collect`), works out
   what A needs, notes the early names (`capture_before_needs`), and loads
   the library files A needs (`load_needs`, `module.rs:345`). Each file B
   loads as a nested unit: `enter_nested_unit` sets the floor to the
   declarations before B, and `leave_nested_unit` puts A's back
   (`library.rs:1189`, `:1202`).
3. Then `capture_after_needs` (`cache/mod.rs:526`) takes A's `Before`,
   whose tables mark (`Tables::mark(self.ids())`) has each `OwnedBy`'s
   `cut` at the number of declarations *after* the loads.
4. A's entry is written by `encode_namespace`, which refuses it if any
   library file loaded after step 3 (`cache/mod.rs:569`), and then by each
   table's `encode_since`, which partitions rows by `id < cut` and refuses
   if the number of old rows changed.

So in the review's example (A starts at `DataId` 100, B declares 100, A
then writes a row for 100):

- The assertion doesn't fire: 100 is at least A's floor, 100. The review is
  right.
- If B wrote no row for 100 in that table, A's row is a new row below the
  cut, the old rows number one more than at the mark, and the entry is
  refused ("a row for an older declaration changed"). So the brief was
  right that the count check catches *this* example; the review read the
  cut as the floor, which the brief's excerpt didn't rule out.
- If B did write a row for 100 and A overwrote it (`insert` on an existing
  key), the count is unchanged and the entry is written without A's
  change. A replay then differs from a fresh check. The review's second
  point is right: the count isn't an independent safeguard against a
  changed value. (`no_ord`'s `remove` followed by an `insert` is the same.)
- Without the check cache (a language server's own namespaces when the
  cache misses, `--no-cache`, the playground) nothing checks this at all.

Does anything write such a row today? To find out, I moved the floor to
the cut (after the loads) in a scratch build and printed each project
namespace's ids at its start, before its loads and after them. Not
committed; the patch was four lines in `module.rs`. On `aoc`
(`check --no-cache`, 207 namespaces), 17 namespaces load library files
inside them, no namespace makes a declaration before its loads, and the
moved floor's assertion never fired. With the same build these passed:
`namespaces.rs` (all), `check_cache.rs`'s `a_replayed_*`,
`an_edit_re_elaborates_the_namespace_and_what_uses_it` and
`different_targets_share_one_cache`, and `rewind.rs`'s
`a_check_cancelled_part_way_rewinds` (35 tests). So declarations are
contiguous per unit in practice, and the bug is latent, not live.

**What A's entry holds of B's effects.** B gets its own entry if the
cache is usable: `load_library_file` looks B up (`cache_lookup`), takes
B's own `Before` (`cache_before`, `library.rs:1074`) and writes B's entry
when it checks (`cache_after`). A's entry is worked out against a `Before`
taken after B loaded, so it holds none of B's declarations, table rows or
names. It holds B as a dependency: the library files A needs, by path
(`PreOut::needs_files`), the equations it asked for (`needs.equations`),
and the dot calls; A's replay loads those first (`cache/mod.rs:709`), from
B's entry or by elaborating B. One exception: the members section
(`NamesOut::members`) is the scope's members minus `start_members`, which
is copied before the loads (`cache/mod.rs:433`, `:605`), so A's entry also
lists B's members (constructors, fields, methods). The replay marks them
again, which changes nothing because members are a set. Harmless, but it
is a case of "what changed since the mark" standing in for "what this unit
did", which is the review's point. Equations made on demand for a library
definition (`ensure_equations_of`, `equations.rs:4724`) run as a nested
unit too (`in_library_file`), before A's `Before`, and are named in A's
entry rather than held by it.

A library file never loads another inside itself: its needs load before
it does, and one found missing is an error (`unloaded_needs`,
`library.rs:978`). Its own on-demand equations of other files are made
before its `Before` is taken (`library.rs:1041-1043`).

So today's policy is *dependencies, not duplication*, and it rests on
timing: every nested unit runs before the outer unit's `Before`, and an
entry is refused if one ran after. Step 6 keeps the policy and replaces
the timing assumption with an explicit tag (§4.8.3).

**First-change tracking.** `nav::Logged` (`nav.rs:159`) keeps `touched:
HashSet<K>` and clears it at every mark and rewind. hashbrown's `clear`
walks every bucket to drop the keys (they are `String`s) and resets every
control byte, so it is O(capacity), and capacity never shrinks. A mark is
therefore O(the largest number of keys any one segment ever touched), not
O(1). Amortised over the writes that filled the set it is O(1) per write,
but a language server whose first unit wrote 20,000 keys pays for clearing
a 20,000-key table at every later mark. Step 6 uses a stamp instead
(§4.8.2), which makes a mark O(number of tables).

#### 4.8.2 The journal and its checkpoints

All the `Logged` tables of a session share one **journal**: one stack of
open checkpoints and one generation counter. Each table keeps its own
undo `Vec` (so its entries are typed); the journal only knows positions.
Like today's `Mark`, a checkpoint's positions are a tuple built by
destructuring `Tables` and `Session`, so a new `Logged` table can't be
left out.

```rust
pub(crate) struct Journal {
    open: Vec<Open>,        // open checkpoints, oldest first
    next_serial: u64,       // never reused
    generation: u32,        // a new segment starts when it changes
    segments: Vec<Segment>, // (unit, positions) where each segment starts
    stats: JournalStats,    // §4.8.7
}
struct Open { serial: u64, kind: Kind, at: Positions }
enum Kind { Retained, Transaction }

/// A language server's checkpoint: may be rewound to any number of times.
pub(crate) struct Checkpoint { serial: u64, depth: u32 }   // not Clone
/// A cache transaction (or any other short-lived one): must be ended.
#[must_use] pub(crate) struct Transaction { serial: u64, depth: u32 }
```

`Logged<K, V>` stores `(V, u32)`: the value and the generation in which
its key was last logged. A write logs `(key, old value)` when the stamp
differs from the journal's generation, and sets the stamp. A key with no
row is always logged (so a delete and a re-insert in one segment log twice,
which is harmless: a rewind applies the log newest first, so the older
entry wins). While no checkpoint is open, nothing is logged and the stamp
isn't read. This replaces `touched` (§4.8.1); its cost is 4 bytes per row
(about 120 KB for 30,000 scope rows, an estimate), and a mark is O(number
of tables). *Implementation detail, decided here.*

The operations:

| Operation | Effect | Rule |
|---|---|---|
| `checkpoint() -> Checkpoint` | pushes `Open{Retained}`; turns logging on; new generation | a language server's base mark and its mark before each namespace |
| `rewind(&Checkpoint)` | undoes every table back to its positions; drops every open checkpoint above it (they become invalid); new generation; the checkpoint itself stays open | panics if the checkpoint is invalid |
| `release(Checkpoint)` | pops it | only the top one: a checkpoint below others is released by rewinding to an older one, which drops it |
| `begin() -> Transaction` | pushes `Open{Transaction}`; turns logging on; new generation | one per unit whose entry may be written |
| `commit(Transaction)` | pops it; the log entries stay, belonging to whatever is still open | only the top one; consumes it |
| `abort(Transaction)` | `rewind` to it, then pops it | consumes it |

**Invalid checkpoints are detected, not misused.** A handle holds its
serial and its depth in the stack. Every use checks `open[depth].serial ==
serial`, which is O(1); after a rewind to an older checkpoint the newer
ones are gone from the stack, so their handles fail the check and panic
with "a checkpoint used after a rewind to an older one". `LiveProject`
already drops the `Step`s after the one it rewinds to; this turns a
forgotten one into a failure instead of a wrong state. A `Transaction`
dropped without `commit` or `abort` fails a debug assertion in its `Drop`.

**Pruning: keep the history back to the oldest open checkpoint.** The log
only exists while something is open. When the stack becomes empty (the
last checkpoint released or the last transaction committed), every
table's undo `Vec` and the segment list are cleared and logging stops. As
the first checkpoint is always taken with an empty log, "everything in the
log" and "everything since the oldest open checkpoint" are the same, so no
other rule is needed. In a command-line check with the cache, each unit's
transaction is the only thing open, so the log holds one unit's writes and
is dropped when its entry is written: no whole-project history. In a
language server, the base checkpoint stays open, so the log holds the
writes since the library loaded, which is exactly what a rewind to the base
needs. After an edit, rewinding to namespace `i` truncates the log to `i`'s
positions, so the log's size depends on the project, not on the number of
edits (§4.8.7 checks that it stabilises).

**Cancellation.** A cancelled check returns through the unit's code as
today. Its transaction is committed without writing an entry
(`cache_after` and `elaborate_namespace_cached` already don't write when
cancelled), and then `cancellable_at` rewinds to the retained checkpoint it
took, which undoes the unit's writes. *Decided here:* commit, not abort,
because the retained rewind that follows undoes it anyway and a transaction
must be ended before an older checkpoint is rewound to.

**What stays outside the journal.** `GrowVec` and `OwnedBy` keep their
own marks (lengths and id cuts, §4.2): they don't log. `Kernel`'s `Vec`s
and `Attempt`'s trail are unchanged. The journal is only for the tables
copied today.

#### 4.8.3 A cache entry is the write-set of its unit

The review's main point: an undo log can restore a state perfectly and
still not say which changes belong to an entry. So the log is used as an
*index of keys*, and the unit is explicit.

- **Segments.** The journal records a segment boundary, with the unit that
  is current, at `begin`, at `enter_nested_unit` and at `leave_nested_unit`
  (and starts a new generation there, so each segment logs each key it
  writes). A unit is a `UnitId`, a counter in `Session` (§4.8.4). An
  on-demand equation is made in the segment of the library file that
  defines it (`in_library_file`), as today's floor treats it.
- **A unit's write-set** is the set of keys logged in its own segments
  since its transaction began. For a project namespace that is the segment
  before its library loads (its early names) and the one after them; the
  loads' segments belong to the files loaded.
- **Encoding.** For each key in the write-set, the encoder reads the
  value at the start of the unit's first segment that logged it (the
  oldest log entry for it there) and the current value. Equal: nothing.
  Absent then, present now: a new row. Present both, different: a changed
  row. Present then, absent now: a removal. Each table's policy then says
  what an entry may hold. The scope: new names (early and late, as now),
  changed names (`NamesOut::changed`, as now), and a removed name refuses
  the entry (as now, `cache/mod.rs:582`). `instances` and `helper_keys`:
  new rows; a changed or removed older row refuses the entry (as now). Keys
  are sorted as today, so entries stay byte for byte the same and `FORMAT`
  doesn't change (checked as in step 5: every entry for `aoc`, the
  roguelike and the example projects, written before and after).
- **Nested loads.** B's segment is in B's write-set and not A's, wherever
  it falls in A, so the refusal "a library file loaded part way through"
  (`cache/mod.rs:569`) can go: a load after A's first declarations is
  attributed correctly. *Recommendation: keep the refusal in step 6 anyway*
  (it costs nothing), and drop it only when something needs mid-unit
  loads. A's entry stops listing B's members.
- **What this replaces.** `Before.scope` (a copy of `scope.entries`),
  `start_keys` and `start_members` (`cache/mod.rs:432-433`),
  `Mark.instances` and `Mark.helper_keys` (copies), and the scope's
  `ScopeOp` log for library files' entries, *if* the library entry's
  order of new names can be rebuilt from follower positions as the
  namespace entry's is (`cache/mod.rs:590`). If it can't, `ScopeOp` stays,
  as an ordered list next to the journal; the step 6 lane finds out by the
  byte comparison above.

#### 4.8.4 Ownership: a unit tag per declaration

Two ways to make `OwnedBy`'s check sound (review Q2):

| | Unit tag per declaration | Contiguous allocation |
|---|---|---|
| Rule | `owner(id) == current unit` on every `insert` and `remove` | the floor moves to the cut once the unit's needs have loaded, and nothing loads after that |
| Data | `owners: GrowVec<UnitId>` for definitions and one for data types, pushed as each is made (in `Kernel`, beside `defs`/`datas`); rewound by length; a replayed declaration gets the replaying unit's tag | none |
| Run-time cost | one indexed read per `OwnedBy` write; 4 bytes per declaration: about 60 KB for `aoc`'s 14,950 (estimate) | none |
| What it relies on | nothing about order | an assertion in `load_library_file` that the current unit hasn't started its own part, and every future feature keeping to it (lazy loads, parallel workers that allocate their own ids) |
| Encoding | the rows whose id the unit owns (a filter by tag in place of the cut); no other row can have been written, by the assertion | the rows at or past the cut |
| Catches a changed older row | yes, at the write, with or without the cache | yes at the write once the floor is at the cut; the count check stays weak |

Both are cheap. The probe in §4.8.1 shows contiguity holds today, so the
second would work now. The tag is recommended (D2283) because it states
the invariant directly, costs about 60 KB, makes the assertion meaningful
in sessions without the cache, needs no rule about when loads may happen,
and doesn't assume that ids are allocated in one sequence per unit, which a
parallel design might not keep (§4.9). With the tag, the count check in
`OwnedBy::encode_since` becomes a debug assertion.

`UnitId` is a session counter, never written to an entry, so entries stay
id-independent. The core and the prelude get a unit of their own.

**Tables of another kind: shared keys.** `instances` is keyed by
`(interface, head)`, two data types that can both belong to older units
(an orphan instance), so its key says nothing about ownership. Its row's
`def` does: the row is owned by `owner(info.def)`. It is a `Logged` table
whose rows are each owned by a declaration in the value, and a later unit's
write to an older row is refused at the write (assertion) as well as by the
encoder. §4.5's note found no write of that kind today. `helper_keys` (a
set of strings) and the scope's maps have no owner: any unit may add a
name, and the scope legitimately changes older rows (a name's `Global`
moves from `Unchecked` to `Def`, `module.rs:1010`, `:1449`, in the unit
that declares it; extensions add to other namespaces' types). They are
`Logged` with no ownership check, and the entry's policy (§4.8.3) is what
limits them. So there are three classes: owned by the key (`OwnedBy`),
owned by a declaration in the row (`instances`), and shared (`Logged`).

#### 4.8.5 The mutation rule

Every write to a `Logged` table goes through its methods (`insert`,
`remove`, `update(key, |v| ..)` which logs the old value first). Nothing
returns `&mut V`, `Deref` gives only `&HashMap`, and a row type has no
interior mutability (no `Cell`, `RefCell` or `Rc<RefCell<_>>` in a row),
so a shared reference can't change it either. Enforced by:

- *Types.* The map is private to `Logged`; `Logged` implements `Deref` to
  `&HashMap` only. `Scope`'s fields become private and its maps `Logged`,
  so `pub entries` goes.
- *Known escapes to remove in step 6* (found by grep at `ed1d472c`):
  `scope.entries.get_mut` at `lib.rs:1839`, `module.rs:1010`,
  `module.rs:1449`, `scope.entries.remove` at `update_lemmas.rs:94`,
  `instances.get_mut` at `interfaces.rs:599`, and `helper_keys.insert` in
  seven places (`decreasing.rs:1106`, `lib.rs:2239`, `opaque.rs:293`,
  `update_lemmas.rs:89`, `equations.rs:2644`/`:2646`,
  `equations/induct.rs:728`). Each becomes a method call; making the
  fields private makes the compiler find any missed.
- *Rows.* A `NoInteriorMutability` marker can't be checked by Rust's
  types for arbitrary rows, so it is a review rule, written on `Logged`'s
  doc comment, plus a debug check: under `debug_assertions`, `rewind`
  compares a hash of each table's content after undoing with one taken at
  the checkpoint (only for tests that opt in, `Options::check_rewinds`,
  since hashing 30,000 rows per checkpoint is too slow to be on always).
  *Implementation detail, decided here.*

#### 4.8.6 Tests that accept step 6

1. **A model-based test of `Logged` and the journal** (a unit test in
   `state/`). A reference keeps a `HashMap` and, per open checkpoint, a
   clone of it. A seeded generator (no new dependency: a small xorshift, as
   other tests do) produces sequences of insert, overwrite, remove,
   `checkpoint`, `begin`, `commit`, `abort`, `rewind` (to any open
   checkpoint, including the same one several times running) and
   `release`, plus uses of invalidated handles, which must panic
   (`catch_unwind`). After each step the map equals the reference's, and
   after each `commit` the write-set (§4.8.3) equals the keys whose values
   differ between the reference's clone and its current map, plus any it
   removed. It includes the review's sequence by name: `x = 0; a = mark;
   x = 1; b = mark; x = 2; rewind b (x == 1); x = 3; rewind b (x == 1);
   rewind a (x == 0)`. 10,000 sequences of up to 50 steps should run in
   well under a second (estimate).
2. **Differential scenarios** (`rewind.rs`, `check_cache.rs`, each a small
   project made in a temporary folder, as `check_cache.rs` does):
   - nested library loads with hits and misses: a namespace that needs a
     library file, checked with a cache that has the file, one that hasn't,
     and one whose entry for the file is corrupt;
   - cancellation at several points: the existing
     `a_check_cancelled_part_way_rewinds`, plus a cancel during a nested
     library load and during an entry's encoding;
   - repeated edits of an early namespace: edit, recheck, edit back,
     recheck, five times, comparing with a fresh session each time (this is
     the review's `rewind b` twice, at project scale);
   - replay then depend: replay a namespace from its entry, then elaborate a
     namespace that uses its names, instances and extensions, and compare
     with a fresh check of both (the review's "is the state usable", not
     only "is the dump equal");
   - changes to older rows: a namespace that adds an extension to an older
     namespace's type and moves a name from `Unchecked` to `Def`, replayed
     and fresh.
   - a replay that fails part way (`Miss::Late`) and then elaborates: the
     existing `a_replay_that_fails_part_way_gives_the_same_result`, whose
     write-set now spans the failed replay's writes and the elaboration's;
   - kept: step 4's cleared-caches test.
3. **The ownership assertion** gets one test that it fires: elaboration
   code can't be made to write another unit's row from a test, so this is
   a unit test of `OwnedBy` with two `UnitId`s.

These run in each step 6 lane by name (`task test:one`), with
`rewind.rs`'s `aoc` test once with `STITCHWORT_SLOW=1` if Matt approves, as
the step list says.

#### 4.8.7 Measurements that accept step 6

Each measurement is taken before step 6 (on `main` when it starts) and
after, on the same machine, with the load average written down (draft 1's
benchmark ran at 20-37, which made some cells vary by 30%). CPU time is
compared, not wall time, where other lanes are running.

| What | How | Exists | To build |
|---|---|---|---|
| Language server memory after the first check, and after 100-500 edit and recheck cycles: RSS and the bytes the journal holds; does it stabilise | an edit loop over `LiveProject` (as `crates/cli/tests/lsp.rs`'s `latency_on_aoc` drives `serve`), printing RSS (`task_info` on macOS, `/proc/self/statm` on Linux) and `JournalStats` every 10 cycles | `latency_on_aoc` (ignored; six rounds of two edits, in process); `crates/bench/src/alloc.rs` (a counting allocator: live and peak heap bytes) | the loop: N cycles, edits chosen in an early, a middle and a late namespace; `JournalStats` |
| Edit latency, median and p95, for an early, a middle and a late namespace | the same loop, timing `didChange` to `publishDiagnostics` | `latency_on_aoc` measures this for two namespaces | per-position percentiles |
| Command-line cost: cold (no cache), cold with an empty cache folder (entry creation), warm (all hits), mixed (one middle namespace edited) | `stitchwort check` on `aoc`, user CPU from `time`, two runs each | the CLI, `STITCHWORT_TIMINGS=1` (per unit times, hits and misses) | nothing |
| Journal statistics: entries, distinct keys, peak log length, bytes held, entries undone per rewind | counters in `Session::stats`, printed by `STITCHWORT_TIMINGS` | `Stats` (step 3) | `JournalStats` (summable, §4.9) |
| Mark and rewind time on `aoc` | `rewind.rs`'s `mark_and_rewind_cost` | yes | nothing |

**Budget (estimates).** An early edit makes the language server recheck
nearly every namespace: about a minute each on `aoc` without hits, so the
loop does 10 early, 100 middle and 300 late cycles rather than 500 of each,
or runs the long loop on the roguelike and the short one on `aoc`. That is
about 15-25 minutes per build, twice (before and after). The command-line
runs are 4 modes x 2 runs x 2 builds of about 70-90 s for the cold ones and
a few seconds for the warm, about 15 minutes. All in the background, none
of it a test tier, and run once per build. It is more than a lane's usual
two minutes, so it needs Matt's approval (D2287).

**What counts as success** (proposed, D2287): the language server's RSS
after 300 cycles within 10% of after the first check, and at least 100 MB
below today's on `aoc` (draft 1 estimated several hundred MB in marks; the
earlier `aoc` measured 348 MB against 165 MB for `check --index`,
language-server.md §"As built"); edit latency p95 no worse than today's by
more than 10%; command-line cold and warm checks no slower than 2% in CPU
time.

#### 4.8.8 As built: the journal (step 6a, SW-1171)

`state/journal.rs` has `Logged<K, V>`, the `Logs` trait, `Journal<P>`,
`Checkpoint`, `Transaction` and `JournalStats`, as §4.8.2 specifies, with
these details decided in the lane:

- **The journal is generic over its positions.** `Journal<P>` stores each
  open checkpoint's positions, a `P`, and every operation takes the tables
  as a `&mut impl Logs<Positions = P>`: positions, `undo_to`,
  `set_generation`, and the counts for `JournalStats`. `rewind.rs`'s
  `LoggedTables` names every logged table (in 6a, navigation's five maps,
  while it is on) and `LogPositions` is its `P`; the model test uses one
  `Logged` as its own `Logs`. 6b adds the scope's maps, `instances`,
  `helper_keys` and `Session`'s copied maps to `LoggedTables`.
- **A table holds a copy of the generation.** The journal sets it in every
  table at each checkpoint, transaction and rewind (O(number of tables)),
  so a write reads only its own table: no shared cell, no reference to the
  journal (§4.9). `None` means nothing is open: nothing is logged, and the
  logs are dropped when the stack empties.
- **A restored row gets stamp 0**, which is never a generation. Starting a
  generation at a rewind is therefore redundant (every key written since
  the checkpoint is undone and restamped) but kept, as specified.
- **Checks before changes.** Every operation checks its handle (`serial`
  at `depth`), and `release` and `commit` that it is the newest, before
  changing anything, so a refused use leaves the tables as they were. A
  rewind or abort past an open `Transaction` panics ("commit or abort it
  first"), as §4.8.2's cancellation rule requires.
- **Write-sets.** `Journal::began_at(&Transaction)` gives the positions a
  transaction began at, and `Logged::changed_since(at)` the keys logged
  since, each with its oldest logged value (its value when the
  transaction began). Segments by unit (§4.8.3) are not built: they belong
  to 6c, with the entries made from them.
- **`Elaborator::mark` takes `&mut self`** (and so does the driver's
  `Session::mark`): a mark is a checkpoint, which changes the journal. Five
  call sites needed `let mut`. A `Mark` holds its `Checkpoint`, so a
  rewind to a mark that a rewind to an older one dropped panics, with or
  without navigation (before, only navigation's maps and the driver's
  count of sources caught some such uses).
- **Nothing releases a mark yet.** In 6a a dropped `Mark` leaves its
  checkpoint open until a rewind to an older one, as navigation's log was
  kept before; a command-line check takes no marks, so it logs nothing.
  6b makes `LiveProject` and `Session::cancellable` release theirs. The
  journal's `release`, `begin`, `commit`, `abort` and the write-set are
  used only by the tests until 6b and 6c (`#![cfg_attr(not(test),
  allow(dead_code))]` on the module).
- **`JournalStats`** (public, from `Elaborator::journal_stats`, summable by
  `add`): `entries` (logged), `peak_entries`, `held`, `bytes_held` (the
  logs' entries' own size), `distinct_keys` (counted when read),
  `rewinds`, `undone` (per rewind: `undone / rewinds`), `checkpoints`,
  `transactions`. Entries are counted at each journal operation from how
  much the logs grew, since a write doesn't reach the journal. Not printed
  by `STITCHWORT_TIMINGS` yet: SW-1172's harness reads them.

The model test (`state/journal/tests.rs`, §4.8.6 item 1) runs 10,000
seeded sequences of up to 50 steps (about 256,000 steps: 128,000 writes,
26,000 checkpoints, 13,000 transactions, 11,500 rewinds of which 5,400
repeat the last one, 10,000 releases, 2,800 commits, 2,700 aborts, 1,100
uses of a dropped handle and 5,800 other refused uses) against a `BTreeMap`
with a copy per open checkpoint, in 0.2 s in a release build. It checks the
map after every step, that the logs are empty whenever nothing is open, and
each transaction's write-set before it ends. Besides it: the review's
`x = 0..3` sequence by name, a rewind past a transaction, nothing logged
while nothing is open, and (debug builds) the dropped transaction's
assertion. Changing the journal to not start a generation at a checkpoint,
or a write to not log an overwritten row, fails all of them.

#### 4.8.9 As built: ownership (step 6a, SW-1171)

`state/owners.rs` has `UnitId` and `Owners`, in `Session` (not beside
`defs`/`datas`: they are `Globals`' in `core`, and `Kernel` doesn't exist
until step 8):

- **Tags are filled in when the unit changes,** rather than pushed by
  whatever makes a declaration (the kernel's two `push`es in `core`, the
  cache's replay). `Owners::begin` (`elaborate_namespace`), `enter` and
  `leave` (`enter_nested_unit`, `leave_nested_unit`) first tag the
  declarations made since the last change as the outgoing unit's. An
  untagged id is the current unit's. That gives each declaration the unit
  that was current when it was made, which is the rule, without assuming
  anything about the order ids are given out in, and without touching
  `core`. A rewind cuts the tags to the mark's and puts its current unit
  back (`Session`'s mark); `rewind_globals` and a failed admission in the
  cache cut them to the declarations that remain, as their ids are given
  out again.
- **Units.** Unit 0 is the core and the prelude, and everything before the
  first `elaborate_namespace`. Each `elaborate_namespace` (a project
  namespace, a file, a library file) begins a new unit; a nested load
  (`enter_nested_unit`: a library file, or `in_library_file`'s on-demand
  equations) enters one and puts the outer one back after. So on-demand
  equations are a unit of their own, as the floor treated them (§4.8.3's
  "the segment of the library file that defines it" is for 6c's segments,
  which would need the file's unit, looked up by file).
- **`OwnedBy::insert(owners, id, row)`** and `remove` assert it (14 call
  sites; the replay passes `&session.owners`). `Tables::begin_unit`, the
  floor and `Tables`' `start` are gone.
- **The encoder still partitions by the cut,** not by tag: an entry holds
  the declarations from its `Before` on, so a row for an id below the cut
  couldn't be replayed whoever owns it, and with the assertion no unit
  writes another's. The count check is a `debug_assert_eq!` and still
  refuses the entry in a build without debug assertions, which the tests
  use (`--release`).
- **Tests:** `OwnedBy`'s unit tests (`state/table.rs`): a unit writing,
  overwriting or removing the row of a declaration of a unit nested in it
  (the review's example, F9) panics, as does one for an older unit's; and
  the tags after a rewind.

#### 4.8.10 As built: the copied tables on the journal (step 6b, SW-1173)

- **The scope.** `Scope`'s seven maps that outlive a module (`entries`,
  `followers`, `namespaces`, `std_root`, `members`, `extensions`,
  `extended`) are `Logged` (the sets are `LoggedSet<K> = Logged<K, ()>`),
  and every field is private. `Scope` is the `Logs` of its seven; what a
  mark copies of it (`scope::Mark`) is the current module's imports (as
  `SavedImports`) and a load's flags (`loading`, `core_only`, `log`), all
  small or empty between namespaces. `Scope` is no longer `Clone`. The
  escapes of §4.8.5 became methods: `set_global` (`lib.rs`'s
  `fail_data_names`, `module.rs`'s renumbering and `fail_unchecked_names`),
  `remove` (`update_lemmas.rs`), and one the grep missed,
  `drop_unconfirmed`'s `entries.retain` (`library.rs`), now
  `remove_where`, a logged `Logged::retain`. Reads that bypassed the
  out-of-the-way filter go through `stored`, `has` and `rows`.
- **`instances`** is `Instances`, a `Logged` whose `insert` and `update`
  assert that the unit current is the one that made `info.def` (and, for
  an overwrite, the old row's), §4.8.4's second class; reads go through
  `Deref` to the `Logged`, which gives no write. `validate_instance`'s
  `get_mut` is an `update` (asserting the definition doesn't change), and
  the replay inserts through it. **`helper_keys`** is a `LoggedSet`; its
  seven `insert`s are `add`s. A unit test checks that an outer unit can't
  change an instance a nested one made.
- **The session's maps.** `include_locations` and `namespace_keys`, which
  loads add to, are `Logged`. *Decided here:* the maps the host sets whole
  and nothing changes afterwards (`project_namespaces`, `project_prefixes`,
  `project_names`, `namespace_sources`) are `Arc`s that a mark shares,
  O(1), rather than logged: logging a whole replacement would log every
  row at each edit for nothing. `replayed_names` (one failed replay's early
  names, emptied as each namespace begins) and `namespace_defs` (one row per
  project namespace, compared whole by `auto.rs`) are still copied.
- **`LoggedTables`** names navigation's, the scope's, `Tables`' two and the
  session's two (`SessionLogs`, split from `Session` because the journal is
  in it too); `Elaborator::with_journal` builds it for `mark`, `release`
  and `journal_stats`.
- **The cache keeps its copies until 6c.** `Tables::Mark` no longer holds
  `instances` or `helper_keys`; the cache's `Before` takes `Tables::copies`
  (`Copies`, two `Logged::copy`s: a clone of the map, not a rehash) beside
  its copy of the scope's entries (`Scope::copy_entries`), and
  `start_members` is `Scope::copy_members`. `encode_since` reads the
  copies, so what an entry holds and its bytes are as before.
- **Releasing marks.** `Elaborator::release` and `driver::Session::release`
  close a mark's checkpoint; only the newest open one, as `Journal::release`
  requires. `Session::cancellable` releases the mark it takes, cancelled
  or not (so `f` mustn't leave one of its own open); the
  `recheck_namespaces` hook releases its mark after rewinding to it;
  `LiveProject::step` releases the step's mark when the step is cancelled
  (it was rewound to, and the next step takes a new one), and
  `LiveProject::rewind_to(keep)` rewinds to step `keep`'s mark, which the
  rewind drops those after, and releases it. So a language server's
  journal holds its base and one checkpoint per namespace kept, and its log
  what those need; `JournalStats::open` (new) says how many are open.
- **Not built:** §4.8.5's opt-in hash check of the tables after a rewind.
  The differential tests compare the whole canonical dump with a fresh
  session's, which every logged table is in, so it would add nothing to
  them; rows have no interior mutability (`Global`, `Span`, `String`,
  `Vec<String>`, `()`, `InstanceInfo`, `FileId`, `Key`).
- **Tests added** (`crates/driver/tests/rewind.rs`, §4.8.6 item 2's
  rewinding scenarios): `repeated_edits_of_an_early_namespace_rewind_exactly`
  (a `LiveProject` of two example projects, one with extensions of an older
  namespace's type and one with instances: the first namespace's file
  edited, checked, edited back and checked five times, each compared with a
  fresh session on the same text, with the open checkpoints and the log's
  size the same after each edit back);
  `a_language_servers_check_cancelled_at_each_namespace_rewinds` (a
  `LiveProject` cancelled as each namespace begins, from a check cache
  lookup, then finished: as fresh, no mark left open); and
  `a_check_cancelled_at_each_use_of_the_cache_rewinds` (a project and a file
  that loads library files, cancelled at each of their 90 uses of the cache:
  nested library loads, namespace lookups and entry writes, then checked
  again with the entries written before the cancellation: as fresh). The
  model test also retains. Breaking the scope's undo of one table (the
  followers) fails the first. `mark_and_rewind_cost_on_aoc` (ignored, run by
  name) runs the measurement below without the rest of the full tier.
- **Measured** (`mark_and_rewind_cost`, `aoc` with navigation, the same
  test on the build before and after, load 3-9): a mark 1.04 → 0.26 ms, a
  rewind to it 1.35 → 0.28 ms, ten marks 8.4-9.0 → 2.0-2.4 ms, and what a
  mark holds (the resident set's growth over ten) 3.6-3.7 → 1.9-2.1 MB. The
  rest is `Caches`' dot-call maps (15,089 rows in `dot_heads`), which no
  step of this note moves onto the journal: they are written through
  shared references (`RefCell`), so they need their own change (§9, F11).

### 4.9 Keeping parallel checking possible

Parallel checking isn't planned (D2281). This section says what it would
need, so that step 6 and the steps after it don't make it harder.

**What it would need.**

- *Shared state that is `Send + Sync`.* Core terms and values are `Rc`:
  166 occurrences of `Rc<` in 14 files of `crates/core/src` at
  `ed1d472c`. The elaborator has 106 lines declaring or building a `Cell`
  or `RefCell`. There are 8 `thread_local!`s (`timings.rs`, `kernel.rs`'s
  rejection log, and `core`'s `reference.rs`, `term.rs` and four in
  `value.rs`); `unify.rs`'s went into `Attempt` in step 1. Moving the
  core to `Arc` costs an atomic increment per clone everywhere (not
  measured), which is why §6 rules it out now.
- *A frozen base per worker:* each worker starts from the library and the
  namespaces it depends on, read-only and shared (§4.5 with `Arc`).
- *Merging a worker's namespace as a cache hit:* the worker's result is an
  id-independent entry, and the main session replays it (§2.5's format is
  already a merge format).
- *A deterministic merge order:* replays in the canonical namespace order,
  whatever order the workers finish in, so that ids, hashes and
  diagnostics are those of a sequential check.
- *Per-worker `Caches`,* since they are derivable, and per-worker `Stats`
  that sum into the session's.

**The constraints this design adopts now.**

1. Ownership doesn't assume contiguous ids: the unit tag (§4.8.4).
2. A unit's delta is its write-set, id-independent (§4.8.3), so it is the
   same thing whether it was made in this session or in a worker.
3. A journal belongs to one session and has one writer. Nothing in it is
   shared between sessions, and no table holds a reference into another
   session's journal.
4. No new `Rc`, `RefCell`, `Cell` or thread-local in `state/`: new state is
   plain fields of a component, mutated through `&mut`. (The existing
   `RefCell`s moved with their fields, §4.1; this rule stops new ones.)
5. `Stats` and `JournalStats` are sums of counters with an `add`, so
   per-worker values combine.

These cost nothing measurable beyond the tag's 60 KB (estimate).

**A cheaper first experiment** (future research ticket, not part of step
6): check independent namespaces in separate *processes*, each replaying
its imports from the check cache, and merge by replaying the entries they
write. It needs no `Send`, uses the cache's existing format, and measures
how much parallelism the namespace graph has before anyone touches `Rc`.
`aoc`'s namespace graph would give the upper bound; that is the ticket's
first measurement.

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
| 4 | **`Caches`**, plus a test switch (`Options::clear_caches_per_declaration`, checked in `Elaborator::glued`) that clears `Caches` before every declaration; the rewind test runs a sample with it | proves the caches are caches | `rewind.rs` with the switch, on its normal-tier sample |
| 5 | **Table kinds and `Tables`.** `GrowVec`, `OwnedBy`, `Derived`; move the `Tables` fields; `Tables::{mark, rewind, encode_since, replay, dump}` destructure exhaustively. Encoded bytes unchanged (no `FORMAT` bump) | SW-1128's class | `check_cache.rs`, `rewind.rs`, `hash_stability.rs` (bytes unchanged) |
| 6a | **Ownership tag and the journal** (§4.8.2, §4.8.4). `UnitId` in `Session`, `owners` beside `defs`/`datas`, `OwnedBy` checks `owner(id) == current unit` (the count check becomes a debug assertion); the `Journal`, `Checkpoint`, `Transaction` and `Logged` with stamps, and `nav::Logged` moved onto them. Take §4.8.7's "before" measurements first. *Done (SW-1171): §4.8.8, §4.8.9; `Owners` in `Session`, tagged at unit changes; marks are checkpoints; nothing releases one until 6b* | the floor (§4.8.1); `touched`'s O(capacity) mark | the model-based test (§4.8.6 item 1), `OwnedBy`'s unit test, `navigation.rs`, `rewind.rs` (normal sample) |
| 6b | **The copied tables onto the journal.** `Scope`'s maps (fields private, §4.8.5's escapes removed), `instances` (owned by `info.def`), `helper_keys` and `Session`'s copied maps become `Logged`; `Mark` stops copying them; `LiveProject` holds `Checkpoint`s. *Done (SW-1173): §4.8.10; the host's whole-set maps shared (`Arc`) rather than logged; marks released by `LiveProject`, `cancellable` and the rewind test's hook; a mark on `aoc` 1.04 → 0.26 ms, 3.7 → 2.1 MB (the rest is the dot-call cache)* | mark memory and time (F3) | `rewind.rs` (`STITCHWORT_SLOW=1` once, with Matt's approval), `navigation.rs`, the differential scenarios of §4.8.6 item 2 that are about rewinding |
| 6c | **Entries from write-sets** (§4.8.3). Segments by unit; each unit's entry from its write-set; `Before.scope`, `start_keys`, `start_members` go; entries byte for byte unchanged (as step 5 checked); then §4.8.7's "after" measurements | the per-unit copies; the members a namespace's entry repeats | `check_cache.rs`, `hash_stability.rs`, the cache scenarios of §4.8.6 item 2 |
| 7 | **`Presentation`.** `nav`, `goal_snapshots`, `counterexample_log` | last loose fields | `navigation.rs`, `search_at.rs` |
| 8 | **The `Globals` split** (review step 9, its own design note): the meta store into `Attempt`, `Env` private as `Kernel`, `erasure`/`js` as `OwnedBy` tables | review issue 3 | per that note |
| 9 | **Frozen base** (optional, after measuring): its own short design note with the fork's measured value | SW-1109, search's second session | per that note |

Steps 1-4 are independent of each other once step 1's module skeleton
(`state/`) exists, but they all edit `lib.rs`, so they run one after
another (CLAUDE.md: lanes on the same area don't run side by side). Steps 5
and 6 touch `cache/` and `rewind.rs` and also run one at a time.
*Estimate:* steps 0-7 take about 8 lanes of 1-3 hours each; draft 2 makes
step 6 three lanes (6a-6c, about 2-3 hours each, an estimate).

*Draft 2 on the order.* Step 6 stays before the frozen base (step 9), as
the review advised: the frozen base adds overlay lookups to hot code, and
step 6 fixes the measured memory problem without changing how tables are
read. Splitting step 6 into three is an implementation choice, made here:
6a is small and fixes the latent ownership bug on its own, 6b changes
rewinding only, and 6c changes the cache only, so each lane's differential
test is about one mechanism. Nothing in step 6 depends on the `Globals`
split (step 8).

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

Draft 2's open questions, for step 6 (answered 1-9 above are draft 1's):

- **D2283: ownership by a unit tag per declaration** (§4.8.4), rather than
  guaranteeing contiguous allocation and moving the floor to the cut. Both
  work today (the probe in §4.8.1). The tag costs about 60 KB on `aoc` and
  one indexed read per `OwnedBy` write (estimates); contiguity costs
  nothing but becomes a rule every future feature must keep (no library
  load once a unit has started its own part; one id sequence per unit),
  and leaves the count check weak. *Rec: the tag.*
- **D2284: the journal's lifecycle as specified** (§4.8.2): retained
  checkpoints and transactions as two types over one journal; serials that
  make an invalidated checkpoint panic; the log kept only while a
  checkpoint is open, so a command-line check holds at most one unit's
  writes; stamps per row instead of `touched`. *Rec: yes.*
- **D2285: a cache entry is its unit's write-set** (§4.8.3): segments
  tagged by unit; nested library loads stay dependencies (named by path,
  replayed from their own entries), never duplicated in the outer entry;
  the "a library file loaded part way through" refusal kept until
  something needs mid-unit loads. *Rec: yes.*
- **D2286: the parallel-readiness constraints** (§4.9) as rules for
  `state/` code, with the separate-processes experiment filed as a
  research ticket in the backlog, not scheduled. *Rec: yes.*
- **D2287: step 6's measurements** (§4.8.7): about 30-40 minutes of
  background runs before step 6 and the same after (an estimate), outside
  the lanes' two-minute test budget, with the success criteria stated
  there. *Rec: yes.*

Decided here, as implementation details: stamps rather than a `touched`
set; commit rather than abort on cancellation; the debug rewind-hash check
opt-in; step 6 as three lanes 6a-6c in that order.

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

- **F8** (draft 2). A namespace's entry lists the members (constructors,
  fields, methods) of the library files loaded inside it, because
  `start_members` is copied before the loads (`cache/mod.rs:433`, `:605`).
  Harmless (members are a set); step 6c removes it.
- **F9** (draft 2). `OwnedBy`'s floor doesn't stop a namespace writing a
  row for a declaration of a library file loaded inside it, and the
  encoder's count check misses an overwritten row (§4.8.1). Latent: no
  such write on `aoc` or in the tests run. Fixed by step 6a.
- **F10** (draft 2). `nav::Logged::mark` clears `touched`, which is
  O(capacity), so a mark costs more after one large namespace than
  before it (§4.8.1). Fixed by step 6a.
- **F11** (step 6b). After 6b a language server's mark still copies
  `Caches`' dot-call maps: 15,089 rows of `dot_heads` on `aoc`, about
  2 MB and 0.2 ms a mark, now nearly all of a mark's cost. They are
  written through `RefCell`s during elaboration, so `Logged` doesn't fit
  as it is. They are caches (step 4's switch clears them with no change),
  so a rewind could instead cut them (rows keyed by a source address or a
  definition from after the mark) or empty them, at the cost of
  recomputing dot calls after each edit; which is cheaper is a
  measurement.

## 10. Response to the external review (draft 2)

The review ([elaborator-state-review.md](../reviews/elaborator-state-review.md))
approved the architecture and step 6 on conditions. Each point:

| Review point | Answer | Where |
|---|---|---|
| Q1.1: marks for language-server checkpoints, cache transactions and nested elaboration have different lifecycles; make them different concepts, and specify commit, discard and invalidation | Accepted. `Checkpoint` and `Transaction` over one journal; nested elaboration is a segment, not a checkpoint | §4.8.2 |
| Q1.1: track validity, so a rewind to an earlier checkpoint invalidates later ones and keeps its target | Accepted, by serial and depth, checked in O(1); a stale handle panics | §4.8.2 |
| Q1.2: keep history only back to the oldest usable checkpoint; a command-line check must not accumulate the whole project's log | Accepted. The log exists only while a checkpoint is open, so a CLI check holds one unit's writes at a time | §4.8.2, §4.3 |
| Q1.3: clear `touched` after a rewind; test `x = 0..3` | Accepted. `nav::Logged` does clear it; the sequence is in the model test by name | §4.8.6 item 1 |
| Q1.3: is clearing `touched` O(1)? | It isn't: O(capacity). Replaced by a generation stamp per row | §4.8.1, §4.8.2, F10 |
| Q1.4: the log holds old values, not what to replay; use it as a write-set index | Accepted: the entry holds each key's current value or its removal, with a per-table policy | §4.8.3 |
| Q1.4: nested loads' writes must not become the outer entry's | Accepted. Today they don't, by timing (§4.8.1), except members (F8). Step 6 attributes by segment tag | §4.8.1, §4.8.3 |
| Q1.4: every write through the logging API; no `&mut` escapes or mutable objects behind `Rc` | Accepted. Twelve escapes found and listed; fields made private; no interior mutability in rows; an opt-in debug check | §4.8.5 |
| Q2: the floor isn't an ownership invariant when units interleave | Accepted. Confirmed in the code, latent today | §4.8.1, F9 |
| Q2: the count check wouldn't catch the example | Partly rejected: the cut is taken after the nested loads, so the example as written (a new row) *is* refused, which the brief didn't show. Accepted for an overwritten row, which isn't caught, and for sessions without the cache, which check nothing | §4.8.1 |
| Q2: a unit tag, or guaranteed contiguous allocation | Accepted: the tag is recommended, with its cost; contiguity costed as the alternative | §4.8.4, D2283 |
| Q2: tables like `instances` need a different classification | Accepted with change: `instances` is owned by the declaration in its row, not its key. But no later unit changes an older instance row today (the brief said one could; the code sets `valid` only in the instance's own unit) | §4.8.4, §4.5 |
| Q3: step 6 before the frozen base; can the base really be immutable? | Accepted; the order is kept. The immutability question is left to the frozen base's note, with §4.5's finding that `instances` needn't shadow | §7, §4.5 |
| Q4: model-based tests of `Logged`; differential scenarios (nested loads, cancellation, repeated early edits, replay then depend, changed rows); keep the cleared-caches test | Accepted, as acceptance criteria | §4.8.6 |
| Q4: exhaustive destructuring doesn't make a classification correct | Accepted; nothing to change. Review of a diff asks "does a later unit read this?" (§4.4), and replay-then-depend tests usability | §4.4, §4.8.6 |
| Q5: measure sustained language-server memory, edit latency, CLI overhead and log statistics, before and after | Accepted, with the tools that exist, what must be built, a budget and success criteria | §4.8.7, D2287 |
| Q6: persistence possibly per table, after step 6 | Accepted. §8 decision 2 is "no dependency now"; a persistent map for one table stays an option if undo logging proves awkward for it, decided after step 6's measurements | §8 |
| The `Globals` split is unfinished | Agreed; it is step 8 and doesn't block step 6 | §7 |

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
| `tests` | `--RED` | Tables | grow | in `state::Tables`: `GrowVec` |
| `sides_capture` | `--r--` | Decl | scratch |  |
| `scope` | `--RED` | Tables | logged | 6b: its seven maps `Logged` (the module's imports and a load's flags copied per mark); still copied per cached unit (Before) until 6c |
| `namespace_root` | `--RE-` | Unit | swap |  |
| `project_namespaces` | `--R--` | Session | set once | set by the host per project; 6b: an `Arc`, shared with the marks |
| `project_prefixes` | `--R--` | Session | set once | 6b: shared with the marks |
| `project_names` | `--R--` | Session | set once | 6b: shared with the marks |
| `namespace_defs` | `--RED` | Tables | copied | in `state::Tables`, by hand: copied per mark; not in an entry (a namespace's replay sets its range) |
| `prelude_defs` | `--R-D` | Tables | set once | in `state::Tables`, by hand: dumped, not encoded: set before any unit |
| `file_mode` | `--R--` | Unit | swap |  |
| `include_files` | `--RE-` | Session | host-provided | set by the host as it loads a project or a file on its own (`include_from`, `include_in_folder`), so it is not an option; copied per mark |
| `include_locations` | `--RE-` | Session | logged | 6b: `Logged` |
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
| `abilities` | `--RED` | Tables | grow | in `state::Tables`: `GrowVec` |
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
| `dot_heads` | `--R--` | Caches | cache | in `state::Caches`; copied per mark (6b: 15,089 rows on `aoc`, nearly all of a mark's 2 MB); keyed by addresses within a source epoch |
| `source_epoch` | `--s--` | Session | counter | ignored by rewind (never reused) |
| `dot_failed` | `--R--` | Caches | cache | in `state::Caches`; copied per mark; keyed by meta-state lengths: valid only while those identify a state |
| `condition` | `--r--` | Decl | dynamic extent |  |
| `app_expected` | `--r--` | Decl | dynamic extent |  |
| `decreasing` | `--r--` | Decl | dynamic extent |  |
| `recursion` | `--R--` | Decl | dynamic extent | empty at a mark (asserted) |
| `records` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` |
| `no_eq` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` |
| `no_show` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` |
| `no_finite` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy`; SW-1128 (fixed) |
| `no_decide` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy`; SW-1128 (fixed) |
| `no_ord` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` (also removes rows) |
| `generated_alls` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy`, cut by its key only; SW-1128 (fixed) |
| `drafts` | `UCr--` | Attempt | trail |  |
| `standalone_inputs` | `--s--` | Session | counter | ignored by rewind |
| `glue` | `--s--` | Options | setting | not in `cache_key()`: glued and unglued evaluation might give a library file different terms (unchecked) |
| `arounds` | `--r--` | Decl | dynamic extent |  |
| `lifted` | `--RED` | Tables | grow | in `state::Tables`: `GrowVec` |
| `match_columns` | `--rED` | Tables | owned by DefId | in `state::Tables`: `OwnedBy` |
| `pending_run_bodies` | `--r--` | Decl | queue across a group | drained when helpers are final |
| `owner` | `--r--` | Decl | dynamic extent |  |
| `body_type` | `--r--` | Decl | dynamic extent |  |
| `local_keys` | `U-r--` | Attempt | trail | cleared at 4 sites besides rewind |
| `preadmitted` | `--r--` | Decl | scratch |  |
| `signature_matches` | `--r--` | Decl | per declaration key | kept between type and body; never encoded |
| `owner_unfolding` | `--r--` | Decl | dynamic extent |  |
| `owner_helpers` | `--r--` | Decl | scratch |  |
| `local_helpers` | `--R--` | Decl | scratch (per group) | empty at a mark (asserted) |
| `helper_keys` | `--RED` | Tables | logged | in `state::Tables`; 6b: a `LoggedSet`; still copied per cached unit until 6c |
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
| `cong_candidates` | `--r--` | Caches | cache | in `state::Caches`; emptied by a rewind and at each namespace |
| `result_heads` | `--r--` | Caches | cache (by DefId) | in `state::Caches`; cut to the remaining definitions by a rewind |
| `decision_order` | `--r--` | Caches | cache | in `state::Caches`; emptied by a rewind |
| `performs` | `--r--` | Caches | cache (by DefId) | in `state::Caches`; cut to the remaining definitions by a rewind |
| `total_rows_only` | `--r--` | Decl | dynamic extent |  |
| `total_rows` | `--r--` | Tables | owned by DefId | in `state::Tables`: `OwnedBy`; F1, fixed in step 0 (SW-1140) |
| `interfaces` | `--RED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` |
| `instances` | `--RED` | Tables | logged | in `state::Tables`; 6b: `Instances`, `Logged`, a row owned by `info.def`'s unit (asserted); still copied per cached unit until 6c; an older row may change (valid flag), by its own unit only |
| `data_owners` | `--rED` | Tables | owned by DataId | in `state::Tables`: `OwnedBy` |
| `instance_steps` | `-Cr--` | Attempt | budget, keyed by meta | reset with the metas; deliberately not refunded when an attempt is undone |
| `instance_budget` | `--sE-` | Options | setting |  |
| `uniform_operators` | `--sE-` | Options | setting |  |
| `instance_waits` | `--s--` | Session | statistic |  |
| `in_instance_signature` | `--r--` | Decl | dynamic extent |  |
| `nav` | `--RED` | Presentation | logged (`state::Logged`) | its five maps on the session's journal since step 6a; its lists cut back by length |
| `check_cache` | `--sE-` | Options | setting (host) |  |
| `cache_stats` | `--sE-` | Session | statistic |  |
| `namespace_sources` | `--RE-` | Session | set once | 6b: set whole by the host, so an `Arc` shared with the marks rather than logged |
| `namespace_keys` | `--RE-` | Session | logged | 6b: `Logged` |
| `namespace_capture` | `--rE-` | Unit | swap |  |
| `skip_navigation_walk` | `--rE-` | Unit | swap |  |
| `omega_for_auto` | `--R--` | Unit | swap | copied per mark. Cleared when a module starts and set after its loads. A nested library load starts with the outer unit's value and the outer's comes back with it (SW-1150); a mark keeps it. Typed-in expressions (`eval`, the REPL) see the last module's, or `false` before any |
| `replayed_names` | `--RE-` | Session | copied | 6b: still copied per mark: one failed replay's early names, emptied as each namespace begins |
| `owners` (step 6a) | | Session | per declaration | `Owners`: the unit that made each declaration and the current one; tags cut back and the current unit put back by a rewind (§4.8.9) |
| `journal` (step 6a) | | Session | journal | the checkpoints of the logged tables; a mark is one (§4.8.8) |
| `fail_replays_late` | `--sE-` | Options | test switch |  |
| `recheck_namespaces` | `--s--` | Options | test switch |  |
| `clear_caches_per_declaration` | `--s--` | Options | test switch | new in step 4: empties `Caches` in `Elaborator::glued`, before each declaration |
| `include_trace` | `--rE-` | Unit | log |  |
| `library_digest` | `--sE-` | Session | computed once |  |
| `counterexample_runner` | `--s--` | Options | setting (host) |  |
| `no_counterexamples` | `--s--` | Options | test switch |  |
| `untimed_counterexamples` | `--s--` | Options | setting |  |
| `counterexample_log` | `--s--` | Session | log | grows forever; ignored by rewind; goes to `Presentation` in step 7 |
| `tuple_matches` | `--R--` | Decl | scratch | read only for termination errors; empty at a mark |
| `leaf_log` | `--r--` | Decl | scratch |  |
| `arm_probe` | `--r--` | Decl | scratch |  |
| `equation_skips` | `--rE-` | Tables | grow | in `state::Tables`: `GrowVec` (several rows per definition, in order) |
| `local_asts` | `--r--` | Decl | scratch |  |
| `equations_done` | `--R--` | Tables | grow | in `state::Tables`: `GrowVec`; SW-1135, fixed in step 0 |

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
