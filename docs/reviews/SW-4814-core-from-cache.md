# SW-4814: the core from the check cache

**Status:** built on `lane/SW-4814`, 25 Nov 2026, for a Fable review before
merge (the ticket asks for one). Matt approved the trust change (D3746,
25 Nov 2026: "we should be using caches"). The requirements are section 3
of [SW-4816-checking-profile-review.md](SW-4816-checking-profile-review.md)
("Must stay true" 1-5, "Brief should require"); this note says how each is
met and lists every piece of state loading the core sets.

## The design in short

- **Where.** `crates/elab/src/cache/core_entry.rs` (key, capture, write,
  replay); `Session::start_with_core` and `start_cached` in
  `crates/driver/src/driver.rs`; the process-wide switch
  `check_cache::use_core_cache(dir, recheck)`, set by the CLI with the
  name index (`use_index_cache` / `use_index_and_core_cache`: `check`,
  `check --std`, `test`, and everything that loads a program through
  `load_main`: `run`, `build`, the opcode census) and by
  the editor at start. Nothing else sets it, so tests, snapshots, the
  benchmark and `--no-cache` elaborate and check the core from source.
- **Who uses it.** `Session::start` passes the switch on only for
  `Library::Standard` without library tests. `with_prelude_falling_back`
  (stale pins) goes through `start_in` and never sees it; `core_alone`
  (`Library::None`), `with_library_files` (`Files`) and
  `with_library_index` (`Index`) never use it either.
- **The key** (`Elaborator::core_cache_key`, worked out after the limits
  and navigation are set and before anything loads): the tag, `FORMAT`,
  `natives {!disable_natives} compact {!disable_compact_text}
  {Options::cache_key()} nav {nav_tag}`, the core text the session is
  about to elaborate (the `prelude` argument, not the index's copy), and
  the library interface (below). The unit is `core` plus the nav tag.
- **The stamp** must be this build's compiler, exact, and its interface
  `library_interface_of(hash(core text), index)`: the same function
  `Elaborator::library_interface` uses, so it equals what the session works
  out after `finish_core` and `install_library`. The CheckCache's salt is
  checked by `open`. Only `store.read` is tried: never `read_others`, so
  no carried-over core, whatever `--carry-over` says.
- **Write** (a miss): `core_capture` begins a journal transaction and the
  scope log before `elaborate_module`; after the chain warnings are
  partitioned off, the entry is written only if nothing else was
  reported (`rest` empty: no error, no doc-link warning, no binder-sweep
  or other warning), with the chain warnings in the entry's head; the
  transaction is committed either way. Encoding is the library file's
  (`encode_pass`), with `UnitOut::core` allowing primitives and core
  built-ins, and `encode_stamped` stamping with the core's interface.
- **Replay** (a hit): `replay_core` opens, checks the stamp, reads the
  head and decodes (all of which change nothing: a failure is
  `CoreReplay::Miss`, and the session elaborates the core in place), then
  begins the unit as `elaborate_namespace` does, sets the unit state the
  core leaves, and calls `admit_replayed(.., library = true, ..)` and
  `replay_tables`. A refusal there is `CoreReplay::Failed`:
  `Session::start_with_core` drops the session and starts again with
  `Elaborator::new()`, elaborating the core (and writing its entry), and
  counts the refusal (`Stats::refused`, or `refused_on_recheck`).
- **After either path** `finish_start` runs what followed the core before:
  `finish_core` (with `check_complete_core`), `check_library_declares_all`,
  `install_library`, and the eager loads.
- **`check --recheck`** sets `recheck` in the switch: the core's
  declarations go through the kernel's checking calls (`recheck_def`,
  `recheck_group`, `declare_indexed_data_group`, `define_data_group`,
  `recheck_run_body`), and `Stats::core_rechecked` makes the report say
  "the core and ...".

### Two changes to shared code

1. **Run bodies before built-in binding in `submit`.** Binding `List.length`
   (`bind_builtin_def` → `length_run_body`) gives it a run body unless it
   has one; replay used to bind first and then admit the entry's run body,
   which the kernel refuses as a second one. Library entries never hit
   this (`List.length` is the core's). The comment on `length_run_body`
   already said "a replayed `List.length` has it already". Found by the
   differential tests failing (all five hit tests failed with "a run body
   of the wrong arity, or a second one" before the swap).
2. **`finish_core` resets `unit.module`** (the core module's scratch:
   items, waits, the declarations each made) to the default. Nothing after
   the core reads it before the next module replaces it; a replayed core
   has none, so both paths now leave the same.

Also: `FORMAT` 46 → 47 (a `primitive` flag on every definition record);
the decoder refuses a primitive outside the core's entry (`submit`: an
entry that binds built-ins with no library installed is the core's), one
left out to part B, or one in a group. (Since SW-1204, 27 Nov 2026, `FORMAT`
48: a library file's entry may hold float primitives, admitted by
`float::define_primitive`; the core's primitives are still refused outside
the core's entry, and a namespace's entry may hold no primitive.)

## What loading the core sets, and how each is replayed or recomputed

"Entry" means read from the entry as a library file's entry is read;
"recomputed" means the same call elaborating makes runs again on replay;
"both" means it runs after either path.

### Kernel

| State | How |
|---|---|
| Definitions and data types: types, bodies, groups, flags (theorem, instance, fold, opaque, tailrec, param default, unfolding), admitted metadata, run bodies | entry, through `admit_trusted_*` (or the checking calls with `--recheck`) |
| Primitives (`Effect.Delay` and the six others): declared, defined by `partial::define_primitive`, which checks the type and registers it in `Builtins::primitives` | recomputed (`admit_primitive`: the declaration from the entry, then `define_primitive`, `registry::bind_def`, `check_shape`, as `lib.rs`'s primitive branch) |
| Registry bindings of core built-ins | recomputed (`bind_builtin_def` / `bind_builtin_data` per final declaration, as elaborating binds), and compared with the entry's `bound` list |
| Pins: each bound declaration's hash against `pins.rs` | recomputed inside `bind_builtin_*`, against the replayed terms |
| `registry::check_shape` of each bound definition | recomputed (inside `bind_builtin_def`, and for primitives) |
| Natives (`register_native`), the `nat` and `bool` slots (`register_nat`, `register_bool`), compact text (`chars::register` when `Char` binds), the `+` rule (`nat_add::register`), `List.length`'s run body | recomputed (inside `bind_builtin_*`; the run body from the entry first, so `length_run_body` keeps it) |
| Float bindings | none in the core (they are `std/Float/Float.sw`'s) |
| Content-hash cache | seeded from the entry's recorded hashes, as for library entries; the test checks them against hashes worked out again |
| `check_complete_core` | both (`finish_core`) |
| `check_library_declares_all` | both (`finish_start`) |
| Machine, budget, erasure and evaluation caches | derived; nothing to replay |

### Elaborator

| State | How |
|---|---|
| Scope: the names the core declares (new, changed, members marked, extensions) | entry |
| Scope imports | both: `finish_core` clears them |
| Tables (records, interfaces, instances, abilities, lifted helpers, readings, walks, why derives were skipped, parameter defaults, ...) | entry (the write-set from the transaction plus the grow-only tables since an empty mark) |
| `tables.prelude_defs` | both (`finish_core`) |
| Tests | none kept by the core in a session without library tests; an entry with tests is refused |
| Navigation (refs, expression and local types, binders, outline) | entry, when the session records it (the nav tag is in the key and the unit) |
| `library_warnings` (the core's `W-PROOF-CHAIN`, `W-REWRITE-THEN-*`) | entry (head warnings), appended in the order they were reported |
| `Session::warnings` (other warnings) | the entry is written only when there are none, so empty on both |
| `W-DOC-LINK` | an error for the core; no entry is written then. The links are checked against the index, which is in the key |
| Binder sweep and statement-style output (`statement_style`) | warnings in `rest`; any of them stops the entry being written, so on replay there are none to give |
| `session.core_digest`, `library_interface_digest` | both (`finish_core`) |
| `session.core_link_names` | set and cleared around elaboration only; `None` after either path |
| `session.owners` | replay begins a unit as `elaborate_namespace` does, so the core's declarations are owned by unit 1 either way |
| `session.paths` | synced lazily from the environment |
| `session.journal` | the capture's transaction is committed; a replay opens none of its own beyond `admit_replayed`'s |
| `unit.loading_prelude` | set by the driver before, cleared by `finish_core`, both |
| `unit.module_path` ("Std"), `namespace_root` (""), `omega_for_auto` (false: no library during the core) | replay sets what elaboration leaves |
| `unit.module` | both: reset by `finish_core` (above) |
| `caches.cong_candidates` and the other memo tables | not replayed: emptied whenever, and cleared when the next module starts |
| `session.stats` (elaboration counters), timings | not replayed: statistics; the timings label says `core (cached)` |
| `derive_waiting`, `blocked`, `waiting_names`, `failed_sources`, `broken_tests`, `failed_decls` | only written for declarations with errors or goals; the core has none, or the entry isn't written |
| `expansions`, `walks`, `facts` (for `--expand*`) | recorded only once `record_expansions` etc. are called, after the session starts; the core's never were |

## How the requirements are met

1. **Key.** As above. Session flavours: `library_tests` and every library
   but the standard one never use the cache; stale pins only exist in
   `try_with_prelude_falling_back`, which calls `start_in` directly.
2. **Exact hits only.** `replay_core` reads only `store.read` and requires
   `stamp.exact`, this compiler and the core's interface.
3. **State.** The tables above. The built-in, pin, shape and registry
   checks run on every start against the replayed declarations.
4. **A refused replay leaves nothing behind.** `CoreReplay::Failed` drops
   the elaborator; a fresh one elaborates the core. A failure before
   admission is a miss with nothing changed (open, stamp, head and decode
   only read).
5. **Same results.** The tests below.

## Tests

`crates/driver/tests/projects/check_cache/core_entry.rs` (binary
`projects`), each comparing a session started through the cache with one
that elaborated the core: the canonical dump, every declaration's content,
interface and data hash (as the session has them, then with the hash cache
cleared and worked out again), the rendered `library_warnings`, and the
canonical dump after loading a program (`accept/day2-chunks.sw`):

- `the_core_loads_the_same_from_its_entry` (cold: miss and write; warm:
  hit), and `..._with_navigation`;
- `the_core_checked_again_from_its_entry_is_the_same` (`--recheck`'s path);
- `a_core_of_its_own_misses_the_standard_entry_and_hits_its_own`;
- `a_corrupt_core_entry_is_a_miss_and_is_rewritten`;
- `a_core_replay_refused_part_way_starts_again_from_source` (forced after
  `Std.Bool`, through `refuse_replays_after`).

All five hit tests failed before the run-body ordering fix. The CLI's
`check_cache::check_recheck_says_what_it_checked_again` (binary `server`)
now expects "the core and 2 namespaces".

## What the reviewer should attack

- **The key's completeness.** Is there an input to the core's elaboration
  outside `Options::cache_key`, the two kernel switches, the nav tag, the
  text and the index? In particular anything a host sets on the
  elaborator before `start` returns (the counterexample runner is set,
  but only runs in tactics the core doesn't use), and environment
  variables read during elaboration (§2.1's inferred rows).
- **Ordering in `submit`.** Binding a group's built-ins after its run
  bodies rather than before: is there a built-in whose binding a run
  body's admission depends on, or one whose run body a binding must make?
- **Primitives on the trusted path.** `admit_primitive` declares the
  signature through `admit_trusted_def` and then calls the checking
  `define_primitive`. Is the primitive's placement in the replay order
  (immediately on declaration) the elaborator's, so the prelude types it
  needs are final? (They are, by the same argument as every group's, if
  elaboration defines a primitive at its signature, which `lib.rs` does.)
- **Unit state.** Anything a host reads between the core and the first
  module that differs between the paths, beyond the dump (which prints
  `module_path` but not `unit.module`).
- **The detection of the core in `submit`** (`library` and no library
  installed). A library file's replay always has an index installed; is
  there a path that replays a library entry before `install_library`?
- **Eviction.** One entry per unit: a test's own core evicts the standard
  one's entry, so alternating cores keep missing. Fine for tests (which
  don't use it); worth knowing.

## Measured

`hyperfine -N`, 20 runs, warm caches, `cd aoc && stitchwort check
Aoc.Year2024.Day02 Aoc.Year2024.Day02.Proofs`, 5-minute load 7.8 (25 Nov
2026, 17:10): base binary (`e0a1aabd0`) against this branch.

| | before | after |
|---|---|---|
| `STITCHWORT_JOBS=1` | 176.5 ± 5.2 ms | 86.2 ± 1.3 ms |
| default jobs | 178.0 ± 2.2 ms | 88.2 ± 1.1 ms |
| peak memory | 70 MiB | 57 MiB |

About 90 ms a check, above the 60-80 ms SW-4816 estimated. Both print the
same.
