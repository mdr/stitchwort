# Code review: `crates/elab`, part 3 (everything else)

SW-1912, 7 November 2026, Opus, by reading only (no build, no tests run).
Baseline: `ca13da333`. Scope: `derive*.rs`, `interfaces.rs`, `effects.rs`,
`rows.rs`, `no_effect.rs`, `lift.rs`, `defaults.rs`, `library.rs`,
`library_tests.rs`, `std_dir.rs`, the Rust side of `std/`, `cache/`,
`nav.rs`, `module.rs`, `project.rs`, `data_auto.rs`, `families.rs`,
`partial.rs`, `tailrec.rs`, `quot.rs`, `opaque.rs`, `reify.rs`,
`attributes.rs`, `builtin_docs.rs`, `doc_links.rs`, `equations.rs` and
`equations/`, `equation_notes.rs`, `missing.rs`, `redundant.rs`, `shown.rs`,
`shared.rs`, `timings.rs`, `probe.rs`, `kernel.rs`, `update_lemmas.rs`,
`patlet.rs`. `cases.rs` is in part 2's scope (SW-1899) and is left to it.
About 51,000 lines.

Read closely: `cache/mod.rs`'s `admit_replayed` and `submit`, the cache
key and codec, `library.rs`'s load path, `nav.rs`'s recorder and
`navigation_index`, `module.rs`'s component loop, `rows.rs`'s `retry`,
`effects.rs`'s `comp_app` settle, `lift` and `align`, `interfaces.rs`'s
search, budget and `none`, the derive drivers and their failure paths,
`kernel.rs`, `shared.rs`'s `shared_fields` and `accessors`, `patlet.rs`,
`equations.rs`'s `branch_lib` and `attempt`, `timings.rs`. The rest I
skimmed by outline and by grepping for the patterns below. The deep
reading was split across three forks of this lane (derives and kernel
trust; instance search and rows; library, cache and navigation); I checked
the medium findings against the code myself.

Questions for Matt are D2720 and D2721.

## Summary

There is nothing here that lets a wrong proof through. Every derived
definition, accessor, equation, induction principle, lifted helper and
default helper is a kernel term or elaborated syntax that ends in
`kernel::declare_def`/`define_group`. The only path to the kernel's
`admit_trusted_*` is the check cache's `admit_replayed`, which is
documented as trusted. The one finding that reaches toward soundness is in
that replay path. When a replayed entry is refused partway, the undo
truncates the environment but not the kernel's builtin bindings (natives,
Float definitions). A definition admitted later under a reused id could
then be evaluated as a native. That needs a sealed entry that fails late,
so it's rare, but it's an S fix and should go first. Next come two
behaviour bugs. A library file that fails to check stays `Loaded` for the
rest of the session, half declared. SW-1564's settle-to-empty in
`comp_app` runs before the call's own postponed row comparisons are
retried, which is the likely reason the same settle broke `List.cross` in
SW-1581. After that come costs and consistency. Derived declarations run on
the data type's budget. Derive failures are handled five different ways. In
the language server, navigation records an expression type for every
expression of every std file it loads. Instance search is deterministic and
bounded. The row operations hold their invariants where I checked them.

**Top five recommendations**

1. **Undo a refused replay with the kernel's mark and rewind** (F1), and
   print all of `Builtins` in the canonical dump (F10), so the differential
   cache test would see it. One Opus lane with F11.
2. **Retry a call's own postponed row comparisons before settling its row
   empty** (F2), then try SW-1581's settle at the end of `comp_check_in`
   and `comp_infer` again.
3. **Give a library file that failed a `Failed` state** (F3, D2720), so
   later requests get its real errors rather than "dependency analysis
   missed".
4. **One failure path for generated declarations** (F6, D2721), with a
   budget of its own for each deriver (F5). A failure the deriver's plan
   was meant to rule out is a compiler bug, and should be visible.
5. **Stop recording expression types while library files load** (F4).
   This shrinks the language server's memory, its `+nav+ty` cache entries
   and the cost of each `navigation_index`.

**Findings by severity:** 0 high, 7 medium, 17 low.

## Findings

| # | Severity | Confidence | Where | What | Size |
|---|---|---|---|---|---|
| F1 | medium | high (mechanism), low (frequency) | `cache/mod.rs:2584-2594`, `core/src/globals.rs:704` | A refused replay's undo leaves native and Float bindings on ids that will be reused | S |
| F2 | medium | medium | `effects.rs:3619-3629` | SW-1564's settle in `comp_app` ignores the call's own postponed row comparisons, and isn't marked `settling_empty` | S |
| F3 | medium | high | `library.rs:1338-1378` | A library file that fails stays `LoadState::Loaded`, half declared | S/M, after D2720 |
| F4 | medium | high | `nav.rs:432-442`, `nav.rs:1024-1029` | The language server records and caches a type for every expression of every std file loaded | S |
| F5 | medium | medium | `lib.rs:2322-2332`, `records.rs:61-73`, `module.rs:394,496` | Derived declarations (some quadratic in constructors) run on the data type's budget | S |
| F6 | medium | medium | ten derive sites (list below) | Derive failures handled five ways; some hide compiler bugs entirely | M, after D2721 |
| F7 | medium | high | `effects.rs` (5,231), `module.rs:292-1137`, `equations.rs` (7,406) | Files and one 845-line function too large to reason about | M ×2 |
| F8 | low | high | `rows.rs:271-316` | `retry` drops kept row comparisons when it fails | S |
| F9 | low | high | `effects.rs:1091,1098,1100,1159,1529,1532,1605,2837`, `rows.rs:390` | The `bool` from `cx.unify` is dropped in row code | S |
| F10 | low | high | `cache/dump.rs:305-325` | The canonical dump leaves out most of `Builtins` | S |
| F11 | low | high | `cache/mod.rs:2791`, `lib.rs:2982` | Replay binds builtins for project namespaces; fresh elaboration doesn't | S |
| F12 | low | high | `kernel.rs:63-68` | `without_glue` restores by hand (1 Nov §4.1) | S |
| F13 | low | high | `interfaces.rs:1606`, `derive.rs:642` | `findable` treats running out of instance budget as "no instance" (D2543) | S |
| F14 | low | medium | `interfaces.rs:1108-1269` | `E-INSTANCE-NONE`'s hints scan every definition, also on probe paths that throw the error away | S |
| F15 | low | high | `effects.rs:390` | Row invariants checked only by `debug_assert!` | S |
| F16 | low | low | `effects.rs:1601-1641`, `1213-1221` | A fresh row tail is untyped and not noted, so it's never defaulted | S |
| F17 | low | medium | `interfaces.rs:1046-1050` | Sets the budget tree on whichever obligation happens to be last | S |
| F18 | low | medium | `derive_induct.rs:388-392`, `748,777,795` | Nested induction can admit `D.All` and then give up on `T.induct` | S |
| F19 | low | medium | `nav.rs:747-790` | Each `navigation_index` reprints every outline item's type, signature and header | M |
| F20 | low | high | `library.rs:137-148` | `LibraryIndex::standard` caches its first result, an error included, and the first caller's stack size | S |
| F21 | low | high | `module.rs:214-218,415,463,466,595,818`, `library.rs:1349-1365` | More control flow by error-code strings and message text | (part 1's F5) |
| F22 | low | high | `equations.rs:4470-4536`, `module.rs:2851` | The branch equations' std lemmas are listed twice and fail soft when missing | S |
| F23 | low | high | `timings.rs:93-99,251` | Timing stacks not unwound on a caught panic; process-wide rows and stats keep every session | S |
| F24 | low | high | `derive.rs:376-385`, `derive_show.rs:577-586` | A duplicated helper; only same-module instances replace a derived one | S |

## Details

### F1. A refused replay leaves builtin bindings behind

`admit_replayed` (`cache/mod.rs:2570-2594`) submits a library entry's
declarations. If any group is refused, or the builtins it bound differ from
what the entry recorded, it undoes with
`Kernel::forget_declarations_from(base_defs, base_datas)`, then truncates
`owners` and `paths`. `forget_declarations_from` (`core/src/globals.rs:704`)
truncates the environment and `caches.forget_from`, and nothing else. It
doesn't touch `Builtins`: `natives`, `primitives`, `float_defs`, the Float
data and bit lemmas, the Nat-add rule, and the `nat`/`bool`/`text` slots.
`submit` fills all of these through `bind_builtin_def` (and from there
`float::register_def` and `register_native`) as each group becomes final.
`Kernel::rewind` does clear them, through `Builtins::rewind`
(`core/src/native.rs:261`). `forget_declarations_from` has no other caller.

**Scenario.** A library entry for the Float file binds `Float.add`, so
`float_defs` holds `DefId(n)`. A later group of the same entry is refused,
which the module doc lists as an ordinary way to miss ("one the kernel
refuses"). The defs are truncated, and the file is elaborated again from
source. If the source no longer binds `Float.add` at `n` (the edit that made
the entry stale might move or remove it), whatever definition is next
admitted as `DefId(n)` is evaluated by the machine as the Float native. This
is a wrong-answer bug in evaluation and in kernel conversion, under an entry
the checksums accept. Frequency is low: a sealed entry has to fail late.

**Change (S).** Take `self.kernel.mark()` before `submit` and
`self.kernel.rewind(&mark)` on failure. Or have `forget_declarations_from`
call `builtins.rewind`. Add a test that forces a refusal after a Float
binding (a fixture entry with a corrupted later group) and checks that
`float_defs` is back as it was. F10 would have caught this in the
differential test.

### F2. SW-1564's settle runs before the call's own row comparisons are retried

When a call's arguments are all checked and its row is still unknown,
`comp_app` (`effects.rs:3619-3629`) settles the row as empty, so the call is
a plain one rather than a step of the enclosing row (SW-1564). But checking
those arguments can have postponed row comparisons through
`rows::postpone`: a callback whose type was blocked (`Answer ?flag`) when it
was compared. They are still in `row_constraints`, unretried. When one of
them later resolves to a `Comp` over the enclosing ability, `settled_first`
returns `Abilities`, and the user gets `E-ABILITY` ("settled as the empty
row before the callback's type was known") for a program that checked
before SW-1564. The settle also isn't wrapped in `rows::settling_empty`,
unlike `settle_let_lambda` (`effects.rs:1591`). So the row unknown isn't
marked `settled_empty`, and `explain_defaulted`/`settled_early` can't point
at this call when the late error comes.

This is very likely why the same settle, moved to the end of `comp_check_in`
and `comp_infer`, broke `List.cross` in SW-1581. More callbacks are still
blocked at that point. This is a reading, not a run.

**Change (S).** Note `row_constraints.len()` on entry to `comp_app`. Before
settling, run `while self.retry_rows_from(first_new)? {}`, as
`check::pure_first` and `no_effect::pure_as_plain_calls` already do. Don't
settle if a comparison still kept from `first_new` mentions the call's row
unknown. Wrap the settle in `settling_empty`. Then retry SW-1581's open
unknown-row lifting on top.

### F3. A library file that fails stays loaded

`load_library_file` (`library.rs:1335-1378`) sets `state[f] =
LoadState::Loaded` and pushes `f` onto `order` before it looks at the
diagnostics. On failure (an error, an open goal, `W-REDUNDANT` and the other
convention codes, or `E-RESOURCE` under a tight `--limits`) it returns the
errors but leaves the file `Loaded`, and `drop_unconfirmed` doesn't run. The
next namespace in the same session that needs the file gets `Ok(())` at
once. Its pending names then surface as an internal "unloaded / dependency
analysis missed" error, or as unrelated errors downstream such as missing
instances. The language server rewinds its marks between checks, so it
mostly escapes this. A CLI run over several namespaces, or `test` over a
project, doesn't. The `E-RESOURCE` branch is the reachable one: a program
that needs a large library file under a small `--limits` fails once with
the right message, and every later namespace fails with the wrong one.

**Change (S/M, after D2720).** Add `LoadState::Failed(Vec<Diagnostic>)`.
A later request returns those diagnostics, or a short "library file X
failed earlier in this run" pointing at them.

### F4. Expression types for every std file in the language server

The language server turns on `enable_expression_types`
(`lsp/src/lib.rs:1938`). `note_expr` (`nav.rs:432-442`) checks only
`nav.generated == 0`, not whether a library file is loading. Navigation stays
on while std files load (only `in_library_file`'s import handling switches
anything off). So on a cold library load the server prints a type for every
expression in every std file it loads, keeps the strings in `expr_types` for
the session, and writes them into the `+nav+ty` library cache entries.
`navigation_index` (`nav.rs:1024-1029`) then clones and sorts the whole
table on every call, and `driver/src/nav.rs:547` throws away everything that
isn't a user file.

**Change (S).** Skip `note_expr`'s push, and the pending pushes for
expressions, while `loading_prelude` or a library file is on the stack.
Rebuild the `+nav+ty` entries (format bump; the migration cost doesn't
count).

### F5. Derived declarations run on the data type's budget

`lib.rs:2322-2332` runs `derive_data_eq`, `_show`, `_ord`, `_finite`,
`derive_nested` and `derive_update_lemmas` inside the type's own component,
under the type's budget (`module.rs:394`). So does `records.rs:61-73` for
ext and `Decidable`. Several grow with the square of the constructor count.
Derived `==` matches pairs (`derive.rs:64`: "n² - n checks"), and Ord's
`%unfold` has an `rfl` per pair (`derive_ord.rs:479-504`) unless the type is
a plain enumeration. With a type of many constructors (an opcode type with
fields), the user can get `E-RESOURCE` on their `type` line for code they
never wrote, and the whole type fails. `derive_pending_ord` already gets a
fresh budget (`module.rs:496`), so an Ord derived late is measured
differently from one derived at once.

**Change (S).** Give each deriver a fresh budget, and name the derivation in
the resource error ("deriving `Ord` for `Op` ran out"). Separately, time a
100-constructor type. If it's slow, an O(n) `decEq` for enumerations through
the tag round trip would remove the square.

### F6. Five ways a derive can fail

- **A stored note, shown only on use.** DecEq, Show, Ord, Finite and Decide
  store "deriving it failed: …" as a note that appears only when `==`,
  `${}` or the instance is used. For Decide that's the designed path (the
  `reject/derive-decidable-record-field` snapshot). For the others, the
  deriver's plan is meant to rule failure out first, so a failure is a
  compiler bug, and no test would notice.
- **Dropped.** `derive_ext.rs:79-82` drops every non-resource error with no
  note.
- **Removed from scope.** `update_lemmas.rs:93-96` removes the name from
  scope, and leaves the kernel declaration pending.
- **Turned into `E-INTERNAL`.** `derive_induct.rs:299-312` does this, which
  is right for a generated proof.

All ten sites spot a resource error by `e.code == "E-RESOURCE"`, not
`undo::fatal`: `derive.rs:277`, `derive_ord.rs:165`, `derive_show.rs:98`,
`derive_finite.rs:133`, `derive_decide.rs:91,127`, `derive_ext.rs:81`,
`update_lemmas.rs:93`, `families.rs:59` and `derive_induct.rs:298`
(`partial.rs:818` is similar). Part 1's F13 is the same pattern, and these
sites are additional to its list.

**Change (M, after D2721).** One helper for admitting a generated group. It
re-raises what `undo::fatal` says is fatal. A failure the plan was meant to
exclude becomes `E-INTERNAL` at the type, or at least goes into
`kernel::record_rejections` so the elaborator fuzzer sees it. Decide's
documented "not decidable" stays a note.

### F7. Sizes

- **`effects.rs`.** 2,379 lines on 20 Oct, 5,231 now, and no unit tests. It
  already has section markers that give the split: the row representation
  (171-298, with `decode` and `row_value`), divergence indices (from 298),
  lifting with `align`, `mapping` and `injection` (767-1760), rows in types
  (from 1755), stage-0 passing (from 1910), computation mode (2223-4710),
  handlers (from 4710) and coercions (from 5099). `align`'s open/open case,
  `mapping`, `injection` and `no_duplicates` are tested only through
  examples.
- **`module.rs`.** 1,916 lines on 20 Oct, 3,529 now. Its
  `elaborate_namespace_untimed` (292-1137) is one function of about 845
  lines. Its component loop (about 380-600) mixes timing, blame for
  failures, goals, counterexample notes and abandoning the kernel. Extract
  `check_one_component` and `report_failed_component`.
- **`equations.rs`.** 7,406 lines, with `equations/induct.rs` another 2,504.
  Its module doc is the best in the crate. Split along the doc's own
  headings (statements, proofs, branches, on-demand) when it's next touched,
  not before.

**Change (M ×2).** A mechanical split of `effects.rs`, plus unit tests for
`align` and `mapping`. The `module.rs` extraction. Both in a quiet window.

### F8. `rows::retry` loses comparisons on error

`retry` (`rows.rs:271-316`) takes the kept comparisons out with
`split_off(start)`. On the two explicit error returns it puts back `still`
but not the rest of the iterator. On a `?` from `refresh_at`,
`settled_first` or `unify_postponing`, it puts back neither. `Attempt::restore`
cuts `row_constraints` back by length (`state/attempt.rs:327`), so the lost
ones are never recovered. Every caller that recovers from the error today
either works inside its own `start` or abandons the attempt, with one
exception: `local.rs:488` (`preadmit`) swallows a non-fatal error from
`solve_obligations`, which retries rows from 0 (`auto.rs:122`), and carries
on without them. The later effect is a row unknown with nothing constraining
it, defaulted to empty: an `E-ABILITY` or a kernel error far from the cause.

**Change (S).** Put back `still` and the unvisited rest on every exit. A
small guard that does this in `Drop` covers the `?`s.

### F9. Row unifications whose answer is ignored

At `effects.rs:1091,1098,1100,1159,1529,1532,1605,2837` and `rows.rs:390`,
the `bool` from `cx.unify` is discarded: settling divergence indices in
`lift`, "an unknown row on one side is the other's", `settle_empty_at` and
the divergence default. A failed unification (scope, occurs, an index
already fixed) goes unnoticed, and elaboration continues on a false
assumption. The kernel still refuses the term, but as a kernel error rather
than the `E-PARTIAL` or `E-ABILITY` this path would give. **Change (S):**
turn each `false` into this path's error, and put `#[must_use]` on
`Ctx::unify`.

### F10. The canonical dump misses most of `Builtins`

`cache/dump.rs:305-325` prints the registry and `builtins().native(id)`, but
not `float_defs`, `primitives`, the Float and Nat-add registrations, or the
builtin data slots. So the differential check-cache test can't see a replay
that skips, duplicates or leaves behind a Float registration (F1).
**Change (S):** print all of `Builtins`, destructured, so a new field won't
compile until it's printed (the pattern `state/` uses).

### F11. Replay binds builtins where elaboration doesn't

Replay calls `bind_builtin_def` on every replayed declaration
(`cache/mod.rs:2791`). Fresh elaboration binds only while `loading_prelude`
(`lib.rs:2982`). The `bound_builtins` comparison catches a difference, but
as a late miss, which is exactly F1's path. **Change (S):** bind on replay
only for library entries, as elaboration does.

### F12. `without_glue` restores by hand

`kernel.rs:63-68` saves glue, runs `f`, and puts it back. A panic in `f`
leaves glue off for the session. `search.rs:1402` reuses the session after a
caught panic (part 1's F4), so the rest of the session runs unglued: slower,
with different messages, but still sound. The callers are `lib.rs:980, 1062,
1102`, `check.rs:1493, 4987`, `cases.rs:877, 1862`, `matching.rs:1828` and
`rewrite.rs:1495`. **Change (S):** use a drop guard (`ScopedCell`). It fits
in the same lane as part 1's F4.

### F13. A limit chooses whether a type derives `==`, `Show` or `Finite`

`findable` (`interfaces.rs:1606`) treats every non-fatal error as "no
instance", `E-INSTANCE-BUDGET` included. The derivers call it for each field
type (`derive.rs:642`, `derive_show.rs:276`, `derive_finite.rs:249`), so
running out of instance budget decides what is derived. The budget message
goes into the `no_eq` reason, so it isn't silent, but it is a choice made by
a limit (D2543). **Change (S):** treat `E-INSTANCE-BUDGET` as fatal in
`findable`, or report it at the derive.

### F14. `E-INSTANCE-NONE`'s hints cost a scan of the environment

`none` (`interfaces.rs:1108-1269`) iterates `g.env.defs()`, with `conv` on
the candidates and several `cx.show`s, to build its hints. The diagnostic is
built and discarded on speculative paths: `solve_tree` when not strict, and
`findable`, which runs for every field type of every data declaration
(F13's callers) and as a probe (`numbers.rs:336,782`, `cases.rs:1846`).
`conv(..).unwrap_or(false)` hides resource errors there, which is acceptable
for a hint. `let _ = k;` is dead. **Change (S):** build the hints only when
the error is reported, for example with a probe flag.

### F15. Row invariants under `debug_assert!`

`row_value` (`effects.rs:390`) checks "a row with abilities and a tail is
total" and "`partial` is false when `div` is set" with `debug_assert!`,
which the `--release` test tiers compile out. If either is broken,
partiality silently drops out of the row. This is part 1's F3 pattern.
**Change (S):** return `E-INTERNAL`, as `ops_row` does for `NoOp`.

### F16. An untyped row tail

`extend`/`extend_with` (`effects.rs:1601-1641`) and `align`'s open-to-open
case (`1213-1221`) make the fresh tail with `cx.fresh_meta()`, not
`fresh_meta_of` the `Effects` type, and don't `note_row_meta` it. So
`default_rows` never defaults it to the empty row. If nothing closes it,
the declaration ends with an unsolved unknown. I couldn't build such a
program by reading, so this is unconfirmed. **Change (S):** type and note
it.

### F17. The budget tree goes on the last obligation, whichever it is

After `implicit_arg(cx, Icit::Auto, &dom)`, `interfaces.rs:1046-1050` sets
`last.tree = ob.tree` on the last obligation in the list, assuming that
`implicit_arg` pushed one. If it didn't, the tree goes on an unrelated
obligation, which then spends the wrong step budget. **Change (S):** have
`implicit_arg` return the obligation it made.

### F18. Nested induction can stop halfway

`member_parts` (`derive_induct.rs`) can define and admit `D.All` for one
container, under its user-facing name when `D` is in this module (`all_for`,
about 752-760). It can then hit `Stop::Unsupported` for a later container
(748, 777, 795), which `derive_nested` (388-392) treats as success with
nothing made. The result is a `D.All` with no `T.induct`. That's harmless
logically, but surprising in completion and docs. **Change (S):** check
every container's shape before admitting anything, as `define_all` already
does within one container.

### F19. `navigation_index` reprints everything

Every call prints `global_type`, `global_signature` and `global_header` for
every outline item, each with three `scope.get`s, whatever `wanted` asks
for, and rebuilds every symbol and ref (`nav.rs:747-790`). Each edit
therefore costs printing for the whole project. The cost is bounded, since
these are prints with no evaluation. **Change (M):** cache the strings per
declaration, or print lazily for the symbols a ref uses.

### F20. `LibraryIndex::standard` caches its first answer

`library.rs:137-148` stores the first result in a process-wide `OnceLock`,
an `Err` included, and builds under the first caller's stack size. A parse
failure under a small stack therefore sticks for the whole process.
**Change (S):** build under a fixed, generous stack of its own, and don't
store an `Err`.

### F21. More control flow by codes and message text

`module.rs:214-218` (`is_steps_or_depth`, which matches message suffixes),
`module.rs:466` (`ends_with("too large to show")`),
`module.rs:415,463,595,818` and `library.rs:1349-1365`. Most only choose a
note. `ran_out` (415) and the library's `ok` test (1349-1365) decide control
flow. Add them to the list for part 1's F5 design note rather than opening a
lane.

### F22. The branch equations' std lemmas fail soft

`branch_lib` (`equations.rs:4470-4536`) looks up about 18 std names. The
core ones fail with `Stop::Skip("the core's logic isn't loaded yet")`, which
misreports a rename as a loading problem. The library ones are `Option`s,
and a `None` quietly turns off a class of branch equations (guards on `&&`,
`if h:`), recorded only as a skip reason. The library names also have to
match the pre-pass's dependency list, `GUARD_LEMMAS` (`module.rs:2851`),
which is maintained by hand in a second place. They agree today. A rename
in std would pass every check except the tests of those equations.
**Change (S):** one list, used by both, and a test that every name in it
resolves after std loads. Elsewhere, `omega` and `ring`'s `LIBRARY_NAMES`
and the derive drivers' surface names fail loudly, so they need no such
test.

### F23. Timing state

`timings.rs`'s `STACK` and `DECLS` thread-locals are pushed by
`begin`/`decl_begin` and popped by `end`/`decl_end`, with no guard. After a
caught panic (`search.rs`), the next report's attribution is off. `ROWS`,
`DECL_ROWS` and `SESSION_STATS` are process-wide and only grow, keeping an
`Arc<Stats>` for every session made in a long-running process. All of this
happens only with `STITCHWORT_TIMINGS` set, which is dev-only, so the
severity is low. **Change (S):** a drop guard for the frames, and clear the
tables in `report`.

### F24. A duplicated helper, and same-module replacement

`derive.rs:376-385` (`declares_dec_eq`) is `derive_show.rs:577-586`
(`declares_instance_of(dec_eq)`) word for word, and the general helper
lives in the Show deriver. Both look only at the module's own items whose
head is exactly this data item. A user instance through an alias, or in
another module, sits beside the derived one, and instance search reports it
as overlapping (`E-INSTANCE-OVERLAP`, one per head). That's loud, so this is
only a design note. **Change (S):** keep one helper, in `interfaces.rs`.

## Checked and sound

- **Derives go through the kernel.** DecEq, Ord, Show, Finite, Decide, ext
  and update lemmas are built as syntax trees and elaborated through
  `Elaborator::definition`/`definitions` (`lib.rs:2341-2400`), which end in
  `kernel::define_group`. The core-term helpers (`%tag`, `%C%k`,
  `%m{m}%type`, induction, `All`, size, partial's wrappers, shared-field
  accessors, builtin docs' bodies) go through `declare_def` plus
  `define_def` or `define_group`, and their errors propagate. A derived
  instance is registered only after admission (`after_definition` →
  `validate_instance`), so a failed one is never a candidate.
- **Trusted admission.** `admit_trusted_*` is called only from
  `cache/mod.rs:2774,2787`, and `mod kernel` is private to the crate. The
  setters `mark_opaque`, `set_unfolding` and `retype_def` act only on
  pending definitions (`core/src/check.rs:1958,2079-2098`). The public
  `Elaborator.kernel` and core's `pub` API are the core review's finding.
- **Partial, tailrec, quotients, reify, opaque.** Partial members are
  non-recursive in core, with the knot tied by the kernel's `pfix`.
  `tailrec` only checks, and takes a nesting step (`tailrec.rs:471`).
  `quot.rs` checks argument counts before indexing. `opaque.rs:179` sets
  transparency through a guard. `reify` elaborates to an ordinary match.
- **Bounds on user data types.** `families::orders` is capped at 24 orders,
  in a fixed order. Nested-induction discovery terminates: containers are
  earlier, non-mutual and uniform. `shared_fields`' decision loop terminates,
  since each round decides one candidate or stops, and the leftovers are
  reported as cycles.
- **Instance search.** It's deterministic. Global instances are found by
  `(interface, head)` with at most one per head (`E-INSTANCE-OVERLAP`,
  `interfaces.rs:572`), local candidates in context order, and several local
  dictionaries give `E-INSTANCE-AMBIGUOUS` with sorted paths. No map
  iteration chooses anything. It terminates: there are 10,000 steps per
  obligation tree (`interfaces.rs:846`), not restored on retry and cleared
  per declaration, and superclass expansion only goes to interfaces
  declared earlier. Orphans and instances with parameters their type
  doesn't fix are refused.
- **`scanned`** (`interfaces.rs:1399`). Its 100,000-node cap still chooses
  silently. That's planned as stage 4a in
  `docs/proposals/bounded-readback-remaining.md` §3.1, and the plan still
  matches the code. `rows.rs:250` (`refresh_at`'s full quote per retry) is
  stage 4c, and `row_in_result` (about `effects.rs:3699`) is stage 4b.
- **Effect rows.** `decode` refuses a repeated ability (`no_duplicates`).
  Rows are built only through `empty_row`/`ops_row`, which keep the
  canonical form and refuse `NoOp` in release builds. `handle` removes the
  handled ability, and an instantiated tail that repeats it is caught.
  `agree` unifies shared abilities' arguments. `lift` uses `translateD`,
  `liftD` and `delayD` correctly for each pair of divergence states.
  Defaulting only sets unknowns to `Empty`/`Total`, and the kernel
  rechecks.
- **`lift.rs`, `defaults.rs`, `no_effect.rs`.** The captures fixed point is
  monotone and bounded by the context. A dependency cycle is
  `E-MATCH-MOTIVE`. `keys` iterates a map, but numbers each prefix after a
  sort. Helpers go through `define_group`/`define_def`. `no_effect`'s trial
  is undone by a snapshot and can't nest.
- **Check cache.** The module doc and `admit_replayed` say that a replayed
  entry is trusted and `--no-cache` is the full check. Corruption and stray
  reuse are caught by a blake3 checksum and a per-directory salt, not
  tampering. Library keys cover the format, compiler fingerprint, modes
  (natives, compact, `options.cache_key`, nav tag), the library interface,
  the file's path and text, and the edges' keys. Namespace keys cover the
  source hash, dependency keys, the library files' keys (rechecked) and
  include hashes. An edit to a `@[js.*]` attribute changes the file text
  and so the key, so a stale `JsRepr` can't be replayed even though
  attributes aren't content-hashed (D598).
- **Decoding** (`codec.rs`, `cache/rows.rs`). Varints are bounded. Counts
  larger than what's left of the entry are refused before allocating.
  Indices are range-checked, and UTF-8 is checked. I found no reachable
  panic. `encode` refuses files that bind core natives, or that have
  exported, primitive, non-final or validator-carrying declarations, and
  only error-free units are written. `static_code` leaks one string per
  distinct diagnostic code read, which is bounded.
- **Native bindings.** Kernel natives bind by full name and are then
  type-checked (`register_native`). A rename is a loud `E-BUILTIN`. A body
  change under the same name stays bound, which is the core review's
  finding. Float natives, and the runtime's text natives and representations,
  bind by content hash. An edit therefore unbinds them to the slow path,
  never to a different definition, and extract's `*_bound_to_the_prelude`
  and `compact_text_is_bound_to_the_prelude` tests catch it.
- **Navigation.** The recorder's maps are `Logged`, so marks don't copy them
  (SW-1052). `pending` is cut back on undo, and holds no metavariables when
  a mark is taken.
- **Module and project.** `tarjan` is iterative. `resolve_include` refuses
  absolute paths, backslashes and escapes past the root. `std_dir` reads
  std once per process and refuses a late `use_std_dir`.
- **Equations.** Every equation is a kernel term. A kernel refusal of a
  generated proof is recorded as a skip, and the `function_equations` and
  `function_induct` tests assert that there are none. Running out of the
  per-equation budget becomes a named skip, reported as `E-NO-EQUATION` if
  the equation is used. That's a limit that reports rather than chooses.
- **Thread-locals and globals outside `Attempt`/`state`.** In scope there
  are `kernel.rs`'s `RECORDING`/`REJECTIONS` (off unless a test turns them
  on), `timings.rs` (F23), and process-wide immutable `LazyLock` names
  (`module.rs`, `omega.rs`, `ring.rs`). There are also `std_dir`'s and
  `library.rs`'s `OnceLock`s (F20) and `cache`'s code interner. `NO_ETA` is
  part 1's F4, and `without_glue` is F12. No address-keyed table in scope
  decides anything. The only `ptr::eq`s compare against marker statics
  (`module.rs:1307,2925`) or a local, and `collections::HashMap`'s hasher is
  fixed across runs.
- **`patlet.rs`.** Its `unreachable!`s follow a `force` and a successful
  unification or `record_pattern`, which forces too, so they're unreachable
  from user input.

## The 1 November review's findings in this scope

| Finding | Status |
|---|---|
| §3.3 Keep the logical trust boundary explicit | **Largely fixed** on the elaborator side. Replay is documented as trusted, and `admit_replayed` is the one path to `admit_trusted_*`. That's enforced by module privacy and a comment, not by type. Core's `pub` API is still open (core review). F1 is a bug inside the trusted path. |
| §3.1 Every table in rollback, replay and the dump | **Open for `Builtins`.** The replay undo skips them (F1), and the dump omits them (F10). |
| §4.1 Manual save/restore | **Open:** `kernel::without_glue` (F12), and `timings` (F23). `opaque.rs` and `families.rs` are fine. |
| §3.5 Internal error classification | **Open, grown:** ten more derive sites (F6) and the `module.rs`/`library.rs` sites (F21). |
| §4.4 Large files | **Worse here:** `effects.rs` 2,379 → 5,231 and `module.rs` 1,916 → 3,529 since 20 Oct. `equations.rs` is 7,406 (F7). |
| §2.5 Comments explain invariants | Still true: `equations.rs`, `shared.rs`, `cache/mod.rs`, `builtin_docs.rs` and `patlet.rs` each argue their soundness in the module doc. One stale claim: `nav_tag`'s doc (`cache/mod.rs:288`) says "entries made with less aren't used", but the key needs an exact match. |

## Questions for Matt

- **D2720: should a library file that fails to check fail every later
  request for it in the same run, with its original errors?** [rec: yes.
  Retrying in the same session would fail again, and the alternative is
  today's misleading "dependency analysis missed" (F3).]
- **D2721: should a derive failure that the deriver's plan was meant to rule
  out be an `E-INTERNAL` error on the type, rather than a note that appears
  only when the derived thing is used?** [rec: yes. It's a compiler bug, and
  today no test sees it. Decide's designed "not decidable" stays a note
  (F6).]

## Tickets to file

1. **Replay undo and the dump** (F1, F10, F11): undo through the kernel's
   mark and rewind, print all of `Builtins` in the dump, bind builtins on
   replay only for library entries, and add a forced-refusal test. Opus
   (trust boundary), 45-60 min. First.
2. **Row settling before SW-1581** (F2, F16): retry the call's own
   comparisons before settling, use `settling_empty`, type and note the
   fresh tails, then retry SW-1581. Opus (core inference), 60-90 min.
3. **Small row and instance robustness** (F8, F9, F15, F17): DeepSeek,
   40 min.
4. **Glue and timing guards** (F12, F23), with part 1's F4 if that isn't
   done yet. DeepSeek, 30 min.
5. **Derive budgets** (F5, F24): a budget per deriver, a measurement on a
   100-constructor type, and one `declares_instance_of`. Sonnet, 45 min.
6. **One failure path for generated declarations** (F6, F18), after D2721.
   Sonnet, 60-90 min.
7. **Library load state** (F3, F20), after D2720. Sonnet, 30-45 min.
8. **Navigation cost** (F4, F19): no expression types during library
   loads, and cheaper index rebuilds. Sonnet, 45-60 min.
9. **Instance hints and budgets** (F13, F14): lazy hints, and the budget
   error in `findable`. Sonnet, 40 min.
10. **Branch-equation lemma list** (F22): one list and a resolve test.
    DeepSeek, 30 min.
11. **Splits in a quiet window** (F7): `effects.rs` with unit tests for
    `align` and `mapping` (Sonnet, 60-90 min), and `module.rs`'s
    `elaborate_namespace_untimed` (Sonnet, 60 min).

F21 joins part 1's F5 design note.
