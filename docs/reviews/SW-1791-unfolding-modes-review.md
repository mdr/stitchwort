# SW-1791: review of SW-1782, cached unfoldings record their modes

**Reviewed:** `lane/SW-1782` at 5a19c406d (code, tests, `docs/testing.md`) and
2c831b28e (the lane's note,
[SW-1782-unfolding-modes.md](SW-1782-unfolding-modes.md)). Independent Opus
review under D2364 (kernel-adjacent caching in `crates/core/src/value.rs`).
Review only: no code changed.

**Verdict: merge.** No fixes needed. Two small doc wordings could be sharper
(§7), and SW-1642 will conflict on `Unfolding` (§1.5). The std + AoC hash dump
isn't needed before merge (§6).

## 1. Is the mode set complete?

I listed every piece of machine or environment state that `unfold_now`, `unfold`,
`eval_step`'s constant case, `glues`, `folds`, `hidden`, `erases_result`,
`float_def` and `native::run` read (`grep 'g\.machine\.\|g\.env\.builtins()'`
over `value.rs`). They fall into three groups.

**Machine state, set by guards outside the machine:** `glue`, `erasure.active`,
`erasure.program_running`, `transparent`. These four are the key. Every write to
them (`check.rs`, `elab/src/{closing,goals,auto,interfaces,opaque,kernel,unify}.rs`,
the instrumentation) happens between machine runs, and nothing inside a run (the
native, float and `nat_add` callbacks get `force` and start nested runs in the
same modes) changes them. So `Modes::now` at `set` time, at the end of the force
(`Frame::Unfolded`), equals the modes in force for the whole unfolding. The lane's
§3 says the same; I checked it independently.

`apart_sets` is only added to, so a name keeps its meaning; not a mode. The budget
isn't one either: running out raises an error, and an error leaves the cell
unset.

**Environment configuration, which needs `&mut Env` to change:**
`disable_natives`, `disable_float_natives`, `float_natives_outside_runs`,
`disable_compact_text`, data types' eta flag, definitions' `opaque` and
`fold`/`theorem` flags. None can change while an `Ev` is borrowed, so none can
change during a computation. A cell could outlive a change only if a `Value`
were kept across one. The only places that flip these mid-session are
differential tests (`driver/tests/{int,natives,nat_add_rule,int_patterns,compact_text}.rs`,
`float_gate.rs` builds a fresh session per mode), and they evaluate their terms
again after each flip. With natives off, natives' definitions glue (`glues`
reads `native(id)`), but natives and their case trees agree by design (the same
tests check that), so a stale cell would change representation, not meaning.
Not worth a key field; worth knowing if a future test keeps a value across a
flip.

1. **Metavariable epoch:** kept as before (`0` or the reader's). Correct.
2. **Natives on/off:** environment configuration, above. Not needed.
3. **Opaque definitions:** `hidden` reads `def.opaque` (static),
   `program_running` and `transparent`; all covered. The float natives
   (`float_def(id, program_running)`) are covered by `program`.
4. **The reference evaluator** (`reference.rs`) never glues
   (`Value::Call(..) => unreachable!` at its read-back) and never touches a
   cell. Out of scope by construction.
5. **The eta hold (lane/SW-1642).** There, `eta_held` is `has_native(id)`
   (static) and `eta_case` is `data.eta && !program_running` (static plus a
   key field), so record eta adds no new mode. Two notes for whoever merges
   second:
   - SW-1642 changes `Unfolding` to `{ value: RefCell<Option<(u64, Value)>>,
     base: Option<Rc<Unfolding>> }` (fields of a call share the base call's
     cell). That's a textual conflict with `Kept`: the merged form is
     `value: RefCell<Option<Kept>>` plus `base`, with `get`/`set` as here and
     `detach` taking `Kept { value, .. }` out of `unfolding.value`.
   - If record eta ever gains a machine-level switch (an "eta off" mode for
     the kernel, say), it must go in `Modes`.

**One input outside the key, not a risk today: the environment growing.** A
group's members have no body until the group is admitted, so an unfolding made
before admission keeps them neutral, and a reader after admission would get that
neutral where fresh evaluation would unfold. Today no cell crosses an admission:
the session-long values (`Def::ty_value`) are made unglued and hold no calls.
closed-type-values.md §4 step 2 (a glued `Def::ty_value`) should check this
before it relies on cells living for a session; step 2's design note is the
place for it.

## 2. "A glued unfolding serves an unglued reader"

**Sound.** A glued unfolding and the unglued one differ only in that the glued
one has `Value::Call`s where the unglued one has their unfoldings. Every call
`needs_forcing`, so every unglued reader that looks inside meets it through
`force`, which reads that call's own cell under the same rule (recursively) or
computes it unglued. Unfolded read-back (`quote`) unfolds every call; conversion
forces calls, and its call shortcuts (`Rc::ptr_eq` on cells, same definition and
equal arguments, `CallMemo`) only find equalities that hold. The kept value is
always forced at its top (`Frame::Unfolded` loops until `!needs_forcing`), so a
reader that takes a cell's value at once (`force_now`) never gets a call where it
expected a head.

None of this is new: before the fix every reader took every cell, and unglued
readers already met glued cells (the lane's note cites `interfaces::locals`).
The fix only removes the other direction.

**Deterministic in meaning, not in representation or steps.**
- *Results:* an unglued `quote`, conversion or `case` gives the same answer
  whichever kind of cell it finds.
- *Steps:* an unglued reader of a glued cell takes the steps to force the inner
  calls, where an unglued cell would cost none. So step counts, and whether a
  tight budget runs out, still depend on what was forced first. That was already
  true of any cache, and the note's §7 says so. Limits are a resource bound, not
  a meaning. Making steps history-free is closed-type-values.md's option 3 (the
  kernel off kept cells), not this lane.
- *One observer of the difference:* a **folded read-back with gluing off**.
  `force_solved` with gluing off returns a call as it is, and a call that
  `matches_at_once` is forced. If its cell is glued, the inner calls are written
  as calls; if unglued, in full. That path is display only (a goal's context
  printed after gluing ended, per `force_solved`'s comment): elaborated terms
  and hashes come from folded read-backs with gluing on, which now never take an
  unglued cell. So the `Unfolding` doc's "what a call unfolds to never depends on
  who forced it first" holds for every reader with gluing on and for every
  unglued reader's results, but not for the shape of an unglued folded print.
  Not worth a code change; see §7 for the wording.

## 3. "The check can only refuse a cached value, never supply one"

True, and overwriting can't disturb a live holder:

- `get` clones the `Value` out (reference counts) and drops its borrow before
  returning; `set` replaces the cell's content. Values are immutable, so a holder
  that took the old value keeps it unchanged. The only shared mutable thing is
  the cell, and it's read only through `get`, which rechecks `fits` every time.
- Overwriting while an outer forcing of the same cell is pending (its
  `Frame::Unfolded` still on the stack): the inner and outer computations run in
  the same modes, so both store values of the same kind for the same call; the
  last write wins, and either is right. A computation never reads its own cell
  half-built: the cell is set only when the force completes.
- `CallMemo` keys on cell addresses but holds the forced values, and lives for
  one outermost `conv` (one set of modes), so an overwrite doesn't change its
  entries' meaning.
- No borrow conflict: `fits` borrows `transparent`, a different `RefCell`;
  dropping the old `Kept` inside `set`'s `borrow_mut` runs `Value`'s drop
  (`detach`), which only unwraps cells it uniquely owns, never this one.
- **Threads:** `Value` holds `Rc` and `RefCell`, so it's neither `Send` nor
  `Sync`. `par_map` (`driver/src/driver.rs`) needs `T: Sync, R: Send`, so the
  compiler rules out sharing a cell across workers; each worker has its own
  session.

**No ping-pong blowup.** A run's modes are fixed, so within one run a refused
cell is recomputed once and then fits. Across runs in alternating modes (an
elaborator and a program reading the same value, say), each switch costs at most
one recomputation per cell reached, which is what no cache at all would cost on
that run. Shared subcalls inside a run still share cells, so there's no
exponential case.

## 4. Cost

- **Memory:** `Kept` adds the transparency set's fat pointer (16 bytes) and three
  bools, about 24 bytes per call cell, on the allocation each `Value::Call`
  already makes; `Value` is unchanged. Each cell also holds a reference to its
  transparency set, which keeps that slice alive; the sets are per-definition
  `Rc`s or empty, so that's negligible. The bench's peak heap agrees.
- **Hot path:** `fits` is four flag comparisons and, for the set, `Rc::ptr_eq`
  first. The pointers differ when equal contents come from different
  allocations; in practice the set is a definition's own `Rc`
  (`def.transparent.clone()`), the elaborator's `opaque.rs` one, or an empty one
  from `Rc::default()` (two empty sets compare by length if their pointers
  differ, so O(1)). The worst case is O(size of the set) per cache hit, only when two
  equal non-empty sets come from different allocations; sets are short lists of
  opaque definitions. `force` itself doesn't change: `fits` runs only in
  `force_now` and `force_call`, both already out of line.
- **Worst case for recomputation:** a cell made unglued and read glued, or made
  under one transparency set or erasure mode and read under another. Bounded per
  mode switch as in §3. The bench's +1,180 steps in 6.48 G (4 cross-mode reads
  over std + rogue) fits the analysis: in normal runs cells rarely cross modes.

## 5. Tests and the instrumentation

**Tests** (`crates/core/tests/it/glue.rs`), all three meaningful:
- `a_call_forced_unglued_reads_back_folded_as_if_never_forced` is the bug in
  miniature: `outer (Succ x)` with a non-matching inner `twice`, read back folded
  with and without an unglued read-back first.
- `an_unfolding_computed_glued_serves_an_unglued_reader` pins both directions by
  step counts: 0 for the allowed reuse, more than 0 for the refused one.
- `an_unfolding_that_saw_an_opaque_body_isnt_used_once_it_is_hidden` covers the
  transparency set and `program` (with erasure on and off, so `program` is
  tested apart from `erasing`).

The one key field without a test of its own is `erasing` with `program` the same
(a cell made while a program runs erasing, read while one runs not erasing).
`erasing` implies `program`, so that pair arises only with
`set_disabled` flipped between two program runs on the same value, which is
test-only. Not worth adding.

**The instrumentation** (`STITCHWORT_DEBUG_FORCE_UNGLUED`): its cost when off is
a `OnceLock` load and a branch per `quote_folded` with gluing on, after the glue
check; `force_unglued` is `#[cold]`. That's per read-back, not per step:
negligible. It runs in its own budget attempt and restores the budget after, so
its errors don't leak; its steps go to `finished_work` (total work), which only
matters when it's on. It's a stronger form of SW-1748's probe and is what makes
the lane's 317-moved-to-0 evidence possible; keeping it, documented in
`docs/testing.md`, is right.

## 6. Hashes

- `hash_stability prelude` on the rebuilt branch: **passes** (24.8 s), so the
  prelude's hashes equal their snapshots, which match the base.
- `glue::` (11 tests, 3 new): all pass.

The lane's dump comparison (std + rogue, fix against base, and fix instrumented
against fix) is the stronger evidence, and its result (no line moves) is
consistent with the 4 cross-mode reads it counted.

**Should the std + AoC dump comparison run before merge?** Not needed. The fix
can only move a hash where some reader with gluing on was handed an unglued cell,
and in that case the new hash is the order-independent one: a move would be the
fix doing its job, not a regression, and the migration cost of a moved hash
doesn't count. It would be informative (AoC uses `decide`, an unglued forcer,
more than std does), so it's worth running when convenient, for the record, or
with the next daily tier; it shouldn't gate the merge.

## 7. Small points (optional)

1. The `Unfolding` doc says "what a call unfolds to never depends on who forced
   it first". True of what it means and of everything written with gluing on; a
   folded print with gluing off can still differ in shape (§2). Could read: "so
   no reader with gluing on is handed an unfolding made unglued, and what a call
   means never depends on who forced it first".
2. The note's §4 "24 bytes" is right; it could say the per-hit comparison is
   O(1) except for equal sets from different allocations (§4 here).

Neither blocks the merge.

## 8. Checks run

| check | result |
|---|---|
| release build of the branch (`task test:one`) | built, 2 m 47 s |
| `glue::` (core `it`, 11 tests) | 11/11 pass |
| `hash_stability prelude` | pass, 24.8 s |
