# SW-2415: erase determined fields, stage 1 (lane report)

Stage 1 of docs/proposals/erase-determined-fields.md (SW-2406; D3429 and
the orchestrator's calls on §9 Q2-Q5): the interpreter and native code no
longer store a constructor field that the constructor's result indices
determine, and a match that reads one rebuilds it. JS (stage 2, SW-2416),
the reference evaluator and the kernel are unchanged. The design as built is
in the note's "As built" section; this is the lane's report.

## What was built

- **`crates/core/src/determined.rs`** (new; outside the kernel's admission,
  nothing hashed, nothing the kernel reads).
  - `ctor_determined(g, d, c)`: from the declaration alone, which fields are
    determined. Rule: data with indices, not a proposition, not a record;
    the field isn't erased, its type is the prelude's `Nat`, and some result
    index is the field under zero or more `Succ`s.
  - `ctor_stored(g, d, c)`: neither erased nor determined.
  - `Replay`: a definition's case-tree context (values and types by level),
    refined as `check.rs` refines it: `of_def` (the telescope's first
    `arity` parameters), `branch` (bind the fields, `unify_index::unify` the
    indices, substitute the matched constructor), `num_arm`, `num_default`
    (the apart marking, as the kernel does it), `assume_ctor` (an empty-row
    variant's fixed row). `branch` returns each determined field's
    `Rebuild { source: Term, minus: BigUint }`.
- **`crates/rt`**
  - `erasure::stored_fields` / `stored_count`: the one layout predicate,
    used by construction, matching, `TypeInfo`, the fixed `Shapes` check,
    the effect clauses' operation fields (`clauses.rs`) and `Comp`'s check
    (`effect.rs`).
  - `lower.rs`: the lowerer records its path down the case tree (`Tree`,
    `TreeStep`); a generic `match` arm binds a slot for each determined
    field, lowers the body, and if the body reads the slot, replays the
    path to the branch and wraps the body in `let slot = rebuild` (a
    rebuild that reads another rebuilt field goes inside it).
  - The debug check: `erasure::checking_rebuilds()` (a thread-local guard)
    or `STITCHWORT_CHECK_REBUILDS`: determined fields are stored as well,
    and every arm computes every determined field's rebuild and runs
    `if EqNat(rebuild, stored) then body else unreachable`.
  - The census: `erasure::census_rebuilds()` / `take_census()`, and
    `STITCHWORT_REBUILD_CENSUS` printing to stderr: each rebuild lowered
    that isn't a variable or a number under `Succ`s, less a number.
  - `specialise.rs`: `Specialiser::row_constants` (factored out of
    `make_body`) for the variant's replay.

For `Fin.toNat` the IR is now (snapshot `it__lower__determined_fields_are_rebuilt`):

```
fn Std.Fin.toNat(v0, v1) {4 slots} =
  match v1: Fin {
    FZero => 0
    FSucc(i: v2) =>
      let v3 = %Nat.sub(v0, 1)
      %Nat.add(Std.Fin.toNat(v3, v2), 1)
  }
```

and `VCons` cells have two fields (`Vec.map`'s loop fills field 1, not 2).

## How a rebuild is found, and why it always exists

The lowerer doesn't key anything by position: it replays, along the path it
is lowering, exactly the refinements the kernel made checking that path
(the same `unify_index::unify`, the same `substitute_in`, in the kernel's
modes and the definition's transparency set). Specialised bodies keep the
case tree's shape except that an empty-row variant drops the cases on its
row parameters, so the variant's replay starts with those parameters fixed
at their constructor, which is what the kernel knew inside that branch. The
replay checks at every match that it has as many variables in scope as the
lowerer.

After unifying the scrutinee's indices `is` with the constructor's `js`,
for a determined field `f` (with `jₗ = Succᵏ f`):

1. if `f` was solved, its value `t` is a value of the refined context: the
   rebuild is `t` read back (calls kept as calls);
2. otherwise `f` is still free, and some variable `y` bound before the
   fields was solved as `Succᵏ' f`: the rebuild is `y - k'`.

Why one of them holds: unification walked `jₗ` from the top, and at each
`Succ` the scrutinee's side was a `Succ` (injectivity), a number (split into
`Succ`), or a flexible variable `y` (solved as the rest of `jₗ`, which is
case 2); reaching `f`, the other side was solved into `f` or `f` into it, or
`f` had already been solved (case 1). The walk's other side starts in
`is`, the context before the fields, and every solution is substituted into
that context's values, so a free field that the walk reached under `Succ`s
shows up in the value of a variable bound before the fields: case 2 never
needs to look at another field. Stuck is `E-INDEX-STUCK` and a conflict is an impossible branch with
no body, so neither reaches the lowerer. The rebuild's free variables stand
for themselves in the refined context: parameters (kept at run time, D141's
second half) and fields (stored, or rebuilt by case 2 from a variable
before the fields), so each has a slot; that the value equals the field the
kernel's value has is the erasure contract (D863). If neither case held,
lowering would stop with an internal error rather than guess.

Evidence beyond the argument: with the debug check on, every branch of
every library definition (lowered whole) has its rebuilds found, and those
the library's tests reach are compared with the stored fields; likewise
the effect examples, the new example and every AoC day (below). A rebuild
deliberately off by one makes the library check fail (tried, then put
back).

## Affected types and fields

std (snapshot `it__lower__the_library_s_determined_fields`): `Fin.FZero n`,
`Fin.FSucc n`, `Vec.VCons n`. `Grid` is built on `Vec`. `aoc/` and the
roguelike declare no indexed families; the AoC days that use `Fin` or `Vec`
are 2021 days 9, 11, 15 and 2025 days 3, 4, 7. Census of rebuilds that
compute a call: none in std, none on those six days.

Not determined, and so still stored, under this stage's rule (narrower than
the note's §2.1): a determined-shaped field whose type isn't `Nat` (the
note's `Ty` example, a `Fin` field under `FSucc` in an index as in the new
example's `Slot`), any field of a record, and a field under a definition's
call in an index (`Nat.add size 2`).

## Counts that moved

- **Steps and frames.** A determined field's argument isn't evaluated at
  construction any more. In the new example, `MkCount (List.length xs)`
  stops calling `List.lengthOnto` (5 fewer calls), as §6.1 predicts. The
  example's `countOf` rebuilds `n` as `List.length xs` (the census's one
  entry), which costs that call where the branch reads `n`; nothing in std
  or `aoc/` has that shape. On the six `Fin`/`Vec` AoC days, `--profile`
  call counts (frames entered, per definition) are identical before and
  after. No pinned step, frame or tick count in `task test:lane AREA=rt`
  or `AREA=native` moved.
- **Allocation traces.** No expectation needed changing: the trace tests
  compare the machine with native code, which share the layout.
- **Results, messages, hashes.** Every AoC day prints the same natively as
  the base build; std's hashes, the prelude snapshot and every other
  example's are unchanged (the new example got its own snapshot). JS output
  for the new example is the same.

## Numbers

Instructions retired (`/usr/bin/time -l`, native executables from `build
--native`, real inputs, lowest of 3), base `69de3042d` built in this
worktree against this stage:

| Day | Before | After | Change |
|---|---|---|---|
| 2025 day 3 | 1,552,219,433 | 1,532,463,608 | -1.3% |
| 2021 day 9 | 1,826,459,138 | 1,814,652,335 | -0.6% |
| 2021 day 11 | 6,284,733,702 | 6,295,201,912 | +0.2% |
| 2021 day 15 | 18,280,726,988 | 18,299,164,174 | +0.1% |

Wall times 0.09-1.2 s, within noise of each other. The layout alone is
worth little; the point is SW-2398 (`Fin` as a machine number), which needs
it. (Main's release binary at the time already had SW-2405, so it isn't the
base: it gave 1.582 G / 1.843 G / 6.290 G / 18.657 G.)

## Commands run

- `task test:one -- determined_fields_are_rebuilt` (new snapshot), then the
  new and touched tests together: `-E 'test(/determined_fields|effect_examples_agree|the_library_rebuilds|the_library_s_determined|the_library_lowers_and/)'`:
  8 passed.
- `task test:one -- every_example_lowers`: passed (85 s).
- `task test:lane AREA=rt`: 65 passed. `task test:lane AREA=native`: 68
  passed.
- `task snap:hashes NAME=determined-fields`, then `task test:one -- -E
  'binary(library) & test(/hash_stability|bound_to_the_prelude|extraction_stability/)'`:
  9 passed (`prelude`, `examples`, `projects` among them).
- `task aoc:check`: 287 namespaces checked (76 s).
- `task bench:compare:check`: 66 ok, 0 skipped, 0 failed (9.6 min; the
  check runs every runner, not a time budget).
- Every AoC day natively, with and without `STITCHWORT_CHECK_REBUILDS`:
  57 of 57 the same; on the machine for the six `Fin`/`Vec` days: 6 of 6.
  Every AoC day natively, base build against this one: 57 of 57 the same.
- `stitchwort run` (machine), `--native`, `--reference` and `--js` on
  examples/accept/determined-fields.sw: the same line.
- `cargo fmt`; `cargo clippy --release -p stitchwort-core -p stitchwort-rt
  -p stitchwort-native --all-targets -- --deny warnings`: clean.
  `stitchwort fmt` on the touched `.sw` files: no change.

## Unsure points

- The replay runs with gluing on and the definition's transparency set,
  while `set_run_body` checks a run body with gluing off. The values are
  convertible either way and unification's outcome doesn't depend on
  gluing; a run body whose check depended on an opaque definition's
  transparency differently from its body's would be the place to look if
  the replay ever reports "unification is stuck".
- The debug check covers `Nat` fields only, which under this rule is all of
  them. Widening the rule beyond `Nat` needs a general equality for the
  check (or a per-type one).
- Lowering a whole program now replays unification once per branch that
  reads a rebuilt field (a path from the root each time). Not measured
  separately; `every_example_lowers` and the library lowering ran in their
  usual times.

## What SW-2398 needs next

1. Rebase onto this; `Data::nat_shape` must count the fast runtime's stored
   fields, not non-erased ones. It's in core and doesn't know the debug
   check, so it should call `determined::ctor_stored`, and the runtime
   should not treat a type as Nat-shaped while `checking_rebuilds` is on
   (the cells then hold the determined fields, so `Fin` isn't Nat-shaped
   there), or the check should keep the Nat layout and only compare.
   Simplest: `nat_shape` takes the stored-field predicate as an argument,
   and rt passes `erasure::stored_fields`.
2. A rebuild path step through a Nat-shaped type isn't needed by this
   stage's rule (paths go through `Nat`'s `Succ` only).
3. Then its own items: the example's header comment, the snapshot
   (`FSucc(4, FSucc(3, FZero(2)))` becomes the literal 2), `Fin` cases in the
   native agreement test, and its step pin after SW-2405.

## Findings

1. **Widen the rule beyond `Nat` fields** if a program wants it: a field of
   any non-quotient type that is an index or under constructors of an index,
   with projection steps through cells (a one-arm match) and a general
   equality for the debug check. Nothing in std or `aoc/` needs it.
2. **`Vec.fromListN`'s doc comment** described storage; reworded here.
   Others in std may describe `Fin`/`Vec` cells; none found by grep.
3. The note's finding 1 stands (index arguments nothing reads are still
   computed by callers: `Count.value (count xs)` computes `List.length xs`
   to pass `n`).
