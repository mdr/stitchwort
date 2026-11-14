# SW-3031 review: Bool as proposition stage 3b

Opus paper review (no builds, no tests) of `lane/SW-3031` at `5b6ee18e0`,
against `docs/proposals/bool-as-proposition.md` §5.4, §6.7, §11 and §13,
`docs/proposals/decidable-record.md` and `docs/core.md`. Line numbers are in
the lane's worktree.

**Verdict:** sound and mergeable as far as the reader goes. No High findings.
Two Medium findings, both in `W-DECISION-TEST`: false positives on generic
instances, and results that depend on what else the run loaded (and so on
the check cache). Fix them before the warning reaches the AoC sweeps, or
merge with the warning and fix it next. On D3541, recommend **(a)**:
generated `T.%sameReads` readings.

## 1. Soundness and trust: no findings

- **Every emitted term is checked by the kernel.** `step_proof`
  (`reading.rs:1008-1039`) writes `Decidable.sound [p] d h`,
  `Decidable.complete [p] d q`, `Decidable.refute [p] d h` and
  `Decidable.toBoolOfNot [p] d n`. Each is a plain application, built by
  `applied` (`:991-1002`) from the callee's own Pi telescope, so implicitness
  comes from the declaration, not from a guess. `Found.prop` is only what
  the elaborator expects. A wrong guess there would fail at elaboration or
  in the kernel's re-check of the definition, never be accepted.
- **`p` is never taken from a name's statement.** In case 1
  (`Decidable.holds [p] d`, `:834-842`), `p` is the test's own implicit
  argument, so `d: Decidable p` holds because the test type-checks. In
  case 2 (`(f x).holds`, `:843-860`), `p` is read off `f`'s declared type
  applied to the call's arguments. So no fact is read through a `d` of the
  wrong proposition: the proposition is always the one `d`'s type, or the
  test, states, up to conversion.
- **Registry.** `Refute = "Decidable.refute": Def => "[p] d e"` and
  `ToBoolOfNot = "Decidable.toBoolOfNot": Def => "[p] d n"`
  (`crates/core/src/registry.rs:374-375`) match the declarations' binders
  (`std/core/Decidable.sw:31,38`). Neither is in `LIBRARY`
  (`registry.rs:71ff`), so both are core built-ins. They are bound only
  while the prelude loads and never rebound (invariant 2, `:9-11`), and
  their shapes are checked by `check_shape`. As with SW-3002's `Ordering`
  entries, a shape checks binders, not statements; the kernel checks the
  statement at every use. Moving `toBoolOfNot` into the core is what makes
  it bindable as a core built-in. `builtin_def` (`check.rs:6802`) fails with
  `E-UNKNOWN-NAME` only before the prelude has loaded.
- `decision_reads` (`:869-879`) builds `¬p` as `Not p` from the registry.
  `refute`'s stated `¬p` is the same up to unfolding `Not`, so the two
  agree by conversion.

## 2. Stuck detection: consistent with §5.4; two Low gaps

- **When a decision counts as stuck.** `stuck_decision` forces `d` to weak
  head normal form (`:861-865`). It is stuck if the result is a neutral
  without a meta at its head: a variable, a call stuck on one (a case tree
  stuck on a variable is a neutral headed by a definition), an opaque
  definition or an assumption. A decision that computes to a record is not
  stuck. Its test is then unfolded through `holds` (`unfold_once`'s
  projection path, `core/src/value.rs:916-924`) and read by the test's own
  reading. A stuck decision's `holds` can't compute any further (a
  projection of a neutral stays stuck, and record eta doesn't make it
  reduce), so step 2 never pre-empts a reading that step 3 would have found
  on what the test computes to. `stuck_decision` runs before the head
  lookup at every unfolding step (`:766-768`), which is §5.4's order. A
  folded call with its own reading (`isSmall n`) is never a `holds` test,
  so its reading wins. Case 2's form `(f x).holds` exists only when the
  call's unfolding is stuck (`names_folded_fields`, `value.rs:2397-2404`),
  so it agrees with the force check.
- **L1. A decision stuck on an unknown inside it is read.** Only a meta at
  the head is excluded (`:862`). `(inst ?m).holds`, where `inst` cases on
  `?m`, reads as `P` now. Once `?m` is solved it might compute to a record
  whose test reads as something else, equivalent but shaped differently
  (`Both` against a record pattern). That breaks §5.6's "the reader never
  solves an unknown" in spirit: the answer depends on when solving happens.
  This is rare, because facts have their metas solved by the time a pattern
  reads them. Suggested fix: treat a decision blocked on a meta as a leaf,
  if the machine can say what blocked it.
- **L2. Unglued and opaque projection forms aren't recognised.** Case 2
  matches only `Value::Call(…, [.., Proj(Decidable, 0)])`. Two forms are
  left as leaves: `d.holds` as `Neutral(Var d, [Proj])`, which an unglued
  value with no written type gives (`as_written` usually covers it), and a
  field of an opaque decision's call, `Neutral(Def f, [App.., Proj])`. The
  first would need the variable's type, which `stuck_decision` doesn't have
  (it takes `&Ev`, not a `Ctx`). Low: today's tests pass with glue on and
  off.

## 3. Warning crediting: correct; one leftover leak (Low)

- Body warnings go to `attempt.lambda_warnings` (`matching.rs:1276`,
  `rewrite.rs:1042`, `redundant.rs:67`, `records.rs:356`,
  `families.rs:487`), which is drained per member (`lib.rs:2987-2993`).
  Signature warnings are drained right after each signature (`lib.rs:2800`,
  `decreasing.rs:942`). So when the new drains run (`lib.rs:3017`,
  `partial.rs:626`, `decreasing.rs:989`), `unit.warnings` holds only that
  member's `after_definition` warnings, and crediting them to `item` is
  right. Before the change they waited for the next drain, which credited
  them to the next declaration. After a unit's last declaration they could
  carry into whatever drained next, because `module.rs:2479-2486` returns
  without draining `unit.warnings` for a signature group.
- **Rewind:** marks are taken between loads, and `Unit` is restored whole
  (`rewind.rs:41-45`). The change doesn't touch it.
- **Cache:** a unit's warnings are stored and replayed as a list
  (`cache/mod.rs:1584-1590`). Which item a warning is credited to changes
  only its position in that list. What does matter to the cache is *which
  unit* raises a warning: see M2.
- **L4 (existing before this lane).** `W-DECREASING-UNFOLD` is pushed from
  `plain_view_or_not` (`decreasing.rs:1490`) during `decreasing_equations`,
  after the new drain at `decreasing.rs:989`. It still carries into the
  next drain. The same goes for anything `after_definition` raises through
  `definition` and `definitions` (`lib.rs:2594`, `:2634`): generated
  declarations, which skip the new warning but not the others. A drain at
  the end of `decreasing_group`, and in `module.rs`'s signature branch,
  would close both.

## 4. Hash and proof stability: no findings expected; one check for the verifier

- Hashes are content-addressed and ignore names: in the lane's own snapshot
  `Main.isSmall` and `Main.smallTest` have the same hash
  (`library__hash_stability__reading-decision-test.snap`). The moved
  `toBoolOfNot` has the same statement and body, so its hash, and the hash
  of everything that refers to it (guarded arms' generated equations,
  `omega` proofs), should be unchanged.
- **Which files load is unchanged where it matters.** `omega`'s `LIBRARY`
  used to load `Decidable/Decidable.sw` through `toBoolOfNot`'s name, and
  `omega` needs `notNotOf` from that file (`omega.rs:676`). Adding
  `Std.Decidable.notNotOf` (`omega.rs:151`) keeps the file loaded, which
  was the right fix. `GUARD_LEMMAS` (`module.rs:3643-3649`) already names
  `notNotOf`.
- No pins are involved: registry entries are checked by shape, and only
  natives are pinned (`pins.rs`).
- **Not verified here:** I ran nothing. The verifier's batch should include
  the `hash_stability` snapshots and one example that uses guarded arms or
  `omega`, to confirm "no example hash changed".

## 5. W-DECISION-TEST

- **M1. False positives on generic instances (Medium).**
  `check_reading_decisions` (`reading.rs:1503-1531`) compares a reading
  with every instance whose decided proposition has the same head
  (`prop_head`). `decision_mismatch` then fits the instance to `P` with
  `auto::instance_for`, which fills `Decidable` parameters by recursive
  search (`auto.rs:1216-1225`). Take a reading whose `P` is a connective or
  relation that std decides generically. For example, `@[reading] inRange
  lo x hi ↔ lo ≤ x ∧ x ≤ hi` matches `Decidable.and`
  (`std/core/Decidable.sw:150`), whose test is `&&` (`TestHead::And`)
  rather than `inRange`, so the user's reading warns:
  "`Decidable.and` decides `lo ≤ x ∧ x ≤ hi` by a test other than …". The
  same happens with `∨` and `Decidable.or`, `¬ …` and `Decidable.not`, and
  `n ≤ 10` and `Nat.decLessEq`. The user can't fix any of these. I followed
  this through the code but didn't run it. Std is quiet today only because
  `Bool.andReads`'s test is itself `&&`. §13's rule ("the decision's
  `holds` is `t`") makes sense only when `P` is the test's own
  proposition. **Fix:** compare only when `P` is its head applied to the
  reading's own parameters, each once, which mirrors the test-side shape
  rule (`List.Mem x xs` and `Small n` qualify; `lo ≤ x ∧ x ≤ hi` and
  `n ≤ 10` don't). Additionally or instead, skip instances that take a
  `Decidable` parameter, since their test is built from other decisions.
  Add an accept example with an `∧` reading and no expected warning.
- **M2. The result depends on what else the run loaded (Medium).**
  `check_reading_decisions` scans every instance in the kernel environment
  (`reading.rs:1513-1517`), and `check_instance_readings` scans every
  positive reading in `tables.readings` (`:1545-1548`). Neither is limited
  to the current unit and its imports. Readings themselves are safe from
  this because a test's head is always visible (`E-READING-PLACE`). A
  proposition's head is not, so the warning has nothing to keep it inside
  what the unit can see. Three consequences:
  - Say unit A has the reading and unit C, which doesn't import A, has the
    instance. Whether the warning appears, and in which unit, depends on
    which was checked first.
  - If C was checked first, A raises the warning and the check cache stores
    it in A's entry. A's key doesn't cover C, so editing C leaves a stale
    warning that is replayed with A.
  - A library reading loaded on demand after a user's instance raises the
    warning inside the nested library unit (`library.rs:823-838`), where it
    is probably dropped or stored with that file.

  **Fix:** limit both scans to the current unit and the units it depends
  on, so the result is a function of the unit's key. The pairing is still
  caught by whichever side is checked second, as long as each can see the
  other.
- **L3. Equality propositions are never checked (Low; misses warnings).**
  `prop_head` returns `None` for `Value::Eq` (`reading.rs:1335-1341`). So a
  reading `same x y ↔ x = y`, paired with a hand-written `DecEq` that tests
  something else, is never compared, and that is the `==` case §13 cares
  about most. If wanted, key it on `Eq` and the head of the type argument.
- Checking only the head is the right call, for the reason the lane gives
  (arguments come from sub-decisions). Skipping generated instances (`%` in
  the name) is right as well.

## 6. D3541: recommend (a), generated `T.%sameReads`

(a) generates, beside each derived `DecEq`, the readings
`T.%same r s = True ↔ r = s` and `= False ↔ r ≠ s`. (b) teaches the reader
to fall back to a decision's `sound` and `complete` when the decision
computes but its test is a leaf.

1. **One reading per test** (D3487 as amended: "one per test, declared
   with the test"). Under (a) the reading belongs to `T.%same`, so it is
   the same whether a fact shows up as `(x == y) = True` (unfold `holds`,
   then find `T.%same`'s reading) or as `T.%same x y = True` after a
   `match` or an unfold. Under (b) the reading depends on the route: the
   same test reached without the decision is a leaf, and one test reached
   through two instances of different propositions reads two ways.
2. **(b)'s trigger is fragile.** "Leaf" means no reading within 8 unfolds.
   For a derived **record** type, `T.%same x y` on neutrals takes its only
   branch by record eta and unfolds to `(DecEq.decide x.f y.f).holds &&
   …`, which `Bool.andReads` reads as a conjunction of field facts, not as
   a leaf. A one-field record would read as `x.f = y.f`. So under (b),
   `(x == y) = True` would read as `x = y` for sum types and as field
   conjunctions for records. I traced this through `derive.rs:49-53` and
   `value.rs:2412-2416` but didn't run it. If it holds, the proposal's
   "on a derived type is a leaf" (§11, "Stage 3 as built") is inaccurate
   for records today too. (a) looks up the folded `T.%same` first, so
   every derived type reads as `x = y`.
3. **(a) is a table entry**, so stage 5 (`auto` and `cases` on the reader)
   and `omega` on the reader's table get it with no special case. (b) is
   logic that only the reader has.
4. **(a) is cheap.** `derive.rs` already makes `T.%sameSound` and
   `T.%sameComplete` (`:55-63`). The positive reading is
   `{ forward = T.%sameSound r s, backward = T.%sameComplete r s }`, and the
   negative one comes from `refute` and `toBoolOfNot` on the instance. Its
   test `T.%same [a] [decEq] r s` passes every parameter once, so it fits
   the shape rule. It lives in `T`'s module, so `E-READING-PLACE` is
   satisfied. Snapshot churn is migration cost (D2303). One thing to
   watch: D3537's ordering edges come from syntax, and nothing names
   `T.%same`. The generated reading has to be filed with the derived
   instance, before anything that uses `==` on `T` is checked. That holds
   if it is made in the same step as the instance.

(b)'s one advantage is that a hand-written test-first instance whose test
has no reading would read too. But §13 asks that author to give the test a
reading, and the author can, because the test is a named function.

## 7. Other Low findings

- **L5.** `equations.rs:4509-4510` and `omega.rs:674,677` still look up
  `Decidable.refute` and `Decidable.toBoolOfNot` by qualified name. Both are
  core built-ins now, so `Builtin::Refute` and `Builtin::ToBoolOfNot` would
  do, and `BranchLib::to_bool_lemmas` could stop being an `Option`.
- **L6.** `docs/core.md:556` lists the core's `Decidable` declarations
  (`Decidable.refute`, …) but not `Decidable.toBoolOfNot`.
- **L7.** `read_note` (`check.rs:1169`) runs a reading lookup, up to 8
  unfolds plus a force, on every `E-TYPE-MISMATCH` whose found type is a
  test fact, including mismatches that a speculative attempt throws away.
  The cost is bounded, and its errors are ignored. Worth remembering if
  mismatch-heavy elaboration ever profiles slow.
- The guide and `docs/syntax.md` text match the behaviour. `syntax.md`'s
  "`x == y` … whose `==` is `(DecEq.decide x y).holds`" is case 2, and the
  claim is correct.

## Summary

| # | Rank | Finding |
|---|---|---|
| M1 | Medium | `W-DECISION-TEST` blames generic std instances (`Decidable.and`/`or`/`not`, `Nat.decLessEq`) for any reading whose `P` is a connective or relation, e.g. an `∧` reading |
| M2 | Medium | `W-DECISION-TEST` scans every loaded instance and reading, not the unit's dependencies: depends on run order, stale in the check cache, likely lost in on-demand library loads |
| L1 | Low | A decision stuck on a meta inside it is read as `P` |
| L2 | Low | Unglued `Neutral(Var d, [Proj])` and opaque-call field forms aren't recognised as stuck decisions |
| L3 | Low | Equality propositions are never checked by `W-DECISION-TEST` |
| L4 | Low | `W-DECREASING-UNFOLD` and generated definitions' `after_definition` warnings still carry into the next drain (existed before this lane) |
| L5 | Low | `refute` and `toBoolOfNot` are still looked up by name in `equations.rs` and `omega.rs` |
| L6 | Low | `docs/core.md` doesn't list `toBoolOfNot` in the core |
| L7 | Low | `read_note` does reader work on discarded mismatches |
| D3541 | — | Recommend (a): generated `T.%sameReads`, both polarities |
