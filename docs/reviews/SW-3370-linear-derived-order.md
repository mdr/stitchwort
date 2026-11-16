# Review: SW-3370, derived `==` and `<` linear in the constructor count

Reviewer: Opus review lane, 15 Nov 2026. Branch `lane/SW-3370` (4c057ad07,
84fd02f6c) against `main` at 48135f42a. This change generates kernel terms, so
it gets an Opus review (D2364).

**Verdict: merge.** Nothing found that blocks it. The generated terms are
right for every shape the plan admits, and every law states what it stated
before. Run-time results are the same in the interpreter and the native
build. The findings below are all low: doc fixes, one brittle spot to tidy,
and a known performance trade-off to watch.

## What I checked

- **Plan scope.** `field_plan_for` (derive.rs ~446-470) still refuses mutual
  groups, propositions, indexed families and types with no constructors
  before anything is generated. Data fields that depend on earlier fields are
  refused too. Proof fields may mention earlier *data* fields, but not
  earlier proof fields, and their carrier may not depend on fields. So the
  new kernel builders only ever see: no indices; data fields closed over the
  parameters; and proof fields in `Prop` whose types mention earlier data
  fields. Mutual groups stay refused until stage 3, as intended.
- **`T.%C%k%at` (derive.rs 900-1000), checked against docs/core.md's `Case`
  rule.**
  - In the context `params, s, h`, `Case(1, …)` matches `s`. The fields come
    after everything in scope, so `Var(n)` is `h` and `Var(n-1-k)` is field
    `k`. Both indices are right.
  - In another constructor's branch, the refinement makes `h : T.%tag (C' …)
    = c`, which computes to `c' = c`. So `Nat.equalFalse c' c rfl h : Void` is
    well typed.
  - `Void.absurd` is used for data fields and `Void.exfalso` for proof fields
    (`field_sorts[k] == Prop`). Erased non-`Prop` fields are refused by the
    plan, so data fields are in `Type 0`, which `Void.absurd [a]` covers.
  - Dependent proof fields: the type of field `k` is evaluated with the
    earlier fields bound to `C%j%at s h`. In the matching branch these
    compute to the bound fields, because `s` is the constructor there. The
    branch body `Var(n-1-k)` therefore converts.
  - Universe levels: `Term::data` carries no levels, and the plan keeps
    fields at `Type 0`/`Prop`, so there is nothing to get wrong.
- **`T.%view` (1007-1070).**
  - Context is `params, s, t, h`. The `NumCase` is on `Var(1) = t`, and its
    default is `Var(2) = s`.
  - Arm `c` substitutes `t := c`, so `h : tag s = c` is what `C%k%at s h`
    needs.
  - `view s c e` computes to `C (at₀ s e) …` for a numeral `c`, whatever `s`
    is. Every proof relies on this.
- **`T.%eta` / `T.%etaAt` (source, 1087-1230).**
  - `eta (C a…) = rfl` holds because `tag` computes to `c`, the arm is taken,
    and each `at` cases on a constructor.
  - `etaAt` is one `J`.
  - For nested members, `at`, `view` and `tag` are generic over the
    container's own parameters, as `derive_field_in`/`derive_tag_in` already
    were. `eta`/`etaAt` are typed over `T`'s parameters through
    `T.%m{m}%type`, and the nested examples check.
- **Types with one constructor** (records included) keep the two-sided match,
  so there is no rebuild. Types with no constructors are refused.
- **Core lemmas** (OrdDerived.sw, DecEq.sw), statement by statement:
  - `Ordering.tagsEqual`: `(if Nat.equal i j then f else Nat.compare i j) =
    Equal → i = j ∧ f = Equal`. Correct and as strong as needed.
  - `Ordering.tagsFlip` / `tagsFlipBy`: the flipped comparison equals `flip`
    of the original, given `i = j → g = flip f`. Correct.
  - `Ordering.tagsTrans` / `tagsTransBy`: `Less` is transitive, given field
    transitivity only when all three tags are equal. All 8 `b, c, d` cases
    are handled.
  - `DecEq.tagsSame`: `(Nat.equal i j && f) = True → i = j`. The `False` arm
    is refuted by the elaborator. Correct.

  The laws assembled from these mean what they meant before:
  - `equal`, `flip` and `trans` are stated on `T.%compare` exactly as before.
  - `Ord.fromCompare` takes the same four.
  - `sameSound`/`sameComplete` are stated on `T.%same` as before.
  - Everything is kernel-checked, so a wrong term could only make derivation
    fail. It can't make a false law.
- **Removed lemmas.** I grepped `byTagTrans`, `andThenTransWhen`,
  `notBothEqual`, `bothEqual`, `%differ` and `%unfold` over the whole repo,
  minus `target/`, snapshots, reviews and worklogs. There are no uses in
  `aoc/`, `games/`, std, examples, `docs/guide` or `web/`. The only hits are
  `%unfoldStep` (unrelated, decreasing.rs) and the two stale mentions in
  findings 2 and 3.
- **Run-time.**
  - `&&` lowers to `if a then b else False` (logic.rs ~575), and the
    comparison is a plain `if`. So the second value's projections only run
    once the tags are equal. The default-projection pitfall (comparing a
    recursive field with itself) can't happen.
  - Probe `run1.sw`: a five-constructor type with a recursive field, a list
    field and a text field. I sorted 8 values and printed `==` and
    `compare`. The output is identical on `main` and the branch with `run`,
    and the same again from the native binary built with `stitchwort build`.
    `build --js` emits.
- **Checker behaviour with only the first value known.**
  - Probe `probe1.sw`, identical results on `main` and the branch:
    - `.read` on `(North == d) = True`, `= False`, `(Turn n == d) = True` and
      `(d == North) = True`;
    - an `if North == d` proved by matching `d`;
    - `rfl` on `Leaf == Node t 0 t`, `Node t n u == Leaf`,
      `Ord.compare Leaf (Node t n u) = Less` and
      `Ord.compare (Node t n u) Leaf = Greater`, with `t`, `u`, `n` unknown;
    - `Ord.equal North d h`;
    - an open goal `Node l v r == Node l v r`, displayed the same on both.
  - `== Card` with a constructor named `J` is not a capture risk: `J` is
    built in and can't be redefined.
- **More shapes** (probe `shapes.sw`, branch): all checked, and the tests
  ran:
  - a value parameter (`Bounded (n: Nat)`) with a proof field `ok: Nat.leq x
    n = True` and an equation field `same: x = y`;
  - two type parameters, with `Option (Two a b, Nat)` nesting (an Option
    member and a pair member);
  - `List (Option Wrap)`, nested two deep;
  - `.read`, `Ord.trans` and `Ord.equal` theorems on these types.
- **AoC days (branch binary).**
  - `check` on Aoc.Year2025.Day04 (`isRoll` refutes `Floor == Roll` by
    computation), 2020.Day18, Day11 and Day17, plus 2020.Day19, 2021.Day08,
    2024.Day21, 2024.Day24 and 2025.Day07: all checked.
  - Only 2024.Day21 and 2020.Day19 were run with `--no-cache`. Both pass, in
    2.3 s and 3.5 s.
- **Step guard.** `derived_instances_grow_linearly_with_constructors`
  passes in 3.5 s (release). See finding 6.

## Findings, ranked

### 1. Low: a missing builtin makes `derive_rebuild` panic, not skip

`crates/elab/src/derive.rs:915,918` (`derive_at_in`) and `:1009,1012`
(`derive_view_in`) return `Ok(())` without declaring anything when `Nat`,
`Void.absurd`, `Void.exfalso`, `Nat.equalFalse` or `T.%tag` is missing. But
`derive_view_in` (`:1052`) and the next field's `derive_at_in` (`:924`) then
call `.expect("… declared first")`, so a silent skip turns into a panic.

- **Can it happen today?** No. The prelude checks, so no type is derived in
  core before these exist.
- **Why fix it anyway.** It's a trap for anyone who moves core files around
  or derives earlier in core.
- **Fix:** check every prerequisite once at the top of `derive_rebuild` and
  return early before declaring anything; or make the inner functions return
  an internal error, not `Ok(())`.

### 2. Low: the proposal still says D3609 is open

`docs/proposals/derived-equality.md:3-4`: "Stage 2 built (SW-3370, §5.6).
Open decision: D3609". Matt answered D3609 on 15 Nov 2026 (board: "Yes, agree
with this recommendation for now, let's see how it goes").

**Fix:** "D3609: yes (Matt, 15 Nov 2026)."

### 3. Low: stale references to `T.%differ`

- **Board.** The SW-3002 ticket body (tickets.json ~32409) has an idea to
  refute constructor equations "with T.%differ instead of a helper". That
  helper no longer exists. The idea would now be `Nat.equalFalse` on the
  tags, or `DecEq.tagsSame`. The orchestrator should reword or drop it.
- **Docs.** `docs/research/inductives.md:726` describes `T.%decEq` as having
  "a default that refutes by tags (`T.%differ`)". It's a dated research note,
  so this is optional: add a one-line "(since SW-3370: tags first,
  derived-equality.md §5.6)".

### 4. Low: brittle proof in `Ordering.tagsTransBy`

`crates/elab/src/std/core/OrdDerived.sw:102-106`: the `False, False, True`
case rebuilds `Nat.compare`'s body by hand, `Eq.cong (b => if b then Equal
else (if Nat.leq i k then Less else Greater)) hd`, to get
`Nat.compare i k = Equal`.

- **Why it matters.** It's correct, but it breaks if `Nat.compare`'s
  definition is ever rewritten. It would break loudly, at std check time.
- **Fix (optional):** derive it from `Nat.equalSound i k hd` and a
  `Nat.compare k k = Equal` lemma, if std has one (`Nat.compareSelf` or
  similar). Otherwise leave it.

### 5. Low (performance, known): small types and wide types

These are measured in the lane's own log entry, not new:

- **Small types got slower.** Types with 2-3 constructors that each have
  several fields, one of them a nested list, check about 1.7× slower (24 →
  41 ms, 37 → 64 ms). Break-even is near six constructors.
- **Wide types keep a quadratic part.** `C%k%at` has n branches for each of
  the type's F fields, so wide types have an n·F term. By my fit to the
  lane's table it's about 0.7 k steps per branch: about 6.5 M of the 38.5 M
  steps for 94 three-field constructors. That's inherent to `Case` needing
  one branch per constructor, and fine.

What to do:

- **Watch the aggregate.** AoC and std are mostly small types, so the
  aggregate effect is the thing to watch. Have Overmind's rolling check, or
  the next benchmark run, compare whole-AoC and std check time before and
  after this merge. Neither was run in the lane.
- **If it regresses noticeably**, a cut-over can keep the two-sided match
  below about 6 constructors. It would be one `if ctors < N` in each
  builder, but two code paths. I wouldn't do it without a measured
  aggregate loss.
- This is an optimisation trade with results unchanged. Hashes do change, so
  strictly it's outside D3447, but D3609's stage 2 covers it.

### 6. Low: the step guard covers checker steps only

`crates/driver/tests/library/derive_cost.rs:62-80`.

- **Robustness.** It's sound:
  - the step counts are deterministic (`total_work`, prelude subtracted);
  - it checks both a ratio (94 vs 47 constructors ≤ 2.6×) and an absolute
    cap (5 M for the one-field type);
  - it runs in 3.5 s.
- **Margins.** The one-field ratio is about 1.96 (0.90 M → 1.76 M). The
  three-field ratio is about 2.2 by the fit above, so it has margin. A
  future change that adds a per-constructor cost linear in n would trip it,
  which is what it's for.
- **Two limits.**
  - It measures the kernel and evaluator budget only. Quadratic work in the
    elaborator's own Rust code, such as source generation or case-tree
    compilation, isn't counted. That's acceptable, but worth a sentence in
    the module doc.
  - A failure message prints counts, but a pass prints nothing. Optional: an
    `eprintln!` of the four counts would make drift visible in
    `--nocapture` runs.

### 7. Nit: code quality

- `derive_ord.rs:170-176`: the `ctors > 1` test sits inside the double loop.
  Hoisting it, or folding it into the `if ctors > 1` above, reads better.
- derive.rs module doc (`:114`) lists `T.%m1%view` among a member's helpers,
  but not the `%m1%…%at` projections or `eta`/`etaAt`. One more clause would
  fix it.
- The "turn the second value into the same constructor" pattern (let `%e`,
  the `at` lets, `J` over `etaAt`) is written out three times in
  derive_ord.rs and once in derive.rs. That's fine for now. If stage 3
  (mutual groups) adds more, a small shared builder (`known` + `eta_at` as
  free functions) would cut repetition.

## For the verifier: AoC and roguelike candidates

Every derived declaration's hash changed, so everything downstream rechecks.
The risk the lane flagged (proofs that rely on the old two-sided match shape)
didn't show up in my probes: readings and `rfl` behave the same.

The places most likely to notice are proofs that use `==` on constructors.
These are the days whose `Proofs/` mention `== Ctor` or `Ctor ==`, with the
ones I already checked on the branch in brackets:

- 2020: Day02, Day03, Day04, Day11 [ok], Day17 [ok], Day18 [ok], Day19 [ok,
  no cache]
- 2021: Day03, Day04, Day05, Day08 [ok], Day12
- 2024: Day04, Day10, Day12, Day14, Day21 [ok, no cache], Day24 [ok]
- 2025: Day02, Day04 [ok], Day07 [ok]
- games/rogue: `Rogue.sw`, `Turn.sw`, `Tests/Generate.sw`,
  `Tests/PlayThrough.sw`, `Tests/Turn.sw`

Several of my "ok" checks may have been cache hits (0.6 s). The whole-AoC and
roguelike `check --no-cache` in Overmind's rolling check covers the rest. No
`aoc/` or `games/` proof refers to any removed lemma or generated name.

## Tests run (this review)

- `task test:one -- -E 'binary(library) &
  test(derived_instances_grow_linearly_with_constructors)'`: passed, 3.5 s.
- Scratch probes, `check`/`test`/`run`/`build`/`build --js` with the branch's
  and `main`'s release binaries:
  - `probe1.sw`, readings and partly known values: same on both.
  - `run1.sw`, run-time output: same on both, and native output the same.
  - `shapes.sw`, parameters, proof fields and nested containers: passes.
  - `cards.sw`, `J`: it's a reserved name.
- AoC per-day checks, as listed above.
