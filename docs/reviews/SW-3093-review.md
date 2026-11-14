# SW-3093 review (reader: applied facts, decisions of equations)

Opus review of `lane/SW-3093` (3 commits, `fd02daa3d`, `c1f8bddd3`,
`b0dc951c3`), 13 Nov 2026. Required by D2364: the change decides which proof
terms are built from test facts.

**Verdict: merge after small fixes.** There are no blockers. The terms are
sound, and they type-check by ordinary unfolding, not by luck. The new step
can't pick an equation other than the one the decision decides. Two
should-fixes: the docs weren't updated for a user-visible change, and the
examples don't pin the cases most likely to regress.

## What I checked and ran

- Read the whole diff and the reader around it (`lookup_folded`,
  `stuck_decision`, `by_decision`, `step_proof`, `read_through`, `read_type`,
  `hypothesis_reads`).
- Rebuilt the worktree's CLI (`cargo build -p stitchwort-cli`, incremental,
  5 s), because the existing binary was older than `reading.rs`. Then I
  checked small probe files with the lane's binary and with main's release
  binary (`~/repos/mdr/stitchwort/target/release/stitchwort`, 11:31) to
  compare old and new behaviour. The probes are quoted below.
- Ran `hash_stability::examples` with
  `EXAMPLES=readings-applied-facts,readings-decision-equations,readings-witness-bound`
  on the existing library test binary: passed, 7 s.
- Ran `stitchwort check` on single days: `Aoc.Year2020.Day05`, `Day17`,
  `Day18` and `Day20`. These days have `==` facts on `Char`, `Operator` and
  lists. All passed.
- Ran `cargo fmt -p stitchwort-elab --check`: clean.
- Not run: the prelude hash test, the whole examples suite, whole-AoC or
  rogue checks. Those are left to the verifier and Overmind.

## Soundness

Every term the new step builds is `Decidable.sound p d h`,
`Decidable.complete p d h`, `Decidable.refute p d h` or
`Decidable.toBoolOfNot p d h` (`step_proof`, `reading.rs:1076`). In each,
`p` is read off `d`'s own type `Decidable p` (`decision_test`,
`reading.rs:850`), and the kernel checks the result.

- `h : test = True`, and `test` unfolds, by δ and β, to `Decidable.holds p d`
  in at most `UNFOLD_LIMIT` steps. Those are the same steps the loop took to
  reach `d`. This is the same conversion `stuck_decision` has always relied
  on at step k > 0. No proof field or extra reduction is involved.
- **No other equation can be chosen.** `==` is `DecEq.decide x y`, whose
  type is fixed as `Decidable (x = y)` with the sides as written. A `y == x`
  reads as `y = x` (probe `swapped`). An instance can't decide a "coarser"
  equation: any `d : Decidable p` proves exactly `p`. A hand-written instance
  built with `Decidable.map` from `Nat.decEq a.n b.n` now reads as `a = b`.
  Before, it read as `a.n = b.n`, the layer inside. Both are true, and the
  new one is what the user's `==` says.
- `test_fact_in` now calls `force_solved` on the test (`reading.rs:275`).
  That only replaces solved unknowns at the head, so the test stays the same
  value up to conversion. It's harmless.
- `decision_test` now also accepts `Value::Neutral(Head::Def f, spine ++
  [Proj])` (`reading.rs:865`). This widens `stuck_decision` as well: a
  definition stuck on its arguments whose `.holds` is projected now reads by
  its decision, where before it was a leaf. It's sound for the same reason
  as above. This side effect isn't mentioned in the report; see note N3.

## Findings

### Should-fix

**S1. The docs aren't updated for a user-visible change.** Which
proposition a fact reads as is visible to users: it changes `.read`, the
patterns that are accepted, and the messages. The lane changed no docs.

- `docs/guide/10-proofs.md:572`: "Where the decision is only known by its
  type, as `==` is on a type known only to have `DecEq`, a fact about its
  test reads as what it decides". This is now true of every `==`: lists,
  `Text`, tuples, `Option`, `Char`, and hand-written instances. The
  paragraph should say so. One example with a concrete type would help, for
  instance `(c == 'a') = True` reads as `c = 'a'`.
- `docs/proposals/bool-as-proposition.md` §5.4: the steps list has no step
  for "a decision of an equation that computes, read through its decision
  unless its test one step in has a reading that states the same equation".
  §5.6 says "a test that computes to `True` or `False` is not read", which
  is now only partly true (see S3).

CLAUDE.md requires the guide to be updated for user-visible language
changes. This fix belongs in this lane, or in a docs-only follow-up merged
in the same batch.

**S2. Behaviour changes that no example pins, and that can break code
outside std.** The prelude moved only through `Text.spaceTabPlain` and its
dependents. Its statements are written in source and unchanged, and the
`Parse.*` hashes moved only because they use `spaceTabPlain` (checked:
`linesBlank` calls it at `Reads.sw:1577`, and `sectionsLinesEach` calls
`linesBlank` at `:1619`). Outside std, these readings changed, compared
against main's binary:

| fact | main | lane |
|---|---|---|
| `([x, ..xs] == [y, ..ys]) = True`, `match h with \| Both hx _` | accepted (`∧` of heads and tails) | `E-NO-READING`: reads as `[x, ..xs] = [y, ..ys]` |
| `(c == 'a') = True`, `.read` | `c.toNat = 97` | `c = 'a'` |
| `(Some xs == Some ys) = True` (lists), `.read` | `xs = ys` | `Some xs = Some ys` |
| hand-written `Code.decide` by `Decidable.map (Nat.decEq a.n b.n)`, `.read` | `a.n = b.n` | `a = b` |
| `(decSmall n).holds = True`, `Small n := isSmall n = True`, `.read` | `n ≤ 4 ∧ …` | `Small n` |

These are the intended direction (SW-3065, SW-3083). But any AoC or rogue
proof that takes apart a literal-cons or tuple `==` with `Both`, or uses
`(c == k).read` as a `toNat` equation for `omega`, now fails. A grep found
no such code in `aoc/src` or `games/rogue/src`, and the four 2020 days I
checked pass. The whole-AoC check is still Overmind's to run. Add to the
lane's examples:

- an accept example for a hand-written `DecEq` instance, both by `match`
  (like `Bool.decEq`) and by `Decidable.map` (the case whose reading
  changed);
- `Some xs == Some ys` with `xs ys: List Nat`, and `Option (List T)` (the
  brief asked for nested Option of list; only `Option Nat` and
  `Option Pos` are covered);
- `(c == 'a') = True` reads as `c = 'a'`;
- a reject example: `Both` on `([x, ..xs] == [y, ..ys]) = True` is
  `E-NO-READING` with "reads as `[x, ..xs] = [y, ..ys]`", so the change is
  deliberate and recorded.

Probe (lane binary; all pass except as the table says):

```stitchwort
theorem optList (xs ys: List Nat) (h: (Some xs == Some ys) = True): Some xs = Some ys := h.read
theorem chars (c: Char) (h: (c == 'a') = True): c = 'a' := h.read
theorem swapped (xs ys: List Nat) (h: (ys == xs) = True): ys = xs := h.read
type Code = { n: Nat }
def Code.decide (a b: Code): Decidable (a = b) :=
  Decidable.map (Nat.decEq a.n b.n) (e => match a, b with | { n }, { n = m } => rewrite e in rfl) (e => rewrite e in rfl)
instance Code.instDecEq: DecEq Code := { decide = Code.decide }
theorem codes (a b: Code) (h: (a == b) = True): a = b := h.read
theorem bothCons (x y: Nat) (xs ys: List Nat) (h: ([x, ..xs] == [y, ..ys]) = True): Void :=
  match h with | Both a b => ?    -- E-NO-READING on the lane, accepted on main
```

### Notes

**N1. The "computes to a constructor" boundary depends on how the decision
is written** (`reading.rs:918`). `force_solved` doesn't unfold calls, so
the check only catches a test that is a literal constructor one folded step
in. Results on the lane:

- `([x, ..xs] == []) = False` reads as `False ≠ True`: a leaf, refuted.
- `([(1: Nat)] == [2]) = True` reads as `[1] = [2]`.
- `(Some (1: Nat) == Some 2) = True` reads as `Some 1 = Some 2`.

On main the second and third were `∧` of `holds` and a leaf, so neither old
nor new matches §5.6's "a test that computes to `True`/`False` is not read".
This isn't a soundness issue, and `match h with | ()` and `cases` still
work on all of them (probe4). Suggestion: drop the constructor exclusion
for decisions of an equation, so `[x, ..xs] ≠ []` reads as the user wrote
it. Or keep the exclusion, but test whether the decision's test computes to
a constructor (force with calls unfolded), so the boundary doesn't depend on
how the instance is written. Either way, say which in §5.6. A follow-up
ticket is enough.

**N2. The scope is wider than "an equation".** The test
`force(prop) is Value::Eq` (`reading.rs:911`) sees through definitions. So
a decision of a proposition defined as a `Bool` equation (`Small n :=
isSmall n = True`, `Int.LessEq`) also reads as its proposition (`Small n`)
instead of the test's body. I think that's the better reading, and the
"same equation" check keeps `Int.leq` and similar on their own readings
where they have one. The doc comment on `equation_decision` and §5.4 should
say this, though.

**N3. `stuck_decision` widened silently** (`reading.rs:865`, the `Neutral`
arm). It's sound, and probably what the `Bool.decEq` case needs: `(a == b)`
on `Bool` variables now reads as `a = b`. Worth one line in the commit
message or the report, and in §5.4 step 2.

**N4. `FRESH = 1 << 24` as the conversion level** (`reading.rs:893`,
`:929`). It works, because the level is only used for fresh variables under
binders. But it's a magic constant where callers elsewhere pass
`cx.level()`. `lookup` has only `g` and `e`, so threading the level through
is a small change. Optional.

**N5. Cost.** `equation_decision` runs at every unfolding step of every
lookup. For anything that isn't a `holds` it costs one pattern match. For a
decision of an equation that doesn't fire (`Nat`, derived types), each step
pays:

- `decision_test` twice (once in `stuck_decision`), each walking the
  function's type for the projection form;
- an `unfold_once` that the loop then repeats;
- `reading_for` (a linear scan of the readings table);
- `statement`;
- a `conv`.

The reader runs only where checking failed before, plus `auto` and `cases`
over the hypotheses (§5.7), so I expect this to be negligible. I didn't
measure it. To halve it, pass the `unfolded` value back to the loop and
compute `decision_test` once per step.

**N6. A proof's hash can depend on checking order.** If the unfolded test's
reading isn't registered yet when a use is checked (D3537's carve-out for a
reading's own dependencies), the step fires and reads the same equation
through the decision rather than through the reading. The proposition is
the same and only the proof term differs, so this affects hashes only, not
whether code checks. Derived `%sameReads` are generated with the type, so
this can't happen for derived equality.

**N7. The message shows the unfolded decision, not the test as written.**
For example: "`((x.decEq y).and (Std.List.decEq (x y => x.decEq y) xs
ys)).holds` reads as `[x, ..xs] = [y, ..ys]`". This happens because the
reading fired at an unfolded step. The variable case does the same on main,
so it isn't new, but the new step makes it more common. The message should
print the test as written (`[x, ..xs] == [y, ..ys]`). Small follow-up.

**N8. Style** (`aoc/.../Day20/Proofs/Corners.sw:14-15`): `Inl (same.read)`
reads more naturally as `Inl same.read`.

## Test adequacy

The new examples cover applied facts, `let`-bound and nested `.right`,
lists (variables, conses, a call on the left), `Text`, tuples, `Option Nat`,
`Option` of a record, `Witness`-bound facts in a lambda, and the `Nat`
control. Missing cases are in S2: a hand-written instance, `Option` of a
list, `Char`, and a reject example for the `Both` change. The boundary
cases in N1 are also unpinned.
