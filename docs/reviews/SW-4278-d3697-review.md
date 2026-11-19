# SW-4278: review of D3697, the cases of a guarded arm that a later arm partly overlaps

Fable paper lane, 19 Nov 2026. Claims are marked **measured** (a probe run
for this review; the files are listed at the end), **read** (in the repo)
or **recalled**.

## Recommendation

**Option 2, one case per arm**, which is not what the proposal recommends
(`functional-induction.md` §3.1 and §6 recommend option 1).

`withoutR.induct` gets three cases, `eq1`, `eq2`, `eq3`. `eq3`'s hypothesis
is the one `withoutR.eq3` already takes:

```
notArm2: ∀ (closer: Kind) (after1: List Kind) =>
  after = [closer, ..after1] → ¬(isComma leaf ∧ isCloser closer ∧ hasItem behind)
```

No new case names, no new naming rule. A proof that needs the next leaf in
hand writes `match after with` inside `eq3` and applies `notArm2` once.

If Matt prefers option 1 anyway, section 5 gives the four changes I would
make to its names and shape.

## 1. The reasons

**1. The formatter's proofs already split by arm, not by place.** The
`withoutR` family's hand proofs don't split on `after` and then on the
guard. They split on a `Bool` summary, `fwdPair behind leaf after`, whose
definition is the option 2 hypothesis as a function (read:
`SettleBareProofs.sw:448`):

```
def fwdPair (behind: List Leaf) (leaf: Leaf) (after: List Leaf): Bool := match after with
  | [closer, .._] => lastPair closer.token.kind leaf behind
  | [] => False
```

Measured in `tools/fmt/src`: 15 proofs open with `match pair: fwdPair …
with`, and 13 lemmas take `fwdPair … = False` as a hypothesis. In the eight
`False` branches I read, none splits `after` again. Each either ignores the
fact apart from rewriting with the step lemma (`withoutRNop`, which `match
induct` makes unnecessary), or hands it whole to a lemma about the step
(`stepNormal … pair`, `gapAfterNop leaf acc after pair`). The people (and
agents) who wrote these had the choice of splitting by place and built a
summary to avoid it. Arm 3 is "the pair rule doesn't fire here", one
thought, and its lemmas are stated that way.

**2. Proof length, by kind of proof.**

| Kind of proof for arm 3 | Option 1 (two cases) | Option 2 (one case) |
|---|---|---|
| (a) The fact isn't used (`allTokensWithout`, `laidWithout`, the `…Tokens` and `…Flat` lemmas) | one alternative joining two cases with different binder counts | one alternative |
| (b) The fact goes whole to a step lemma (`stepNormal`, `gapAfterNop`) | two alternatives, the fact derived twice, from two shapes | one alternative and one bridging lemma per family |
| (c) The proof needs the next leaf where the guard failed | direct | `match after with`, then `notArm2 closer after1 byComputing`: about two more lines |

I found (a) and (b) in the formatter and no (c) among the sites read. The
proposal's own §4.2 concedes (b): "the honest cost of G1's two cases:
helper lemmas stated against the old `fwdPair` summary need restating".
That isn't a migration cost. A lemma about "the step where no pair fires"
wants one hypothesis in the end state too, and option 1 has no case that
states it.

The bridge for (b) is short and checks today (measured: `p3.sw`):

```
theorem noPair ∀ (behind: List Kind) (leaf: Kind) (after: List Kind)
    (notArm2: ∀ (closer: Kind) (after1: List Kind) =>
      after = [closer, ..after1] → ¬(isComma leaf ∧ isCloser closer ∧ hasItem behind)):
    pair behind leaf after = False :=
  match after with
    | [] => byComputing
    | [closer, ..after1] =>
      match guard: isComma leaf && isCloser closer && hasItem behind with
        | False => byComputing
        | True =>
          (notArm2 closer after1 byComputing
            (Bool.andLeft guard, Bool.andLeft (Bool.andRight guard), Bool.andRight (Bool.andRight guard))).impossible
```

It also shows the cost of (c): using the quantified hypothesis by hand is
one `match` and one application.

**3. Names and counts.** With option 2, cases stay one to one with the
equations (the rule in `induct.rs`'s header: "one for each arm with no split
below it and one for each branch, named after the equation"). The
`E-NONEXHAUSTIVE` note stays "the cases are `eq1`, `eq2`, `eq3`". Two or
three guarded arms above one later arm add hypotheses, not cases. Measured
on a four-arm probe (`p1.sw`), `three.eq4` takes

```
∀ (b c: Kind) (after1: List Kind) => after = [b, c, ..after1] → ¬(isComma leaf ∧ isCloser c)
∀ (b: Kind) (after1: List Kind) => after = [b, ..after1] → ¬isComma leaf
```

Option 1 gives that arm three cases when the patterns nest, four when they
don't, and up to 2^n for n guarded arms, hence the proposal's cap of 32 and
its skip. Each or-pattern alternative of the later arm multiplies again
(`eq3Or1NotArm2`, `eq3Or2NotArm2`). Option 2 needs no cap and never skips
for size.

**4. What the user sees in a `?`.** The hypothesis above, in the same
words `withoutR.eq3` shows today (measured: `p2.sw`). It is longer than a
plain `¬(…)`, but it is one shape the user has already met in the
equations, and a fully overlapped guarded arm keeps today's plain
`notArm2: isComma k = False` (measured: `countC` in `p2.sw`).

**5. Lean does this.** Measured (`l1.lean`, `l2.lean`): for an overlapped
arm Lean's `f.induct` gives one case with `(∀ b after_1, after = b ::
after_1 → False)`, and with a condition on the earlier arm, written as a
second discriminant since Lean has no pattern guards, `(∀ b after_1, p
behind = true → after = b :: after_1 → False)`. The usual objection is that
Lean's automation uses such hypotheses and Stitchwort's users instantiate by
hand. Reason 1 answers it: these proofs mostly pass the fact on or ignore
it.

**6. The walk step doesn't need the split in `f.induct`.** The walk
(SW-4238 review §3.5, §3.12) follows the compiled case tree and shows a goal
per path, without case names. It shares the leaf enumeration with
`induct.rs`, and that is the same under either option: option 2's proof
term still visits every leaf and applies the arm's case there, proving the
quantified hypothesis at each. Only the grouping of leaves into named cases
differs, and the walk has no named cases. A walk path that goes past a
failed guard would show the plain negation, which is right for a path.

**7. G2 and or-patterns.** G2's `ih` under a lifted `match` is independent
of this choice. With option 2, or-patterns of cases (SW-4263) are not
needed for this shape at all; they stay useful for `eq2IfTrue | eq2IfFalse`
and `eq3Or1 | eq3Or2`.

## 2. Sketches: `allTokensWithout` (read: `SettleOnceProofs.sw:424`, 29 lines today)

Option 2:

```
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 _ comma closer _ _ ih => …   -- as the proposal's §4.1
    | eq3 _ _ _ _ ih => ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)
```

Option 1 (the proposal's §4.1):

```
    | eq3 _ _ _ _ ih | eq3NotArm2 _ _ _ _ _ ih =>
      ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)
```

The same length. Option 1 relies on the body checking in both cases, where
`coming` is about `[leaf, ..after]` in one and `[comma, closer, ..after]`
in the other; that should hold by computation but is not checked.

`laidWithout` (read: `SettleOnceProofs.sw:228`) is kind (a) as well:
`laidNop leaf behind after back fwd` takes no `fwdPair` fact, so the `?nop`
in the proposal's §4.2 sketch isn't needed there. With option 2 its third
alternative is `| eq3 _ leaf after _ ih => let (b, f) := laidNop leaf behind
after back fwd; ih b f`. The (b) proofs are in `SettleBareProofs.sw` (lines
663, 681, 731, 842): with option 2 each passes `noPair notArm2` where it
passes `pair` now; with option 1 each becomes two alternatives.

## 3. What option 2 costs

- **Kind (c) proofs pay two lines.** If a later family reasons mostly about
  the place where the guard failed, option 2 is the worse fit for it. The
  finer split can be added then as an alternative way to write the case; it
  need not be decided now.
- **The elaborator has to prove the quantified hypothesis at the leaf where
  arm 2's patterns matched and its guard failed** (from `[c, ..a] = [closer,
  ..after1]` by injectivity, then the leaf's `¬guard`). This is the step
  today's refusal names ("which stage 2a's proof doesn't establish").
  `withoutR.eq3` already exists in this form (measured), so the fact is
  provable by the elaborator; Lean generates the same (measured). It is more
  kernel-term generation than option 1's, so the lane is Opus's and its
  review covers that proof.
- **It disagrees with the if-style rewrite**, where the same function
  written with an inner `if` has four cases (read: `withoutR-if.sw`). That
  is consistent in its own way: the cases follow how the definition is
  written.

## 4. Other shapes considered

- **Fully per place, as Isabelle's `fun` (recalled)**: `eq3` at `[leaf]`
  with no hypothesis at all. The best reading where the unmatched part is
  one place, but the number of places grows with the constructors of the
  types in the earlier pattern (a pattern naming one token kind out of
  dozens leaves one place per other kind), and literals have no finite
  list. Rejected.
- **Both grains at once** (`eq3`, or a finer pair in its place). The coarse
  alternative implies the fine cases, so `match induct` could accept
  either. Two layers of names for one arm; not worth it without kind (c)
  proofs to justify it.

## 5. If Matt chooses option 1: four changes

1. **Name: `eq3NotGuard2`, not `eq3NotArm2`.** Both of arm 3's cases are
   "not arm 2", and the plain `eq3` case carries a hypothesis that is
   itself called `notArm2`. What distinguishes the second case is that arm
   2's pattern matched and its guard failed. `eq3Guard2` is shorter but
   reads as if the guard held; `eq3Else2` says less.
2. **List every guarded arm that matched at the place**, in order
   (`eq4NotGuard2NotGuard3`), not only the first. The proposal's "named by
   the first guarded arm whose patterns match there" gives two different
   places the same name when two guarded arms' patterns overlap without one
   containing the other (`[a, b, ..r] if …` and `[Comma, ..r] if …` above
   `[x, ..r]`: "only arm 2 matched" and "both matched" are both
   `eq4NotArm2`).
3. **In the plain `eq3` case, state the hypothesis without the guard**:
   `∀ closer after1 => after = [closer, ..after1] → Void`, the form an
   unguarded overlap has today (read: `induct.rs` header). It is what is
   true there and what the `%apart` refutation proves; carrying the guard
   in it makes the two cases look alike in a `?`.
4. **Keep the hypothesis name `notArm2` in both cases** (the proposal
   calls the new one `notGuard`), as a fully overlapped guarded arm has
   today, and generate the matching equation `f.eq3.notGuard2`, so that
   cases and equations stay one to one. Suffix order: place, then
   or-alternative, then body splits (`eq3NotGuard2IfTrue`).

## 6. Risks and limits of this review

- The count of how arm-3 facts are used is from one family (`fwdPair`, 15
  sites, eight `False` branches read). The nine definitions the proposal
  lists share that guard, so it is the relevant family, but it is one.
- The existing proofs were written without `match induct`; with it some
  might be written differently. None of the eight needed the next leaf.
- Lean's behaviour for a guarded arm is by analogy: Lean has no pattern
  guards (recalled), so `l2.lean` puts the condition in a second
  discriminant.
- Nothing here was built: the option 2 principle for `withoutR` is not
  checked, only its hypothesis's use (`p3.sw`) and the equation that
  already has that form.

## Probes

In `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/d3697/`:
`p1.sw` (equation of an arm under two guarded arms), `p2.sw` (cases and
holes for a fully overlapped guarded arm; `withoutR.eq3`'s hypothesis),
`p3.sw` (the bridge, checks), `l1.lean` and `l2.lean` (Lean's `f.induct`
for an overlapped arm, plain and conditioned). Counts: `grep` over
`tools/fmt/src` for `match …: fwdPair` and `fwdPair … = False`.
