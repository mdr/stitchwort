# SW-2541: AoC 2020 day 21 (Allergen Assessment), friction notes

Lane on Opus, 9 Nov 2026, about 15 minutes from start to the last proof
(estimate 120). Answers on Matt's input: 2380 and
`ktpbgdn,pnpfjb,ndfb,rdhljms,xzfj,bfgcms,fkcmf,hdqkqhh` (1.1 s with
`stitchwort run`); the example gives 5 and `mxmxvkd,sqjhc,fvjkl`, as the
puzzle says. Both answers were right on the first run. `stitchwort audit
Aoc.Year2020.Day21`: 45 theorems, 0 failed, 0 with warnings.

## What is proved

- **Parser** (`Proofs/Parse.sw`): if `parseFoods` reads the input, the
  input is the foods written out as `Spec.FoodListWritten` says, then
  line breaks. 30 lines, copied in shape from day 16.
- **Part 2, exact and unique** (`Proofs/Part2.sw`, `Proofs/Holders.sw`):
  when the elimination settles every allergen, the answer is the names of
  the holders, in the alphabetical order of the listed allergens, under a
  way the allergens could be (`Spec.Holding`: no two allergens in one
  ingredient, each listed allergen's ingredient in every food listing
  it), and every other answer the spec allows equals it. This uses
  `Aoc.Common.assignFinds` and `assignOnly` as they are.
- **Part 1** (`Proofs/Part1.sw`): the count is the spec's, where an
  ingredient "can't possibly contain any allergen" means no way the
  allergens could be has it hold one. The theorem takes the puzzle's
  promise that some way exists (`part1Correct`); `part1Settled` discharges
  it from part 2's answer, so with part 2's answer in hand, part 1 needs
  no hypothesis. Without the promise the statement is false (with no way at
  all, every ingredient vacuously can't contain an allergen, and the
  program would undercount), so the hypothesis is needed, not a
  convenience.

The interesting proof is part 1's other direction: an ingredient in every
food listing allergen `a`, held by nothing in some valid way, is put in
`a`'s place (`moveTo`), and that is still a valid way. So the usual
"intersection of the foods' ingredients" shortcut is exactly the spec's
"can't possibly", whenever any valid way exists; it doesn't need the
elimination to settle.

Not proved: that the elimination settles on every input where only one
way exists (it can get stuck where it shouldn't need to; on the puzzle's
input it doesn't). Breaking the program three ways (dropping the `not` in
`couldHold`, `any` to `all` in `isSafe`, dropping the alphabetical sort)
made the proofs fail each time.

## A newcomer's view, step by step

1. **Program** (5 min, with reading day 16). Records `Ingredient`, `Allergen` (one `name`
   field each), `Food`, `FoodList`, methods on `FoodList`. Reading the
   format with `Parse.many1`, `Parse.sepBy1` and `Parse.lines` was
   direct. `allergens.unique.sortOn .name` reads as the puzzle says it.
   Part 2 is `assign (allergens.map candidates)` from `Aoc.Common`, as day
   16 uses it: reuse cost nothing.
   - *Slow:* guessed `Char.isLower`; it is `Char.isAsciiLowercase`.
     `E-UNKNOWN-NAME` says "`Char` has no `isLower`" with no suggestion.
     *Would have helped:* a "did you mean" over `Char.is*`, by meaning
     (lower/upper/digit) rather than spelling alone.
2. **Spec** (2 min). The puzzle's "can't possibly contain" is about every
   consistent assignment, so the spec quantifies over functions
   `Allergen → Ingredient`. Writing "the number of times these
   ingredients appear" needed a `Bool` classifier paired with an `↔` to a
   `Prop` (`∃ safe, (safe i = True ↔ ¬CanContain i) ∧ answer = …count
   safe`), because you can't count by a `Prop`.
   - *Would have helped:* a std way to count list elements by a decidable
     `Prop`, so the spec could say `food.ingredients.countWhere (i =>
     ¬CanContain list i)` given a decision procedure; here there is no
     decision procedure for `CanContain` anyway (it quantifies over
     functions), so the classifier form may be the honest one. Day 19's
     spec has `NumberWith (p: a → Prop) items answer` (count by a
     relation, no decision needed), which day 20 imports; I found it only
     afterwards, in NOTES-2020's day 20 ranking, which already lists it as
     a library candidate. A `List.CountWith` in std would have been found
     by `stitchwort search`.
3. **Parser proof** (2 min): mechanical. The goals printed as the spec
   wrote them, so `rfl` and `List.appendNil` closed each.
4. **Part 2 proof** (5 min). The spec's holder is a function; `assign`
   gives a list in the order of the allergens. Turning one into the other
   took a lookup (`holderOf`) and four lemmas (70 lines): its map over the
   keys is the list, it relates each key to its value as the lists are
   related, its values are in the list, and it is injective on the keys
   when the values are distinct. The rest was a chain of std lemmas.
   - *Awkward:* error messages and `W-MATCH-NOT-FOUND` show
     `list.allergens` unfolded into `List.mergeRuns … (List.buildRuns …
     (List.uniqueLoop …))`, three lines of internals for a name the
     source writes in 14 characters. Goals at `?` kept `list.allergens`;
     the type-mismatch "expected" text didn't.
   - *Slow:* `stitchwort search '[auto eq: DecEq ?a] → (x: ?a) → (x == x)
     = True'` found nothing (relaxed pass, 0 results); `(?x == ?x) =
     True` finds `DecEq.refl` at once. An `[auto]` binder in a pattern
     seems to stop the match. And `'(x: _) → x ≠ ?y → (x == ?y) = False'`
     finds nothing because std has no such lemma (used `match` on `x ==
     y` and `DecEq.soundFalse` instead).
5. **Part 1 proof** (2 min). The swap argument went through as written.
   `match taken: list.allergens.any (…) with` turned "some listed
   allergen is already held by the ingredient, or none is" into a
   decidable split, so the proof stays constructive.

## Std candidates

Each was proved in the day's `Proofs` namespace; all are generic.

- `distinctPerm [auto eq: DecEq a] (xs ys) (same: List.Perm xs ys) (distinct: ys.Distinct): xs.Distinct`
  (`Proofs/Allergens.sw`). Std has only `distinctMapPerm`, so this went
  through `List.mapId` twice.
- `distinctMapOn (f) (xs) (distinct) (injective on members): (xs.map f).Distinct`
  (`Proofs/Part2.sw`). Std's `List.distinctMap` wants `f` injective
  everywhere.
- `all2OfMapRight (g) (related) (xs) (ys): All2 related xs (ys.map g) → All2 (x y => related x (g y)) xs ys`
  (`Proofs/Part2.sw`); std has the `Left` one only.
- `all2MapBoth (related) (f) (g) (xs): ((x) → x ∈ xs → related (f x) (g x)) → All2 related (xs.map f) (xs.map g)`
  (`Proofs/Part2.sw`).
- `(x == y) = False` from `x ≠ y` for `DecEq`: missing; a `DecEq.falseOfNe`
  beside `DecEq.trueOfNe` (which is about `!=`).
- Two lists, distinct and sorted by an antisymmetric, transitive order,
  with the same members, are equal: `sortedPermEq` composed with
  `permOfSameMembers` (`sameAlphabetical` in `Proofs/Part2.sw`); worth
  one std lemma.

## Aoc.Common candidates

- **`assign`'s result as a function.** `holderOf` and its four lemmas
  (`Proofs/Holders.sw`) are not about allergens: they read a list of
  values aligned with distinct keys as a function on the keys. Any day
  that states its spec with a function (which reads better than "a list
  in the order of the positions") will need the same. They belong beside
  `Elimination.sw`, or in std as lemmas about `List.lookup (List.zip keys
  values)`, which is the same function with `Option`.
- Day 16's `Unique.sw` and this day's `dangerousOnly` both show "every
  valid choice is among the candidates" then call `assignOnly`; the shape
  is the same but the candidates are built differently (a fold over
  tickets there, a filter here), so nothing to share yet.
