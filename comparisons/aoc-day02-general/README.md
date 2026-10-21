# AoC 2025 day 2 part 2 for every input: a Lean 4 prototype (SW-159)

Stitchwort's proof of day 2 part 2 (`aoc/src/day02/part2proof.sw`, `part2Correct`) holds
only for ids of at most 10 digits. Its weights are a fixed table, and the facts about which
repeat counts come together ("6 copies are also 2 copies") are checked by computation. This
directory proves part 2 for **every** input, in Lean 4 with the core library only (no Mathlib,
no Batteries). It is a prototype for the Stitchwort port, so the porting note below lists what
Lean's core gave for free.

**The port landed (SW-166, 20 October 2026):** `aoc/src/day02/part2proof.sw` now proves
`part2Correct` with no hypothesis, following this prototype (664 lines, about 390 of them new,
plus about 185 lines of library; it checks in about 0.85 s). See docs/aoc-2025.md, "Part 2 for every
input".

## How to check

```
cd comparisons/aoc-day02-general/lean
nix shell nixpkgs#lean4 -c lean Day02General.lean
```

Lean 4.34.1. It takes about 12 s: the proofs take about 3 s and the rest is the brute-force
cross-check. Expected output, and no errors or warnings:

```
(4174379265, 4174379265)                      -- the puzzle example: program, spec
[(11111111111, 11111111111), ...]             -- nine ranges of 11 to 20 digits
true                                          -- the same nine, summed
true                                          -- 4,004 more ranges (every id to 200,000, and more)
'part2Correct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The last line shows that nothing is assumed beyond Lean's standard axioms (no `sorry`).

## The theorem

```lean
theorem part2Correct (ranges : List Range) : solvePart2 ranges = part2Spec ranges
```

There is no hypothesis. `part2Spec` is the puzzle as written, as in Stitchwort: walk the ids of
every range and add those whose decimal digits are some block written two or more times
(`repeats`, with `writtenAs ds k n := (replicate n (ds.take k)).flatten == ds`).

## The program change

Compared with `aoc/src/day02/day02.sw`:

- **The weights are computed.** Each repeat count n gets two counts, `plus n` and `minus n`:

  ```
  plus K  = 1 + (minus d, added up over the divisors d of K with 2 ≤ d < K)
  minus K =     (plus d,  added up over the same divisors)
  ```

  The weight is `plus n - minus n`. It is minus the Möbius function and agrees with the old
  table: +1 for 2, 3, 5, 7, 11, 13, ...; −1 for 6, 10, 14, 15; 0 for 4, 8, 9, 12. The
  recursion takes a fuel argument so it is structural (`wf fuel sign n`). Stitchwort has
  `Nat.divFuel`, which works the same way.
- **Repeat counts go up to the digit count of `hi`**, not to 10. The block length k still
  runs from 1 to that count, and only pairs with `k * n` at most the count are used.
- **It's all natural numbers.** One range gives `weighted plus r - weighted minus r`, and the
  answer adds these up. There is no `Int`. Each range's plus total is its puzzle sum plus its
  minus total, so the subtraction never cuts off at 0.
- It stays fast. Each (k, n) pair still adds an arithmetic series (`repeated`, which is
  unchanged), and with ids of 10 digits there are at most 100 pairs.
  `parseRanges`/`fits`/`ifAllFit` and the "more than 10 digits" message can go.

## The proof, in plain words

Take one id x with L digits.

1. **Periods (section 5).** Write the digits around a circle. A *period* is a rotation by p
   places that leaves them unchanged. If p and q are periods, so are p + q and p − q, because
   doing one rotation and then the other is a rotation too. Let p₀ be the smallest positive
   period; L is always a period, so p₀ exists. For any period p, the remainder of p divided by
   p₀ is p minus some copies of p₀. So it is a period, and it is smaller than p₀. So it is 0.
   **Every period is a multiple of p₀**, and in particular p₀ divides L.
2. **Blocks are periods (section 6).** When k·n = L, the digits are their first k digits
   written n times exactly when k is a period.
3. **So (section 7):** the digits are some block written n times (n ≥ 2) exactly when n
   divides K = L / p₀, the number of times the *smallest* block is written. And x repeats
   exactly when K ≥ 2.
4. **The weights (section 4).** Over the divisors of K from 2 on, plus adds up to one more
   than minus when K ≥ 2, and to the same when K = 1. This follows directly from the
   definition: the divisors below K give the same totals, crossed over, and K itself adds 1
   to the plus side.
5. **Assembling (sections 7–9).** For one id and one n, only block length k = L/n can count
   (`count_k`). So x's plus terms are x times the plus weights of the divisors of K, and the
   same for minus. By 4, the plus terms are the minus terms plus x when x repeats. Section 8
   shows that `repeated r k n` adds the ids of the range whose digits are a k-digit block
   written n times. **Stitchwort already proves this** (`repeatedIds`, for any n ≥ 2, with no
   digit limit). Swapping the sums over ids and over (k, n) finishes the proof.

### Changes to the suggested strategy

- **No gcd or Bézout.** Showing that "the smallest period divides every period" needs one
  division with a remainder (`cyc_dvd`). Closure under gcd is never needed.
- **Natural numbers, not `Int` weights.** I first proved it with `Int` weights
  `w K = 1 − Σ w d` (commit 1010318; it checks too). Then I switched to the plus/minus split,
  because Stitchwort's `Int` library has no lemmas about `Int.mul` (core.sw has only
  `Int.toIntMul`, which holds by `rfl`) and one lemma about `List.sumInt` (`sumIntFrom`).
  Its `Nat` sums already have congruence, swap, add, multiply and the "only one term counts"
  lemmas. The existing part 2 proof already splits the total into plus and minus parts for
  the same reason.
- **Rotations as index arithmetic, not list rotation.** `Cyc g L p := ∀ i < L, g ((i+p) % L) = g i`
  with `g i` the i-th digit (`getD`). There are no `List.rotate` lemmas. Addition and
  subtraction of periods are three-line proofs from `(a % L + b) % L = (a + b) % L`.

## Sizes

`Day02General.lean` is 1,001 lines. Below are lines of code without comments or blank lines,
and the number of theorems.

| Section | What | Code lines | Theorems | In Stitchwort today |
|---|---|---:|---:|---|
| 1, 2 | spec, program | 38 | – | spec as is; program ~25 lines changed |
| 3 | sums | 57 | 8 | **have** almost all (see below) |
| 4 | weights: plus is one more than minus | 52 | 4 | new |
| 5 | periods, smallest period | 47 | 7 | new |
| 6 | a block written n times ⇔ period | 82 | 9 | new (length part exists: `repCount`) |
| 7 | one id: plus = minus + [repeats]·x | 108 | 6 | new; adapts `collapse`, `perId` |
| 8 | digit bridge: `repeated` = sum of ids | 305 | 31 | **have** (`repeatedIds` and day02.sw) |
| 9 | assembly | 36 | 5 | adapts `weightedIds`, `rangeSplit` |
| 10 | example and cross-checks | 23 | – | tests |

New mathematics to port: sections 4–7 and 9, about 325 Lean lines in 31 theorems.

## Porting note for Stitchwort

### Lemmas in dependency order (Lean name → what it says)

Weights (section 4):
1. `wf_fuel`: more fuel doesn't change `wf` (induction on fuel; 15 lines).
2. `below_fuel`, `divisorSum_split`: split the divisor sum into d < K and K itself (needs a
   `rangeFrom` append lemma: `[2..K] = [2..K-1] ++ [K]`).
3. `divisorSum_plus`: Σ plus = [K ≥ 2] + Σ minus. A few lines, using `rfl` on `plus K`.

Periods (section 5), with `Cyc g L p` as above:
4. `cyc_zero`, `cyc_add`, `cyc_sub`, `cyc_mul` (p·t is a period). Each is a few `mod` rewrites.
5. `cyc_dvd`: smallest period p₀ divides any period. Uses `p − p₀·(p/p₀) = p % p₀`
   (`Nat.divModEq`) and `p % p₀ < p₀` (`Nat.modLess`).
6. `exists_min`, `smallest_period`: there is a least positive period, it divides L, and the
   periods are exactly its multiples. **Port differently.** Lean finds the least element
   classically (`by_cases` on a Prop). In Stitchwort, make the period test a `Bool`
   (`List.all` over 0..L−1) and define `smallestPeriod ds` as the first p in 1..L that passes.
   Then prove "it passes" and "nothing smaller passes" (`List.allRangeElim`/`allRangeIntro`
   exist). Stitchwort has no `Exists` type (core.sw has `And`, `Or`, `Void`), so return
   witnesses from functions: K = L / smallestPeriod, and "n divides K" as `K % n = 0` or as an
   explicit factor.

Blocks (section 6):
7. Index lemmas for `at ds i` (`getD`): of an append (left and right part), of `take`, and of
   `concat (replicate n b)` (`= b at i % k`); two lists of equal length that agree at every
   index are equal (`ext_getD`). None of these exist yet. `List.get` returns `Maybe`, so
   define `at` with a default.
8. `block_iff_cyc`: "every digit equals the one at i % k" ⇔ "k is a period", when k divides
   L. Needs `(x % L) % k = x % k` for k dividing L (`Nat.mod_mod_of_dvd`; **missing**,
   provable from `Nat.modAddMul`) and `(i + k) % k = i % k` (`Nat.addModSelf`; have).
9. `writtenAs_length` (k·n = L and k ≥ 1). **Have** as `repCount`/`repBlockLength`.
10. `writtenAs_iff`: for k·n = L, written n times ⇔ k is a period.

One id (section 7):
11. `written_iff_dvd`, `repeats_iff`: divisibility algebra. Cancel p₀ (`Nat.mulCancelLeft`;
    have), L/n = p₀·t (`Nat.divUnique`; have).
12. `count_k`: for each n only k = L/n counts (`List.sumRangeOne`/`sumRangeNone`; have).
13. `range'_split`, `count_id`, `count_plus`: swap the k and n sums (`List.sumBySwap`; have),
    drop the n > K terms, then apply 3.

Assembly (section 9):
14. `weighted_ids`, `range_split`, `invalid_eq`, `part2Correct`. The existing `weightedIds`,
    `rangeSplit`, `kFold` and `termsFold` do the same moves. The `Int` part (`invalidSplit`,
    `weightStep`, `plusCase`/`minusCase`, `totalSplit`) is no longer needed.

### What Lean's core library gave for free, and what Stitchwort has

| Lean core | Used for | Stitchwort |
|---|---|---|
| `Nat.mod_lt`, `mod_eq_of_lt`, `mod_add_mod`, `mod_add_div`, `add_mod_right`, `mod_self`, `mul_div_le` | periods | have: `modLess`, `modSmall`, `modAddMod`/`addModMod`, `divMod`, `addModSelf`, `modSelf`, `divMulLe` |
| `Nat.mod_mod_of_dvd` | blocks ⇔ periods | **write** (from `modAddMul`) |
| `Nat.mod_eq_sub_mod` | index of `concat (replicate …)` | **write** (or recurse with `addModSelf`) |
| `Nat.mul_div_cancel(_left)`, `div_le_self`, `eq_of_mul_eq_mul_left/right` | divisibility | have: `divUnique`, `mulCancelLeft`, `mulSuccCancel`; `divLeSelf` **write** (small) |
| `∣` with `dvd_of_mod_eq_zero`, `mod_eq_zero_of_dvd`, `le_of_dvd`, `dvd_refl` | divisibility | **no divides**: use explicit factors or `% = 0`; a few small lemmas |
| `Nat.mul_le_mul(_left/_right)`, `le_mul_of_pos_left/right`, `mul_pos` | bounds | partly: `leMulRight`, `leMulPos`; rest small |
| `Nat.strongRecOn` | least period; digit lemmas | not needed: least period by `Bool` search, digit lemmas done |
| `List.range'_succ`, `range'_append`, `mem_range'` | sums over ranges | `rangeFrom` unfolds by `rfl`; **append lemma to write** (check `List.sumByRangeShift`) |
| `List.any_eq_true` | `repeats` | have: `anyRangeElim`/`anyRangeIntro` |
| `List.length_take/drop`, `take_append_drop`, `take_left'`, `mem_of_mem_take/drop` | blocks | have: `lengthTake`, `takeAll`, `takeAppend`; drop lemmas only in section 8 (done) |
| `List.getD_eq_getElem?_getD`, `getElem?_append_left/right`, `ext_getElem` | index lemmas (7) | **write** (about 60–80 lines) |
| `List.length_flatten`/`replicate` | lengths | have: `lengthConcatReplicate` |
| `List.sum_range'` (Gauss), `foldl_append` | section 8 | have: `Nat.gaussSpan`, `Nat.fromDigitsAppend` |

### Where tactics did the heavy lifting

- **`omega`, 138 uses**: linear arithmetic with `+`, `−`, `max`/`min`, and `/` and `%` by
  literals. In the new sections it mostly checks index bounds (`i % k < k ≤ L`), range
  membership (`2 ≤ n ≤ size`), and `L/n ≤ L`. Each becomes a short chain of `Nat.leTrans`,
  `Nat.addSubCancel` and similar. These are the main cost of the port: expect 3–8 Stitchwort
  lines for each one-word `omega`. 56 are in sections 4–7 and 9 (4: 10, 5: 4, 6: 15, 7: 23,
  9: 4). Most of the rest are in section 8, which is already done.
- **`simp`, 93 uses**: unfolding definitions, choosing an `if` branch whose condition is known,
  list membership in `range'`, and `List.length` of append/singleton. In Stitchwort these
  become `rfl`, `Eq.cong`, `Bool.inspect` case splits and `List.filterKeep`/`filterSkip`-style
  lemmas.
- **`grind`, 2 uses**: two ring identities, both in section 8 (`foldl_digits`, `gauss`),
  which is already done.
- **`decide`, 10 uses**: only `0 < 10` and `1 < 10`. These are `rfl` in Stitchwort.
- **`by_cases` on a `Prop`**: only in `exists_min`. Port it as a `Bool` search (see 6).
- `rfl` already unfolds `plus K` to its recursive definition, as Stitchwort's `rfl` would.

### Estimate

- New Stitchwort proof: about **700–1,000 lines** for sections 4–7 and 9. That is the 325
  Lean lines times 2–3. The ratio comes from the digit bridge. It is 305 code lines in Lean.
  In Stitchwort today it is roughly 600–700 lines: `day02.sw` lines 46–229, `part2proof.sw`
  lines 29–210, and 34 `Nat.digits*`/`Nat.fromDigits*` lemmas in core.sw. This is a rough
  guess, not a measurement.
  Add about **150–250 lines** of library: index lemmas, `modModOfDvd`, a `rangeFrom` append,
  the least-period search, and small divisibility facts.
- Removed from `part2proof.sw`: the computed facts and counting (`blockCheck`, `viaBlocks`, the
  seven `*Checked` facts, `validFor`, `agreeAll` and `check2`…`check10`, the `plus`/`minus`
  tables) and the `Int` split. That is roughly 320 of its 605 lines, including the slowest
  parts to check (block checks about 1.3 s, `agreeAll` 1.3 s, `totalSplit` 1.5 s).
- Net: `part2proof.sw` goes from about 605 lines to about 1,000–1,300, plus about 200 lines
  of library. No computation-heavy steps remain, so checking should get faster. The
  per-(k, n) sums still have to be folded over a variable number of n instead of 2..10.
- It needs no new language feature. Fuel recursion, `match`, `calc`, `rewrite` and
  `Bool.inspect` cover everything.
