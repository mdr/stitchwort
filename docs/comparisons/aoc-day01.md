# AoC 2025 day 1: the Stitchwort proof next to Lean 4, Agda and Idris 2

**Date:** 19 October 2026. **Code:** `comparisons/aoc-day01/` (the commands to check
each version are in its README). **Stitchwort version:** `aoc/day01.sw`.

Labels used below:

- **[checked]**: I ran it, or read it in the installed library or tool output;
- **[cited]**: taken from the linked documentation;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

## 0. The short version

All three ports prove the same theorem as Stitchwort, for every dial size, start and
list of turns, and all three check fully **[checked]**. The theorem is
`zerosPassedCorrect`: summing the arithmetic count `zerosDuring` over the turns gives
the same number as expanding each turn into single clicks and counting the clicks that
land on 0.

- **Lean 4** (core library only, no Mathlib) was quickest to write, about 15 minutes, and
  its proof is about half the size of Stitchwort's: 5,000 characters against 11,500.
  Almost all of the saving comes from `omega`, `simp` and `grind`. These tactics do the
  shuffling that Stitchwort's `Eq.trans (Eq.cong (\x => …))` chains do by hand:
  `a + 1 + n = a + (n + 1)`, `±1`, commutativity, and integer casts. **None of them can
  reason about `x / s` or `x % s` when `s` is a variable.** So the Lean proof splits into
  the same cases as Stitchwort's, and uses the same kind of library lemmas
  (`Nat.mod_self`, `Nat.add_div_left`, `Nat.mod_eq_of_lt`).
- **Agda** (with its standard library) took about 25 minutes. Like Stitchwort, it has no
  tactics and proofs are terms. Three things made it easier: `rewrite`, the `≡-Reasoning`
  notation for chains of equalities, and a large `Data.Nat.DivMod` library. Its proof is
  8,100 characters. Its integer `mod` library is as thin as Stitchwort's, so the integer
  part of the proof follows Stitchwort's `backFrom` almost step for step.
- **Idris 2** (base and contrib) took about 35 minutes, and it needed two workarounds.
  First, Idris has no integer type that proofs can use, so `move` had to be changed to use
  only `Nat`: going left one click is the same as going right `highest` clicks. Second,
  `mod` had to be hidden behind a module boundary so that the type checker would stop
  unfolding it. That second problem is the one Stitchwort's `Dial.place` works around.
- **Arithmetic on literals:** Lean and Agda check the puzzle example while type-checking
  (`decide +kernel` and `refl`) in well under a second, because their checkers do closed
  `Nat` arithmetic with machine big integers. Stitchwort's checker slowed down on `% 100`,
  and so did Idris's.

What Stitchwort would gain most from, ranked (details in §5):

1. a `calc` notation for chains of equalities, and a `rewrite` term;
2. more prelude lemmas about `/` and `%` on `Nat` and `Int`, including uniqueness of
   quotient and remainder;
3. native arithmetic on closed number literals in the checker;
4. an arithmetic normaliser written as a proof by reflection (a term, not a tactic);
5. definitional proof irrelevance, which matters little for this day.

## 1. The table

The numbers ignore blank lines and comments. "Definitions" counts everything before the
`Proofs` banner, including the parser and examples. A "helper" is any declaration in the
proof section other than `zerosPassedCorrect` and `part2Puzzle`, proof-only definitions
like `zerosAfter` included. Check times are wall clock on this Mac (Apple silicon) and
include starting the prover.

| | Stitchwort | Lean 4.34.1 | Agda 2.8.0 + stdlib 2.3 | Idris 2 0.8.0 |
|---|---|---|---|---|
| Lines of definitions | 57 | 48 | 66 | 58 |
| Lines of proof | 145 | 100 | 141 | 172 + 22 (`DialArith.idr`) |
| Characters of proof (spaces squeezed) | 11,529 | 5,006 | 8,067 | 9,495 + 802 |
| Helper declarations | 27 | 14 | 24 | 28 + 4 |
| Check time | 0.16 s | 0.6 s | 4.7 s from clean, 4.2 s cached; about 3.2 s of it loads the stdlib | 1.7 s from clean |
| Checked fully? | yes | yes | yes, with `--safe` | yes, `%default total`, no holes |
| Example checked while type-checking? | yes (`test`) | yes (`decide +kernel`) | yes (`refl`) | no; only by running it (§3.3) |
| My time to write it | (existing) | about 15 min | about 25 min | about 35 min, including chasing a slow check |
| Download through Nix | 5 MB binary | 648 MiB (2.5 GiB unpacked), 83 s | 533 MiB (2.4 GiB unpacked), 138 s | 17.6 MiB (83 MiB unpacked), 3.5 s |

All rows are **[checked]**. Sources: `wc`/`grep` over the files, `time` around the commands
in the README, and the `nix shell` output for sizes (Lean's size comes from the
cache.nixos.org narinfo, `FileSize: 679245015`). Stitchwort's time is
`target/release/stitchwort check aoc/day01.sw` with the main checkout's release build. In
the Agda row, the 3.2 s for the standard library is **[inferred]**: a second run with
`Day01.agdai` cached still took 4.2 s.

The output that shows each check is clean, run from each directory:

```
$ nix shell nixpkgs#lean4 -c lean Day01.lean; echo "exit $?"
(3, 6)
exit 0

$ nix shell --impure --expr 'with import <nixpkgs> {}; agda.withPackages (p: [ p.standard-library ])' -c agda --safe Day01.agda
Checking Day01 (/…/comparisons/aoc-day01/agda/Day01.agda).

$ nix shell nixpkgs#idris2 -c idris2 -p contrib --check Day01.idr; echo "exit $?"
1/2: Building DialArith (DialArith.idr)
2/2: Building Day01 (Day01.idr)
exit 0
$ ./build/exec/day01
(3, (6, 6))
```

(The Idris check also prints contrib's deprecation warnings, which I left out. Lean's
`#print axioms zerosPassedCorrect` gives `[propext, Classical.choice, Quot.sound]`,
Lean's standard axioms, which `omega` and `simp` use. There is no `sorry`.)

**How the ports differ from Stitchwort's version.** All keep the same statement shape:
`Dial highest` holds a position and a proof that it is at most `highest`; `Turn` is
`Left n | Right n`; there are two counts; and the theorem is stated for all inputs.

- In Lean and Agda, `move` uses integers, as in Stitchwort.
- In Idris, `move (Left n)` adds `highest * n` in `Nat`, because Idris has no integers
  that proofs can use (§3.3).
- Agda and Idris use their own small `count`-style helpers where the library's versions
  were awkward. Idris base also has no `scanl` and no structurally recursive `sum`, so the
  file defines them **[checked]**.
- In Lean, the parser reads digits by hand: `String.toNat?` doesn't reduce in the kernel,
  so `decide` couldn't check the parsed example **[checked: the `decide` error]**.

## 2. The key fragment: one click left

The left turn is the interesting part. One click left from 0 goes to `highest`, and from
any other position goes down by one. The count `((size - p) % size + n) / size` must then
grow by exactly the right amount. Here is each version's lemma for that step.

**Stitchwort** needs four lemmas for the count: `stepLeft`, `stepLeftFrom`,
`stepLeftTop`, and `leftZero`/`leftOne`. The position needs `stepLeftAt`, `backFrom`,
`backFar` and four `subNatNat` lemmas. Here is one case of the count:

```
theorem stepLeftFrom (highest : Nat) : (m : Nat) -> Succ m <= highest -> (n : Nat) ->
    Bool.toNat (m == 0) + ((Succ highest - m) % Succ highest + n) / Succ highest
      = ((Succ highest - Succ m) % Succ highest + Succ n) / Succ highest
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Succ ((x + n) / Succ highest)) (Nat.modSelf (Succ highest)))
      (Eq.sym (Eq.trans (Eq.cong (\x => (x + Succ n) / Succ highest) (Nat.modSmall highest (Succ highest) (Nat.leRefl highest)))
        (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addSucc highest n)) (Nat.addDivSelf (Succ highest) n))))
  | Succ j, h, n => …
```

**Lean 4.** One lemma covers every case. Each case is closed by `simp` with the right
`mod`/`div` facts, then `omega` or `grind` for what remains:

```lean
theorem stepLeft (h a p n : Nat) (ha : a ≤ h) (hp : p = if a = 0 then h else a - 1) :
    (if p = 0 then 1 else 0) + ((h + 1 - p) % (h + 1) + n) / (h + 1)
      = ((h + 1 - a) % (h + 1) + (n + 1)) / (h + 1) := by
  subst hp
  rcases a with _ | m
  · rcases h with _ | h
    · simp; omega
    · simp [Nat.mod_self, show h + 1 + 1 - (h + 1) = 1 by omega,
        Nat.mod_eq_of_lt (show 1 < h + 1 + 1 by omega)]
      grind
  · simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    rcases m with _ | m
    · simp [Nat.mod_self, Nat.mod_eq_of_lt (show h < h + 1 by omega),
        show h + (n + 1) = (h + 1) + n by omega, Nat.add_div_left n (Nat.succ_pos h)]
      omega
    · rw [Nat.mod_eq_of_lt (show h + 1 - (m + 1) < h + 1 by omega),
        Nat.mod_eq_of_lt (show h + 1 - (m + 1 + 1) < h + 1 by omega)]
      simp; congr 1; omega
```

Where the position lands after one click, Stitchwort's `leftZero`, `leftOne`, `backFrom`
and `subNatNat…` lemmas, is a single Lean lemma, `moveLeftOne`, of 9 lines. `omega`
proves `-1 = h + (h + 1) * (-1)` and the integer casts. The core library lemmas
`Int.add_mul_emod_self_left` and `Int.emod_eq_of_lt` do the rest. Composing clicks
(`leftAt`) is `Int.sub_emod`, `Int.emod_emod` and `congr; omega` **[checked]**.

**Agda.** The same case split as Stitchwort's. `rewrite` takes the place of the
`Eq.cong (\x => …)` motives, and the standard library's `DivMod` lemmas fill the gaps:

```agda
stepLeft h zero _ n rewrite leftZero h with h
... | zero  = trans (cong suc (n/1≡n n)) (sym (n/1≡n (suc n)))
... | suc k rewrite m+n∸n≡m 1 k | modSelf (suc k) = refl
stepLeft h (suc m) a≤h n rewrite leftOne h m a≤h with m
... | zero rewrite modSelf h | m≤n⇒m%n≡m (≤-refl {h}) | +-suc h n =
  sym ([n+m]/n≡1+m/n (suc h) n)
... | suc j rewrite m≤n⇒m%n≡m (m∸n≤m h j) | m≤n⇒m%n≡m (m∸n≤m h (suc j)) =
  cong (λ x → (x + n) / suc h) (+-∸-assoc 1 (<⇒≤ a≤h)) ⨾ cong (_/ suc h) (sym (+-suc (h ∸ suc j) n))
```

The position part, `back`, is 24 lines of `≡⟨ … ⟩` chains. It splits on `n ≤? h`, like
Stitchwort's `backFrom`/`backFar`, because `Data.Integer.DivMod` has only five lemmas
about `%ℕ` **[checked: grep of the installed library]**.

**Idris 2.** The same shape as Agda, written with `rewrite … in`. All the division facts
come from one contrib theorem, `DivisionTheoremUniqueness`: if `x = q * s + r` and
`r < s`, then `x / s = q` and `x % s = r`. With that, `modSelf`, `modAddSelf`, `divAddSelf`,
`modSmall` and `modPlus` are each a line or two:

```idris
stepLeft h (S m) le n = rewrite leftSucc h m le in case m of
  Z => rewrite modSelf h in rewrite minusZeroRight h in
       rewrite modSmall {h} {x = h} (LTESucc reflexive) in
       rewrite sym (plusSuccRightSucc h n) in sym (divAddSelf h n)
  S j => rewrite modSmall {h} (LTESucc (minusLte h j)) in
         rewrite modSmall {h} (LTESucc (minusLte h (S j))) in
         rewrite minusSucc h j (lteSuccLeft le) in
         cong (divS h) (plusSuccRightSucc (minus h (S j)) n)
```

## 3. What made each easier or harder

### 3.1 Lean 4

- **Tactics and `omega`: a large win for bookkeeping, none for division.** The places
  where Stitchwort needs `Nat.addSucc`, `Nat.addOne`, `Nat.subSuccRight` or
  `subNatNatSucc` inside an `Eq.cong` motive are all a bare `omega` in Lean. Integer
  casts (`↑(a + 1) % ↑s` against `(a + 1) % s`) are `norm_cast` **[checked]**. But `omega`
  treats `x / s` with a variable `s` as an unknown. Its failure messages list
  `↑(n + 1) / ↑(h + 1 + 1)` and `↑(1 + n) / ↑(h + 1 + 1)` as separate atoms, so it can't
  even see that they are equal **[checked: omega output]**. `grind` failed on
  `(s + n) / s = n / s + 1` and on `((x % s) - 1) % s = (x - 1) % s` **[checked]**. So the
  division reasoning is the same as Stitchwort's: split into cases (`a = 0`, `h = 0`,
  `m = 0`), then apply `mod_self` / `mod_eq_of_lt` / `add_div_left`. Lean's documentation
  describes `omega` as linear arithmetic over `Int` and `Nat`, with `/` and `%` only by
  literal constants **[unverified: from memory; consistent with the failures above]**.
- **Library lemmas.** Core Lean already had every `Nat`/`Int` lemma I needed:
  `Nat.mod_add_mod`, `Int.sub_emod`, `Int.emod_emod`, `Int.add_mul_emod_self_left`,
  `List.scanl_append`, `List.countP_append` **[checked]**. A list library with `scanl`
  lemmas meant `zerosAfterAppend` was a one-line `simp`; in Stitchwort it is a hand
  chain through `List.scanLeftAppend`.
- **Proof irrelevance.** Lean has it definitionally. With `@[ext] structure Dial`,
  `turnAt` is `ext; exact leftAt d n`. Stitchwort's `dialExt`/`dialExtAt` (8 lines, with
  `J` and `Bool.uniqueEq`) has no Lean counterpart **[checked]**.
- **Literals.** `decide +kernel` checked the parsed example, including the 600-click
  specification, inside the 0.6 s total **[checked]**. Lean's reference says the kernel
  represents `Nat` literals with GMP and overrides `+ - * ==` and comparisons with
  primitives; it lists `div`/`mod` as overridden only at run time
  ([Lean reference, Natural Numbers](https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/))
  **[cited]**. Even so, the `% 100` here was not slow **[checked]**.
- **Friction.** `simp`'s behaviour is opaque: twice a `simp` closed more or less than I
  expected ("No goals", "unused simp argument"). Lean 4.34 also deprecated `if_pos`/`if_neg`
  **[checked: warnings]**, so tactic proofs depend on the library's simp set and naming
  in a way Stitchwort's terms don't.

### 3.2 Agda

- **Same design as Stitchwort, with better notation.** There are no tactics, but:
  - `rewrite e` abstracts the left side of `e` in the goal, so you don't write the
    motive `\x => …` yourself;
  - `begin … ≡⟨ p ⟩ … ∎` lays a chain of `trans` steps out one equation per line, with
    each intermediate expression written down and checked;
  - `with` does case analysis on a computed value (`with m ≤? h`).

  Those three account for most of the difference from Stitchwort's 11,500 characters
  **[inferred]**.
- **Library.** `Data.Nat.DivMod` has about 60 lemmas, among them `n%n≡0`, `m≤n⇒m%n≡m`,
  `%-distribˡ-+`, `m%n%n≡m%n`, `[m+n]%n≡m%n`, `m/n≡1+[m∸n]/n`, `m<n⇒m/n≡0` and `n/1≡n`
  **[checked: grep of the installed source]**. `Data.Integer.DivMod` has five, which is
  why `back` was the longest lemma.
- **Proof irrelevance.** It isn't definitional for `≤`, but `≤-irrelevant` is in the
  library, so `dialExt` is one line **[checked]**.
- **Rough edges.**
  - `rewrite` fails on an equation with an instance argument (`n%n≡0` needs
    `{{NonZero n}}`), so I wrapped it as `modSelf`.
  - `rewrite` also fails when the goal has already reduced past the term. After
    `-[1+ n ] %ℕ d` unfolds to its `with` helper, there is nothing left to match, and I had
    to write explicit `≡⟨⟩` chains **[checked: both errors]**.
  - The `+_` constructor of `ℤ` clashed with the section `(b +_)`.
  - Stitchwort's checker has no such surprises, because there is no `rewrite`.
- **Literals.** `refl` on the example (with `% 100` and integers) is fast. Agda evaluates
  closed `Nat` terms with Haskell integers, including `div-helper`/`mod-helper`
  ([Agda built-ins](https://agda.readthedocs.io/en/latest/language/built-ins.html))
  **[cited; checked that the file checks quickly]**.

### 3.3 Idris 2

- **No proof-friendly integers.** `Integer` is a primitive, and contrib has no `ZZ` module
  in 0.8.0 **[checked: find over contrib]**. So `x - n` on integers can't be reasoned
  about for a variable `x` **[inferred]**. I changed `move (Left n)` to add `highest * n`
  modulo `highest + 1`, which is the same position. This is the one place where a port's
  program differs from Stitchwort's.
- **Uniqueness of quotient and remainder is the right base lemma.** contrib's
  `DivisionTheoremUniqueness` plus `DivisionTheorem` were enough to derive every
  `mod`/`div` fact needed, each with an explicit quotient and remainder **[checked]**.
  The prelude would gain most from this one lemma (§5).
- **Unfolding.** The type checker unfolds `modNatNZ` into its fuel-driven helper `mod'`.
  This broke `Calc` steps ("Can't solve constraint between: div' a a h and qa", and
  between `mod' …` and `if lte …`) **[checked]**. I moved `modS`/`divS` into a second
  module behind `export`, which hides their bodies. That is the same problem Stitchwort's
  `Dial.place` solves ("keeps `Int.modNat` folded"). Hiding them means `Refl` can no longer
  compute the example: `solvePart1 [Left 50] = 1` fails with `Refl` **[checked]**.
- **A slow check.** With `mod` still visible, merely declaring
  `exampleAnswers : (solvePart1 example, solvePart2 example) = (3, 6)` (with a hole as
  its proof) made checking run for more than 2 minutes before I killed it, while the same
  file without that declaration checked in 1 s **[checked]**. A small closed
  `modNatNZ (50 + 99 * 68) 100 ItIsSucc = 82` by `Refl` was fast (1.5 s) **[checked]**.
  So it isn't plain literal arithmetic; my guess is the elaborator normalising the whole
  example in unary `Nat` **[unverified]**.
- **Smaller points.**
  - Implicit arguments used at run time need binding (`{h : Nat} ->`), because
    auto-bound implicits are erased.
  - `Left`/`Right` didn't clash with `Either`'s constructors.
  - `Syntax.PreorderReasoning`'s `Calc` gives chains like Agda's.

## 4. What Stitchwort does better

- **Speed and size.** It checks in 0.16 s, against 0.6 s, about 4 s and 1.7 s. It is a
  5 MB binary, against 650 MB and 530 MB downloads for Lean and Agda **[checked]**.
- **Stable, explicit proofs.** Every step is a named lemma applied to explicit
  arguments. Nothing depends on a simp set, on lemma names that get deprecated (Lean
  4.34's `if_pos`; Agda stdlib 2.3's `scanl` and `sum` both moved **[checked: warnings]**),
  or on what `rewrite` happens to find in a normalised goal.
- **Programs read as the puzzle.** The pipeline definitions are as short as Lean's and
  shorter than Agda's or Idris's. The prelude's `Text.toNat` works where Lean's
  `String.toNat?` would not reduce in the kernel **[checked]**.
- **Integers you can prove things about.** `Int.modNat` and `Int.modNatLt` exist and
  reduce. Idris has nothing equivalent **[checked]**.
- **Auto-bound names.** `(d : Dial highest)` already binds `highest`, as Agda's
  `variable` and Lean's auto-bound implicits do. Idris needs explicit `{h : Nat}` when
  `h` is used at run time **[checked]**.

## 5. What Stitchwort would benefit from, ranked

Each item fits a design without tactics, where proofs are terms. I rank by how much of
the gap to Lean and Agda each closes in this proof, then by effort. The efforts are rough
guesses **[inferred]**.

1. **`calc` chains and a `rewrite` term (notation only).**
   - `calc a = b := p; _ = c := q` would elaborate to `Eq.trans`, as Agda's `≡-Reasoning`
     and Idris's `Calc` do. Each step's expression is written out and checked.
   - `rewrite e in t` would infer the motive by abstracting `e`'s left side in the
     expected type, then produce `J` or `Eq.cong` as today.

   Together these remove nearly every hand-written `\x => …` motive, which is most of the
   length of `stepLeftFrom`, `stepRight` and `zerosPassedSplit`. Agda shows that this
   brings a term-only proof to about Agda's size (8,100 characters against 11,500).
   Effort: `calc` is small (parser and desugaring, a few days). `rewrite` is medium: it
   needs the goal type known at that point (bidirectional checking) and an abstraction
   step, and Agda's failure modes above are the edge cases to test.
2. **Prelude lemmas for `/` and `%`.** The main one is uniqueness: `x = q * s + r` and
   `r < s` imply `x / s = q` and `x % s = r`. The others follow from it (Idris's route):
   - `(a % s + b) % s = (a + b) % s`
   - `a % s % s = a % s`
   - `(s + n) / s = 1 + n / s` (exists as `addDivSelf`)
   - `x / 1 = x` (exists)

   For `Int.modNat` the two needed facts are `modNat (x + k * s) = modNat x` and
   `modNat (x - 1)` of a position. With those, `backFrom`/`backFar` and the four
   `subNatNat` lemmas in day 1 would go. Effort: small (a day or two of prelude proofs).
   It also helps every later day.
3. **Native arithmetic on closed literals in the checker.** Lean's kernel and Agda both
   evaluate closed `Nat` arithmetic with big integers, so `refl`/`decide` on the puzzle
   example and `% 100` cost nothing there. Stitchwort's own note says `% 100` "unfolds to
   … a hundred additions". `docs/proposals/native-numbers.md` is the place for this.
   Effort: medium. It has to agree exactly with the unary definitions, so the risk is in
   conversion checking.
4. **An arithmetic normaliser by reflection.** This is the term-level counterpart of
   `omega`/`simp_arith`. A checked prelude function normalises linear `Nat`/`Int`
   expressions, and a lemma `normalise e1 = normalise e2 -> eval e1 = eval e2` is applied
   as an ordinary term. The elaborator only has to quote the goal into the `e1`/`e2`
   syntax, as Agda's `Data.Nat.Tactic.RingSolver` macros do. Lean core's `Nat.Linear`
   (used by `simp_arith`) works this way **[unverified: from memory]**. Nearly all of
   what `omega` did in the Lean port was this kind of goal (`a + 1 + n = a + (n + 1)`,
   casts, `±1`). It would not handle division by a variable either. Effort: large
   (quoting, plus a verified normaliser). Item 1 gets much of the benefit sooner.
5. **Definitional proof irrelevance** (`docs/proposals/proof-irrelevance.md`). In this
   proof it would save only `dialExt`/`dialExtAt`, 8 lines. Lean's `ext` made it free,
   while Agda and Idris used an ordinary `≤`-uniqueness lemma in one line. A
   `Bool.uniqueEq`-based `Dial.ext` in the prelude, or a derived ext lemma for records,
   would get most of that saving now. The proposal has other reasons; for day 1 it is
   low priority.

Things I don't recommend on this evidence:

- Copying Lean's `simp`. It saved lines, but it made the proofs brittle and hard to read
  (§3.1).
- Adding a general tactic language. Items 1 to 4 cover what the tactics did here.

## Sources

- Lean reference, Natural Numbers: https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/
- Agda built-ins: https://agda.readthedocs.io/en/latest/language/built-ins.html
- Agda standard library 2.3 source, as installed by nixpkgs: `Data/Nat/DivMod.agda`,
  `Data/Integer/DivMod.agda`, `Data/Integer/Base.agda` (`_%ℕ_`, `_⊖_`)
- Idris 2 0.8.0 contrib, `Data.Nat.Division` (read with `:browse` in the REPL)
