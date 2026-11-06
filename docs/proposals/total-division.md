# Proposal: `/` and `%` that need no proof the divisor isn't 0

**Status:** draft 1, 6 November 2026. Ticket SW-1238 (Matt, 4 Nov 2026: "I think it might be
interesting to consider a total modular operator ... We would want to do a design review of
simple languages in the space"). Nothing is built; this note stops for Matt's decisions
([§8](#8-decisions), Q1–Q6). Written against `main` at `46d6ea30`. Migration cost (hashes,
snapshots, sweeps) is not counted; options are judged by where they end up.

Related notes: [division.md](division.md) (SW-922: how `Nat.div` is *defined*, so that it
computes well on unknowns; this note is about its *type*), [function-equations.md](function-equations.md)
§3 (D2180, `if h:` equations), [proof-irrelevance.md](proof-irrelevance.md) (SW-93, SW-1429).
Related tickets: SW-973 (2021 day 15 friction, "division needs nonzero proof"), SW-741 (2024
day 8 friction, "compare ignoring proof args of / and %", since done by proof irrelevance).

Labels, as in the other notes:

- **[checked]**: read in this repository at the place given.
- **[ran]**: run for this note on 6 Nov 2026 with the release CLI on `main` (built 07:17 that
  morning), on scratch files outside the repository (§9 lists them).
- **[cited]**: read in the source linked, on 6 Nov 2026 (§9).
- **[inferred]**: my reasoning from checked or cited facts.
- **[unverified]**: believed, not confirmed.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [Prior art](#2-prior-art)
3. [The options](#3-the-options)
4. [Recommendation](#4-recommendation)
5. [What would change](#5-what-would-change)
6. [Risks](#6-risks)
7. [Evidence still to collect](#7-evidence-still-to-collect)
8. [Decisions](#8-decisions)
9. [Sources](#9-sources)

## 0. Summary

- **Today.** `x / d` and `x % d` take a hidden proof that `d` isn't 0, which `auto` looks for
  (`[auto ok: d ≠ 0]`). For a number written in the program (`n % 10`) it computes the fact and
  nobody notices. For a divisor that is a variable (a map's width, a bus's id, a computed place
  value) the program has to establish the fact first, or the call is `E-AUTO-STUCK`. The same
  holds for `Int`'s six divisions, `Nat.ceilDiv`, `Nat.divMod`, `Int.modNat`.
- **What it costs.** In AoC programs, `if d ≠ 0 … else` branches that can't happen on real
  input, helpers that match on the divisor only to make it `Succ k`, and a `d ≠ 0` parameter
  threaded through a definition and every theorem about it (2020 day 13: 11 theorems carry
  `[auto ok: bus.id ≠ 0]`). In std, 67 `[auto …: d ≠ 0]` parameters and 76 explicit `[ok := …]`
  arguments, many of them on lemmas that would be true without the hypothesis.
- **What it buys.** A program can never divide by 0, and a reader sees the assumption. Once
  (2024 day 7) the error made a program say what multiplying by 0 means.
- **Two of the ticket's three alternatives are already done.** A `Grid` carries a proof that
  its width isn't 0 (SW-1235), and an `if h: d ≠ 0 then x % d` now gets its equation, since the
  kernel treats two proofs of one fact as equal (SW-1429) **[ran]**. What is left is the
  question of the type.
- **Prior art splits three ways.** Lean 4, Rocq, Isabelle/HOL, Koka, Gleam and Pony make
  division total with `x / 0 = 0` and `x % 0 = x`. Agda, Idris 2 and F\* ask for a proof (Agda's
  is an instance argument found automatically, much like ours). Haskell, Elm's `modBy` and the
  JS `BigInt` operations throw. Why3 and Dafny make the divisor a proof obligation.
- **Recommendation.** Make `/` and `%` total on `Nat` and `Int`, with Lean's values: `x / 0 =
  0`, `x % 0 = x`. Drop the hypothesis from every std lemma that holds without it (about 20 of
  31 in `Nat/Arith.sw` and `Nat/Divides.sw`); keep it on the rest (`x % d < d`, `(a + b * d) /
  d = a / d + b`). The obligation moves from the call to the theorem, where it is needed.
  Stitchwort already works this way for `-` on `Nat` (`3 - 5 = 0`) and for `Float`'s `/`.

## 1. The problem

### 1.1 How division is typed today

`Nat.div` and `Nat.mod` take an `auto` proof **[checked]** (`crates/elab/src/std/core/Division.sw:31,37`):

```stitchwort
def Nat.div (n: Nat) (divisor: Nat): [auto ok: divisor ≠ 0] → Nat := Nat.divFuel n n divisor
def Nat.mod (n: Nat) (divisor: Nat): [auto ok: divisor ≠ 0] → Nat := n - (n / divisor) * divisor
```

So do `Int.div`, `Int.mod` (`core/Int.sw:138,148`), `Int.tdiv`, `tmod`, `fdiv`, `fmod`,
`modNat` (`Int/Basics.sw`), `Nat.divMod`, `Nat.ceilDiv` (`Nat/Arith.sw:150,367`) and
`Int.divMod` (`Int/Int.sw:280`) **[checked]**. The `Int` ones still have to cover a zero
divisor in their case trees, and do it with the proof: `| dividend, OfNat Zero => Void.absurd
(ok rfl)`.

`auto` finds the proof by computing (`n % 10`), from a fact in scope (`if d ≠ 0`, `h: 0 < d`,
`1 ≤ d`, a `let`-bound proof), through `omega` when the module loads it, or by a decision for
a shape it knows (`Nat.pow (Succ b) e ≠ 0`) (docs/guide/02-values-and-definitions.md:188;
aoc/NOTES-2024.md:1826–1831) **[checked]**. Otherwise:

```
[E-AUTO-STUCK] Error: can't decide `width ≠ 0` here
 1 │ def wrap (width column: Nat): Nat := column % width
   │ Note: establish it first, with `if h: … then … else …`
```

**[ran]** (`t2.sw`).

Underneath, the definition already gives an answer for 0: `Nat.divFuel n n 0` counts `n`
steps, so `n / 0` would be `n` and `n % 0` would be `n - n * 0 = n` (`stitchwort eval` on
`Std.Nat.divFuel 7 7 0` gives `7`, and a goal `Std.Nat.divFuel n n 0 = n` displays as `n / 0 = n`)
**[ran]** (`t4.sw`). The runtimes agree: the kernel native, the machine, the native backend and
JS all return the fuel for a zero divisor (`crates/core/src/native.rs:969`,
`crates/rt/src/prims.rs:198–205`, `crates/native/src/n1.rs:3891–3901`,
`crates/js/src/lib.rs:5127`) **[checked]**. The proof only stops anyone from asking. The `Int`
natives don't handle 0: `checked_div_euclid` gives `None`, and the fallback is a `BigInt` division that
would panic (`prims.rs:510`, `euclid` at 275; the panic **[inferred]**), and JS `BigInt` division by `0n` throws a
`RangeError` ([MDN](#9-sources)) **[checked]**, **[cited]**.

### 1.2 What it costs in programs

Every AoC program whose divisor is a variable, and what it does about the proof
**[checked]**:

| where | divisor | what the program does |
|---|---|---|
| 2020 day 3 (`treesOn`) | `map.width` | `let nonZero := map.widthNonZero`; the `Grid` type gained a proof field for this (SW-1235). The first version had a `wrap` helper that matched on the width |
| 2020 day 13 (`Bus.nextDeparture`) | `bus.id` | `if positive: bus.id ≠ 0 then Nat.ceilDiv from bus.id * bus.id else from`; 11 theorems in `Proofs/` take `[auto ok: bus.id ≠ 0]` |
| 2021 day 15 (`Cave.tiles`) | height, width | two parameters `[auto tall: cave.height ≠ 0] [auto wide: cave.width ≠ 0]`; `Cave` carries a proof field |
| 2024 day 7 (`canMake`) | `last`, `placeValue last` | `if last != 0 then … else target == 0` (a real case, §1.4); `placeValue` needed a new `auto` decision (`Nat.decPowSuccNotZero`) |
| 2024 day 8 (`divideBy`) | `divisor` | matches on `Zero` / `Succ below` only to give `/` a `Succ`: "unchanged for 0" |
| 2024 day 11 (`changeStone`) | `Nat.pow 10 …` | `auto`'s power decision |
| 2024 day 13 (`onlyPresses`) | `machine.determinant` | a `nonzero` parameter, threaded into 6 theorem statements; `pressesToCover` has `if step.x ≠ 0 then … else if step.y ≠ 0 then … else 0` |
| 2024 day 14 (`Space`) | width, height | proof fields in the record, `Space.of` with two `auto` parameters; 10 `[ok := ok]` in the proofs |
| 2025 day 1 | `Mod.size n` | `Mod` carries it |
| 2025 day 2 (`sumIn`) | `multiplier` | `if multiplier ≠ 0 then … else 0` |
| `Aoc.Common.Position.wrap` | height, width | two `auto` parameters, passed on by 4 theorems as `[ok := tall]`, `[ok := wide]` |

That is 11 places in the 71 AoC days in the repository. Literal divisors (`% 2`, `/ 90 % 4`, `% 8`,
`% modulus`) are most uses and cost nothing.

Counts of the syntax over the repository (a script that strips comments and strings; `/`
includes `Int` and `Float` division) **[ran]** (`count.py`):

| area | lines with ` % ` | with ` / ` | `[auto …: … ≠ 0]` parameters | explicit `[ok := …]` |
|---|---:|---:|---:|---:|
| AoC programs | 20 | 24 | | |
| AoC specs | 11 | 17 | | |
| AoC proofs | 149 | 107 | 32 (all of AoC) | 27 (all of AoC) |
| std | 383 | 331 | 67 | 76 |
| roguelike | 10 | 32 | 0 | 0 |
| examples | 113 | 116 | | 20 |

### 1.3 What it costs in proofs

Every lemma about `/` or `%` carries the hypothesis, whether it needs it or not. In
`Nat/Arith.sw` and `Nat/Divides.sw`, 31 theorems mention division and have a `d ≠ 0` (most as
`[auto ok: d ≠ 0]`) **[checked]**. `Nat.modMod`, `a % d % d = a % d`, is as true for `d = 0`
as for any other `d`, and Lean states it with no hypothesis (`Nat.mod_mod (a n : Nat) : (a % n)
% n = a % n`) **[cited]**. §5.1 goes through all of them.

Where the divisor is a variable, the hypothesis has to come from somewhere, and in AoC it is
usually threaded by hand: `Int.modNatLt (x.toInt + distance) size [ok := ok]` (2024 day 14),
`Nat.divUnique stone (Nat.pow 10 half) [ok := powTenNotZero half]` (2024 day 11) **[checked]**.

### 1.4 What it buys

The 2024 day 7 notes (aoc/NOTES-2024.md:1736–1740, 1820–1822) **[checked]**: "Because `%`
and `/` need a proof that the divisor isn't 0, the program had to say what multiplying by 0
means (anything times 0 is 0), so it is right for every input, not only for inputs without 0
... Stitchwort's way paid off here: it made the program handle a 0 in the input." That is the
one recorded case of the error finding a bug.

With total division the same program would have compiled and been wrong for an input such as
`0: 5 0`: `canMake` would ask whether `[5]` makes `0 / 0 = 0`, which it doesn't, though `5 *
0 = 0` **[inferred]**. Its theorem `canMakeReaches` (the backwards search equals the forwards
search) would then have failed to prove, so the day would still not have been finished wrong;
the bug would have been found by the proof instead of the type checker. In an unproved
program it would have stayed **[inferred]**. Buzzard puts it the same way for Lean: "The
failure will still however be the assertion that you have a denominator which you have not
proved is nonzero" **[cited]**.

### 1.5 What has changed since the ticket

The ticket (4 Nov) named two alternatives besides a total `%`. Both are built:

- **A `Grid` that carries a non-zero width:** SW-1235. `Grid` has `nonEmpty: (firstWidth rows
  == 0) = False`, and `Grid.widthNonZero` follows (`aoc/src/Aoc/Common/Grid.sw:144,156`)
  **[checked]**. `auto` doesn't look inside a record's fields, so a program still writes `let
  nonZero := map.widthNonZero` before the `%` (aoc/NOTES-2020.md:224–227) **[checked]**.
- **Proof irrelevance for `if h:` equations:** SW-1429 (merged 5 Nov). Day 3's original
  failure was `Not generated: … treesOn.eq.ifTrue … two proofs of it aren't known to be equal
  without proof irrelevance (D2180)`. Now the equations generator checks that the branch's
  proof is only passed where nothing computes on it, which is the case for `%`'s, and makes the
  equation. This file checks **[ran]** (`t1.sw`):

  ```stitchwort
  def wrapAt (width: Nat) (column: Nat): Nat := if nonEmpty: width ≠ 0 then column % width else 0

  theorem wrapAtPositive (width column: Nat) (ok: width ≠ 0): wrapAt width column = column % width :=
    wrapAt.eq.ifTrue width column ok
  ```

  So does rewriting the divisor of a `%` whose proof is about the old divisor (`t6.sw`)
  **[ran]**. (Two docs still describe the old limit: `docs/syntax.md` "Equations" under Guards,
  "An equation isn't generated … (D2180: `| (n, len) if n != 0 => len % n` …)", and
  `docs/guide/10-proofs.md:484`. A small follow-up, §7.)

So the friction left is smaller than when the ticket was filed: the `if` costs a line and a
dead branch rather than a lost equation. The decision is about whether the line, the branch
and the hypotheses on lemmas are worth what they buy (§1.4).

## 2. Prior art

| system | `x / 0`, `x % 0` | how the divisor is checked | source |
|---|---|---|---|
| **Lean 4** core | `0`, `x` (`Nat`); `Int.ediv` etc.: `0`, `x` | not at all; lemmas carry `0 < n` where needed | `Nat.div` docstring "Division by `0` returns `0`"; `Nat.mod`: "When the divisor is `0`, the result is the dividend rather than an error"; `Nat.div_zero`, `Nat.mod_zero`; Int docs: "`x / 0 = 0` and `x % 0 = x`" for all three conventions **[cited]** |
| **Mathlib** | `a / 0 = 0` in every `GroupWithZero` | same | Buzzard, Xena 2020 **[cited]** |
| **Rocq** (`nat`) | `0`, `x` | none | `Nat.div`: `match y with 0 => y …`; `Nat.modulo`: `0 => x` (Corelib `Init/Nat.v`) **[cited]** |
| **Rocq** (`Z`) | `0`, `x` | none; lemmas carry `b <> 0` or `b > 0` | `Zdiv_0_r: a / 0 = 0`, `Zmod_0_r: a mod 0 = a`, `Z_div_mod_eq_full` (no hypothesis), `Z_mod_lt` (`b > 0`) **[cited]**; earlier versions had `a mod 0 = 0` (Rocq Discourse) **[cited]** |
| **Isabelle/HOL** | `0`, `a` | none | `div_by_0: a div 0 = 0` (class `divide_trivial`), `mod_by_0: a mod 0 = a`, axiom `div_mult_mod_eq: a div b * b + a mod b = a` with no hypothesis (`Rings.thy`) **[cited]** |
| **Koka** | `0`, `x` | none | `divmod`: "Euclidean-0 is a total function, for the case where d==0 we have that D%0 == D and D/0 == 0" **[cited]** |
| **Gleam** | `/`: `0`; `int.modulo`: `Error` | none for the operator; `Result` functions | "division by zero returns zero, a behaviour taken from Pony, Coq, and Lean"; `int.divide`/`modulo`/`remainder` return `Error` for 0 **[cited]** |
| **Pony** | `0` | none; `/?` raises an error | "integer division by zero results in zero", chosen to "maintain a practical API and avoid undefined behaviour" **[cited]** |
| **Agda** stdlib | — | irrelevant instance argument `.{{_ : NonZero divisor}}`, found automatically for `suc n` | `_/_ : (dividend divisor : ℕ) .{{_ : NonZero divisor}} → ℕ`; `NonZero` is a one-field record so Agda "is far better at reconstructing meta-variable values"; `≢-nonZero : n ≢ 0 → NonZero n` **[cited]** |
| **Idris 2** | `divNat`, `modNat` partial | erased proof `(0 _ : NonZero y)` on `divNatNZ`, `modNatNZ` | `Data/Nat.idr` **[cited]**; the `Integral Nat` instance uses the partial ones **[cited]** |
| **F\*** | — | refinement: `val ( / ) : int -> nonzero -> Tot int`, `type nonzero = i:int{i <> 0}`, discharged by SMT | `ulib/Prims.fst` **[cited]** |
| **Why3** | logic: unspecified | logic functions total but axioms need `y <> 0`; program `div` has `requires { y <> 0 }` | `stdlib/int.mlw` **[cited]** |
| **Dafny** | — | verification condition | the reference manual defines `/`, `%` "for any integer `a` and non-zero integer `b`" **[cited]**; that a zero divisor is reported as "possible division by zero" is from a third-party mirror of a Stack Exchange question **[unverified]** |
| **Liquid Haskell** | — | refinement `{v:Int \| v != 0}` on `div`'s divisor | 0.8.0.2 tutorial slides; current spec files not read **[unverified]** |
| **Haskell** | exception | none | `base`: `div`/`mod` throw `DivideByZero` for every integer type in `base` (`GHC.Real` source comments) **[cited]** |
| **Elm** | `//`: 0; `modBy 0`: crash | none | `Basics.elm` docs say nothing about 0 **[cited]**; the behaviour is from Elm Discourse threads **[unverified]** |
| **JS `BigInt`** | `RangeError` | none | MDN **[cited]** |

Not covered: Roc (its docs page didn't load usefully; nothing is claimed about it).

What the arguments are:

- **For total division (Lean, Isabelle, Rocq, Mathlib).** Buzzard: "Mathematicians don't
  divide by 0 and hence in practice they never notice the difference"; "It is in the theorems
  where one puts the non-negativity hypotheses." A total function equals the partial one
  wherever the partial one is defined, so any theorem about one is a theorem about the other.
  Some laws hold without a hypothesis (`(a + b) / c = a / c + b / c` for fields) and need none
  **[cited]**. Hillel Wayne: `1/0 = 0` is consistent, "Nothing breaks and you can't prove
  something false", since `1/0` is not an inverse of 0 and `a/a = 1` keeps its `a ≠ 0`; he
  still prefers an error in a *programming* language **[cited]**. The choice of values comes from
  keeping `d * (x / d) + x % d = x` true at `d = 0`: with `x / 0 = 0`, `x % 0` has to be `x`
  (Koka says this, "property (1) still holds"; Isabelle's `div_mult_mod_eq` and Lean's
  `Nat.div_add_mod` are stated with no hypothesis) **[cited]**.
- **For the proof (Agda, Idris, F\*).** The type says what the function promises, and a
  division by zero is caught where it is written. Agda's cost is low because the proof is an
  instance argument found by search and irrelevant (`.{{…}}`), so two divisions with different
  proofs are equal **[cited]**. Stitchwort's `[auto ok: d ≠ 0]` is the same design with a
  stronger search (it computes, uses facts in scope and `omega`), and with proof irrelevance
  since SW-93 **[inferred]**.
- **For an error (Haskell, Pony's `/?`, Gleam's `int.modulo`).** Programs, not proofs: a zero
  divisor is a bug to report. Not an option for Stitchwort's `Nat`, whose functions are total
  in the kernel; an `Option` or `{Fail}` result is the equivalent (option C).

## 3. The options

Each is described by what changes in programs, in proofs, in std and in the runtimes.

### A. Keep the proof (status quo), with what is already built

`[auto ok: d ≠ 0]` stays. Programs establish the fact, records carry it (`Grid`, `Cave`,
`Space`, `Mod`), `if h:` equations now work. Nothing changes; the 11 places in §1.2 stay as
they are, and lemmas keep their hypotheses.

### B. Total `/` and `%` with Lean's values (`x / 0 = 0`, `x % 0 = x`)

Drop the `auto` parameter from `Nat.div`, `Nat.mod`, the six `Int` divisions, `Nat.divMod`,
`Nat.ceilDiv`, `Int.divMod`; define the zero case. Programs:

```stitchwort
-- 2020 day 3, no `let nonZero`:
|> .count (step => find { row = step * slope.down, column = step * slope.right % map.width } == Tree)

-- 2020 day 13, no dead branch, and the 11 theorems lose `[auto ok: bus.id ≠ 0]` unless they need it:
def Bus.nextDeparture (bus: Bus) (from: Nat): Nat := Nat.ceilDiv from bus.id * bus.id

-- 2024 day 8, no match on the divisor:
def divideBy (offset: Offset) (divisor: Nat): Offset :=
  { rows = offset.rows / divisor.toInt, columns = offset.columns / divisor.toInt }
```

**[inferred]**: these are sketches; whether each day's proofs go through unchanged is §7's
prototype. In 2020 day 13 the theorems that use `x % bus.id < bus.id` still need the
hypothesis; with a zero id `nextDeparture` would be `0`, which is fine if no theorem claims
otherwise for id 0.

Proofs: about two thirds of the `Nat` lemmas lose their hypothesis (§5.1); the rest keep it, as
an ordinary or `auto` parameter. `Nat.divides` can become `n % d == 0` with no case for 0, since
`n % 0 == 0` is `n == 0` (`Nat/Divides.sw:18–20` has the two cases today) **[inferred]**.

Runtimes: the `Int` natives need a zero branch (machine, native backend, JS); the `Nat` ones
need a change only if `divFuel`'s own value at 0 changes (§5.3).

### B′. Total with today's underlying values (`x / 0 = x`, `x % 0 = x`)

The same, but keep what `divFuel` already computes, so the `Nat` natives don't change. Fewer
laws hold at 0: `x / 0 / k = x / k`, but `x / (0 * k) = x`, so `Nat.div_div_eq_div_mul`
(`m / n / k = m / (n * k)`, no hypothesis in Lean) would need one; and no other system uses
these values, so a reader who knows Lean, Rocq or Isabelle would be surprised **[inferred]**.

### C. An `Option` (or `{Fail}`) result

`x /? d: Option Nat`, as Gleam's `int.divide` and Pony's `/?` **[cited]**. As the *only* division
it makes every program unwrap; as an addition to A or B it is a std function anyone can write
(`if d == 0 then None else Some (x / d)`). Not worth a design on its own **[inferred]**.

### D. A `NonZero` type, or a better instance search (Agda's way)

Today's `[auto ok: d ≠ 0]` already is Agda's instance argument (§2). What Agda has that we
don't is instance *declarations*: `instance nonZero : NonZero (suc n)` and user instances
**[cited]**. The Stitchwort analogue: let `auto` use a lemma marked for it, so
`Grid.widthNonZero` is found without `let nonZero := …`, and a record's proof field (`Space`'s
`widthPositive`) is found from the record. That removes the `let` lines and some `[ok := …]`,
not the dead branches, the threaded parameters on records without such a field (`Bus`), or
the hypotheses on lemmas. Independent of A/B; useful for other `auto` facts too (`i < n`)
**[inferred]**.

A `NonZero` *type* (`PosNat`, divisor of type `{ n: Nat, ok: n ≠ 0 }`) moves the proof into
the value. Every variable divisor is then converted, and `x % d.value`'s lemmas are about the
wrapper; it is option A with more ceremony **[inferred]**.

### E. A `Grid` (and records) carrying a non-zero width

Done (SW-1235, §1.5). Kept under B too: `Grid.widthNonZero` is still what proves `column %
map.width < map.width` **[inferred]**.

### F. Proof irrelevance for `if h:` equations

Done (SW-1429, §1.5) **[ran]**.

## 4. Recommendation

**B: total `/` and `%` on `Nat` and `Int`, with `x / 0 = 0` and `x % 0 = x`.**

1. **It puts the obligation where it does work.** A program only needs `d ≠ 0` for a claim
   about its result (`x % d < d`); a proof that makes the claim asks for it, once, where it is
   true. Today every call pays, and most lemmas carry a hypothesis they don't use (§5.1).
2. **Stitchwort already does this twice.** `Nat`'s `-` is truncated (`3 - 5 = 0`), and
   `omega` and every lemma about it live with that; `Float`'s `/` needs no proof and gives
   `infinity` (docs/syntax.md:2363) **[checked]**. A total `/` is the same kind of
   decision, and AoC has lived well with truncated `-`.
3. **The values are everyone's.** Lean, Rocq (`nat` and `Z`), Isabelle, Koka, Gleam's `/` and
   Pony agree on `x / 0 = 0`, and the provers on `x % 0 = x` **[cited]**. Lemma names and
   statements can follow Lean's, as std already mostly does.
4. **What is lost is small and partly recovered.** The one recorded catch (2024 day 7) would
   have been caught by the day's proof. Unproved programs lose a check; tests cover some of
   it, and the counterexample search on a theorem that forgot the hypothesis may find `d = 0`
   (that it tries small numbers first is **[unverified]**) **[inferred]**.
5. **It makes the remaining work of D smaller,** and E and F are kept.

Keep the `auto` proof on the lemmas that need it, so callers keep the convenience of `auto`
there: `Nat.modLt (x) (d): [auto ok: d ≠ 0] → x % d < d`.

`Int.modNat` (used for indexing, `x.modNat d < d`) is the one function whose point is the
bound; Q4 asks whether it keeps its proof.

## 5. What would change

### 5.1 Std lemmas

Std's `Nat` lemmas with a `d ≠ 0`, and whether each holds at `d = 0` with Lean's values
(checked by hand at `d = 0`; Lean's statement where it has one, from `Init/Data/Nat/*.lean`
**[cited]**) **[inferred]**:

| lemma (`Nat.…`) | statement | at `d = 0` | Lean's |
|---|---|---|---|
| `divMulLe` | `(n / d) * d ≤ n` | holds | `div_mul_le_self`, none |
| `divModEq` | `n = (n / d) * d + n % d` | holds | `div_add_mod`, none |
| `divLe` | `n / k ≤ n` | holds | `div_le_self`, none |
| `modSmall`, `divSmall` | `n < d → n % d = n`, `n / d = 0` | premise implies `d ≠ 0` | `mod_eq_of_lt`, `div_eq_of_lt`, none |
| `divUnique`, `modUnique` | `r < d → n = q * d + r → …` | premise implies it | – |
| `modSelf` | `d % d = 0` | holds | `mod_self`, none |
| `addDivModSelf` | `d + n = Succ (n / d) * d + n % d` | holds | – |
| `addModSelf` | `(d + n) % d = n % d` | holds | – |
| `addMulDivMod` | `a + b * d = (a / d + b) * d + a % d` | holds | – |
| `modAddMul` | `(a + b * d) % d = a % d` | holds | `add_mul_mod_self_right`, none |
| `modMod` | `a % d % d = a % d` | holds | `mod_mod`, none |
| `modAddMod`, `addModMod` | `(a % d + b) % d = (a + b) % d` … | hold | `mod_add_mod`, `add_mod_mod`, none |
| `mulSplit` | `a * b = a % d * b + (a / d * b) * d` | holds | – |
| `modMulMod`, `mulModMod` | `(a % d * b) % d = (a * b) % d` … | hold | `mul_mod`, none |
| `mulLeOfLeDiv` | `q ≤ n / d → q * d ≤ n` | holds | – |
| `divLeOfLtMul` | `n < Succ b * d → n / d ≤ b` | premise false | – |
| `modModOfMul` (Divides) | `len = t * k → x % len % k = x % k` (two hypotheses) | holds | `mod_mod_of_dvd`, none |
| `dividesMod` | `divides m n = (n % m == 0)` | holds | – |
| `modAddOfModZero`, `modMulOfModZero` | `z % m = 0 → …` | hold | – |
| `divLt`, `divLtSucc` | `1 < k → …` | premise implies it | `div_lt_self` keeps `1 < k` |
| **`modLess`, `modLt`** | `n % d < d` | **fails** | `mod_lt` keeps `0 < y` |
| **`addDivSelf`** | `(d + n) / d = Succ (n / d)` | **fails** | – |
| **`leDivOfMulLe`** | `q * d ≤ n → q ≤ n / d` | **fails** (`q = 1`) | `le_div_iff_mul_le` keeps `0 < k` |
| **`divAddMul`** | `(a + b * d) / d = a / d + b` | **fails** | `add_mul_div_right` keeps `0 < z` |
| **`divFuelBound`, `divFuelBoundStep`** | about `divFuel` | **keep** | – |

So of 31, 20 lose it outright, 4 because another premise implies it, and 7 keep it. On `Int`,
`Int.divAddMod` (`d * (a / d) + a % d = a`) loses it (Lean: holds unconditionally); `modNonneg`
and `modLtAbs` keep it (`-3 % 0 = -3`) **[inferred]**, **[cited]**. Dropping a hypothesis is a
stronger theorem, so callers are unaffected apart from explicit `[ok := …]` arguments, which
the sweep removes. Proofs of the lemmas that lose it need a case for 0, usually by computation
**[inferred]**.

### 5.2 Programs and their proofs

The 11 places of §1.2 can lose their `let`, branch, helper or parameter, except where the
branch is meaning, not plumbing: 2024 day 7's `if last != 0` (multiplying by 0) and 2024 day
13's determinant (Cramer's rule needs it, and the other branch searches) stay **[inferred]**.
Theorems that carry `[auto ok: … ≠ 0]` only to talk about the program's `%` lose it; those that
need a bound keep it. The number of each is §7's prototype.

### 5.3 Definitions and runtimes

- **`Nat.div`.** `Nat.divFuel fuel n 0` today counts the fuel down, giving `n`. For `n / 0 =
  0`, `Nat.divStep`'s `True` case would match on the divisor (`Zero => 0`), or `Nat.div` would;
  which one keeps `0 / d` and the stuck shape from division.md (one folded `divStep` on an
  undecided comparison) is for the implementation to measure. The `divFuel` native then
  changes its zero case from "the fuel" to `0` in four places (`core/native.rs`, `rt/prims.rs`,
  `native/n1.rs`, `js/lib.rs`), which the natives-against-definitions tests check
  **[checked]** places, **[inferred]** design.
- **`Nat.mod`** is `n - (n / d) * d`, which is `n` at 0 with either value; unchanged.
- **`Int`.** Each case tree's `OfNat Zero` arm returns `OfNat 0` (div) or the dividend (mod)
  instead of `Void.absurd (ok rfl)`. The natives for the six divisions and `modNat` need a zero
  test: today the machine would panic and JS would throw (§1.1) **[checked]**.
- **Hashes** of everything above division change, and pinned natives (`Float`'s,
  `TEXT_NATIVES`' `Nat.toText`) are re-pinned, as SW-922 did. Not counted (Matt).
- **`omega`** reads `x / k` and `x % k` for a literal `k` and treats a variable divisor as an
  atom; unchanged **[checked]** (docs/syntax.md, omega).

### 5.4 Docs

The language guide (02-values-and-definitions.md, "`/` needs a proof", `shelves` and
`averageOf`), syntax.md's operator table ("`/` and `%` need a proof that `b != 0`"), the
guide's chapter 10 and 11 examples (`share`), and the proving guide on division lemmas
**[checked]**. The `E-AUTO-STUCK` example in the guide needs another proposition.

## 6. Risks

- **Silent zeros in unproved programs.** A program that divides by an unexpected 0 gets 0 (or
  the dividend) and carries on, as in Pony and Gleam. In AoC every day has proofs, so the
  proof catches it; scripts and the roguelike have no such net **[inferred]**.
- **A lemma that is true only for non-zero divisors, stated without the hypothesis,** won't
  prove: the kernel says so; nothing unsound can follow **[inferred]**.
- **Readers' surprise.** `7 % 0` is `7`. The guide should say so in the first chapter that
  uses `%`, as Lean's docstrings do **[cited]**.
- **Specs.** A spec that divides by a variable now means something at 0 that the puzzle never
  said. The theorem's hypothesis says it as before **[inferred]**.

## 7. Evidence still to collect

1. **A prototype** (one lane): the definitions and natives of §5.3, the lemmas of §5.1, and
   the 11 AoC places of §1.2; then `task audit` of std and AoC and the roguelike check. It
   counts how many AoC theorems lose a hypothesis, how many keep it, and whether any proof
   needs more than deleting an argument.
2. **The reductions:** that `0 / d` still computes to `0` for unknown `d`, and that division.md's
   normal-form sizes for `(x * 3 + K) / 2^31` don't regress.
3. **Check times** of std and AoC before and after (expected unchanged).
4. **Docs drift** found here, independent of the decision: syntax.md's Guards "Equations"
   bullet and guide 10-proofs.md:484 still say an `if h:` branch using `%` gets no equation,
   which SW-1429 fixed **[ran]**. Worth a small ticket either way.

## 8. Decisions

- **Q1. Make `/` and `%` total on `Nat` and `Int`?** (B) [rec: yes] Assumes that proofs, not
  the type checker, are where AoC catches a zero divisor (§1.4), and that losing the check in
  unproved programs is acceptable.
- **Q2. Which values?** `x / 0 = 0`, `x % 0 = x` (Lean, Rocq, Isabelle, Koka), or today's
  underlying `x / 0 = x` (B′, no `Nat` native change). [rec: Lean's] More laws hold
  unconditionally, and it is what readers of other provers expect.
- **Q3. All of `Int`'s divisions too** (`div`, `mod`, `tdiv`, `tmod`, `fdiv`, `fmod`,
  `divMod`), with the same values? [rec: yes] Lean's three `Int` conventions all give `x / 0 =
  0`, `x % 0 = x` **[cited]**; one rule for every division is easier to remember.
- **Q4. `Int.modNat` and `Nat.ceilDiv`:** total too (`modNat x 0 = (x % 0).toNat`,
  `ceilDiv n 0 = 0`), or keep their proof because their point is the bound? [rec: total, with
  the bound a lemma that keeps the hypothesis] Consistency with `%`; the indexing callers
  (`Position.wrap`) already have the fact for the lemma.
- **Q5. Lemmas:** drop the hypothesis wherever the statement holds at 0 (§5.1, about 24 of
  31), keep it as `[auto ok: d ≠ 0]` on the rest? [rec: yes]
- **Q6. Option D's `auto` improvement** (lemmas marked for `auto`, record proof fields found):
  file separately? [rec: yes, backlog] Useful for `i < n` and other facts whatever Q1 says;
  with B it no longer matters for division.

## 9. Sources

Cited (read on 6 Nov 2026), 19:

1. Lean 4, `Init/Data/Nat/Div/Basic` API docs: `Nat.div_zero`, `Nat.mod_zero`,
   `Nat.div_add_mod`, `Nat.add_mul_div_right`, `Nat.div_lt_self`, `Nat.mul_div_cancel`.
   <https://lean-lang.org/doc/api/Init/Data/Nat/Div/Basic.html>
2. Lean 4 source, `src/Init/Prelude.lean` (master): `Nat.div` and `Nat.mod` docstrings,
   `Nat.mod_lt`. <https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean>
3. Lean 4 source, `src/Init/Data/Nat/Lemmas.lean`, `Div/Basic.lean`, `Div/Lemmas.lean`,
   `Basic.lean`, `Dvd.lean` (master; statements of `mod_mod`, `mul_mod`, `add_mod`,
   `mod_mod_of_dvd`, `div_mul_le_self`, `le_div_iff_mul_le`, `div_div_eq_div_mul`, …).
4. Lean 4, `Init/Data/Int/DivMod/Basic` API docs (Int conventions and their values at 0).
   <https://lean-lang.org/doc/api/Init/Data/Int/DivMod/Basic.html>
5. Kevin Buzzard, "Division by zero in type theory: a FAQ", Xena, 5 July 2020.
   <https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/>
6. Rocq Corelib `Init/Nat.v` (`divmod`, `div`, `modulo`).
   <https://rocq-prover.org/doc/master/corelib/Corelib.Init.Nat.html>
7. Rocq stdlib `ZArith.Zdiv` (8.17): `Zdiv_0_r`, `Zmod_0_r`, `Z_div_mod_eq_full`, `Z_mod_lt`.
   <https://rocq-prover.org/doc/V8.17%2Brc1/stdlib/Coq.ZArith.Zdiv.html>
8. Rocq Discourse, "Division and Mod by 0" (why the library's functions are total).
   <https://discourse.rocq-prover.org/t/division-and-mod-by-0/110>
9. Isabelle/HOL `src/HOL/Rings.thy` (GitHub mirror, master): `div_by_0`, `mod_by_0`,
   `semiring_modulo`'s `div_mult_mod_eq`.
   <https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Rings.thy>
10. Agda standard library, `Data.Nat.Base` (master): `NonZero`, `_/_`, `_%_`, `≢-nonZero`.
    <https://agda.github.io/agda-stdlib/master/Data.Nat.Base.html>
11. Idris 2, `libs/base/Data/Nat.idr` (main): `divNatNZ`, `modNatNZ`, `divNat`, `modNat`.
    <https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/Nat.idr>
12. F\*, `ulib/Prims.fst` (master): `nonzero`, `( / )`, `( % )`.
    <https://github.com/FStarLang/FStar/blob/master/ulib/Prims.fst>
13. Why3, `stdlib/int.mlw` (master): `EuclideanDivision`, `ComputerDivision`.
    <https://github.com/AdaCore/why3/blob/master/stdlib/int.mlw>
14. Dafny Reference Manual, integer division and modulus (the part from character 100,000).
    <https://dafny.org/latest/DafnyRef/DafnyRef>
15. Koka, `std/core/int` docs (`divmod`, Euclidean-0 division).
    <https://koka-lang.github.io/koka/doc/std_core_int.html>
16. Gleam stdlib, `gleam/int` docs. <https://gleam-stdlib.hexdocs.pm/gleam/int.html>
17. Pony tutorial, "Divide by Zero". <https://tutorial.ponylang.io/gotchas/divide-by-zero.html>
18. Hillel Wayne, "1/0 = 0". <https://www.hillelwayne.com/post/divide-by-zero/>
19. MDN, "RangeError: BigInt division by zero".
    <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Errors/BigInt_division_by_zero>

Used only through search-result summaries, so supporting only claims marked **[unverified]**
(or, for Haskell, a claim also in `base`'s source comments as the search quoted them): GHC
`GHC.Real` source on Hackage (base 4.17, 4.19); Elm Discourse "Division by Zero" and "Integer
division by zero"; Liquid Haskell 0.8.0.2 slides; a mirror of a Stack Exchange question on
Dafny's "possible division by zero". Also read, for what `elm/core`'s docs say (nothing about
0): `elm/core` `src/Basics.elm`.

Not read, so supporting nothing: Roc's `Num` docs (the page didn't load usefully), current
Liquid Haskell spec files, Dafny's source for its error message, any academic paper on
division by zero in type theory.

Repository (read in part): `crates/elab/src/std/core/Division.sw`, `core/Int.sw`,
`Int/Basics.sw`, `Int/Int.sw`, `Nat/Arith.sw`, `Nat/Divides.sw`; `crates/core/src/native.rs`,
`crates/rt/src/prims.rs`, `crates/rt/src/natives.rs`, `crates/native/src/n1.rs`,
`crates/js/src/lib.rs`; `aoc/NOTES-2020.md` (day 3), `aoc/NOTES-2024.md` (day 7); the AoC
programs named in §1.2; `docs/proposals/division.md`, `function-equations.md`,
`proof-irrelevance.md`, `docs/syntax.md`, `docs/guide/02-values-and-definitions.md`,
`docs/proving-guide.md` §6; tickets SW-1238, SW-1429, SW-741, SW-973.

Scratch files (not committed; session scratchpad `div/`): `count.py` (the counts in §1.2),
`t1.sw` (`if h:` equations with `%`), `t2.sw` (`E-AUTO-STUCK`), `t4.sw` (`divFuel` at 0),
`t5.sw`, `t6.sw` (rewriting a divisor), and `lean-src/` (the Lean files of source 3).
