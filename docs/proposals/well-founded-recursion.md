# Proposal: well-founded recursion, `decreasing n` instead of fuel

**Status:** draft 1, 22 October 2026. Design only: nothing is built. Ticket SW-199, decision
D472 (write this note). Decisions D473 to D475 ([§10](#10-decisions)) are open. The critical
review ([§9](#9-critical-review)) was written as a separate, adversarial pass by the same
author, not by an outside reviewer. Related: [equation-lemmas.md](equation-lemmas.md) (D226
to D233; this note brings back a narrow form of D231), [partial.md](partial.md) (`{Partial}`,
for loops that really might not end), [fast-runtime.md](fast-runtime.md) (`crates/rt`), and
the day 4 community comparison ([aoc-day04-community.md](../comparisons/aoc-day04-community.md)
§3.3, D422).

**The short answer.** Let a definition say `decreasing <a Nat expression>`. The compiler
turns it into an ordinary structurally recursive helper with a hidden fuel argument that
carries its own proof of being enough, so the kernel is unchanged and tests and `rfl` keep
computing. The compiler also proves, once per definition, the equation a user wants to
rewrite with (`f.unfold`), so nobody writes a "fuel is enough" or "fuel doesn't matter" lemma
again. The fast runtime and the JS backend drop the fuel and run the recursion as written.
This is option B of the ticket, made concrete; [§3](#3-what-we-ran) shows it working by hand
on `Nat.digits`.

This note can be read without knowing type theory. Code references were checked at commit
`786a83e9`. Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given, or in a
  source listed at the end ([L1], [C1] and so on);
- **[run]**: a Stitchwort or Lean program run on 22 October 2026 (Stitchwort's release CLI
  at `786a83e9`; Lean 4.34.1 from nixpkgs). The programs are scratch files, not committed;
  each is quoted where it's used;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [0. Summary](#0-summary)
- [1. The problem, with our own code](#1-the-problem-with-our-own-code)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. What we ran](#3-what-we-ran)
- [4. How other languages do it](#4-how-other-languages-do-it)
- [5. Options](#5-options)
- [6. The proposal in detail (option B)](#6-the-proposal-in-detail-option-b)
- [7. Before and after](#7-before-and-after)
- [8. Staged plan](#8-staged-plan)
- [9. Critical review](#9-critical-review)
- [10. Decisions](#10-decisions)
- [Sources](#sources)

## 0. Summary

- **Today** a loop that doesn't recurse on a piece of its argument gets an extra `Nat` counter
  ("fuel") so that it does, plus a default answer for when the counter runs out. Each one
  needs a lemma that the fuel is enough and usually one that the amount doesn't matter.
  There are seven in `std` and `aoc/` ([§1.1](#11-where-fuel-is-used-today)); `Nat/Digits.sw`
  alone mentions fuel 64 times.
- **Elsewhere** ([§4](#4-how-other-languages-do-it)): Lean (`termination_by`) builds the
  function from a proof that `<` has no infinite descending chains. Such functions don't
  compute in the kernel: `example : digits 1234 = [1, 2, 3, 4] := by rfl` fails, and so does
  `by decide` **[run]**. Since Lean 4.9 they are `@[irreducible]` by default [L2]. Rocq's
  `Program Fixpoint` needs the function-extensionality axiom to unfold [C2]; Equations uses it
  too [C3]. Agda's sized types are not allowed with `--safe` because of known soundness bugs
  [A2]. Dafny and F\* check `decreases` with an SMT solver; Dafny's verifier itself unrolls
  recursive functions with a fuel counter [D2].
- **Stitchwort is unusual in one way that decides this:** tests are checked by the kernel's own
  evaluator (`docs/core.md`, "Arguments are computed only when a type needs them": in
  `test "t" = f x == y`, "`f x` is computed when the test is checked as well as when it
  runs") **[checked]**. So whatever we choose must compute in the kernel, quickly. That rules
  out Lean's design (option A) for us.
- **Recommended: option B** ([§6](#6-the-proposal-in-detail-option-b)). `decreasing m` is
  compiled by the elaborator into fuel that carries a proof `m x < fuel`, so the
  out-of-fuel branch is impossible rather than a default. The kernel sees only structural
  recursion. Tests compute: the fuel is a native number, so `Nat.digits` of a 30-digit number
  takes 30 steps **[run]**. The compiler generates `f.unfold` (the definition's own equation,
  with `f` in place of the fuelled helper) and its proof. `stitchwort run` and `--js` erase
  the fuel. Proofs about `f` use `decreasing` too: a theorem can recurse on the same measure,
  which is functional induction without a new principle.
- **Not covered by stage 1:** a recursive call under a lambda (day 2's `weightFuel` passes
  `d => weightFuel f False d` to a sum), which needs Lean-style "attach" support; mutual
  groups; measures that aren't one `Nat`. They stay on fuel until a later stage.
- **Decisions** ([§10](#10-decisions)): D473 adopt B; D474 the syntax; D475 where a
  termination argument may live in AoC programs.

## 1. The problem, with our own code

### 1.1 Where fuel is used today

| Where | Function | What the fuel stands for | Lemmas it costs |
|---|---|---|---|
| `crates/elab/src/std/core.sw:345` | `Nat.divFuel` (`/`, `%`) | `n` steps are enough when `d != 0` | `Nat.divFuelLe`, `Nat.divFuelBound`, their `Step` helpers and `Nat.fuelSub` (`Nat/Arith.sw:99-134`, 36 lines). Runs natively (`docs/core.md`, Numbers) |
| `crates/elab/src/std/core.sw:546` | `Nat.digitsOnto` (characters, for `Nat.toText`) | `n + 1` | none needed so far |
| `crates/elab/src/std/Nat/Digits.sw:7` | `Nat.digitsFuel` (`Nat.digits`) | `n + 1` | `digitsFuelSmall`, `digitsFuelBig`, `digitsFuelIndep` (the fuel doesn't matter), and an `n < f` hypothesis plus `Nat.leTrans` glue in six more (`Digits.sw:45-201`) |
| `crates/elab/src/std/List/Toolkit.sw:738` | `List.chunksOfFuel` | one unit per element | none proved yet |
| `crates/elab/src/std/List/Toolkit.sw:222` | `List.transposeN` | the number of columns | none; see below |
| `aoc/src/Aoc/Day02/Day02.sw:61` | `weightFuel` | `n + 1`, recursion on divisors, *through a lambda* | in `Day02/Proofs/Part2.sw` (15 mentions) |
| `aoc/src/Aoc/Day04/Day04.sw:123` | `settleMarked` | the number of rolls | `settleEnds` (`Proofs/Part2.sw:124`), using `fewerRolls` |

**[checked]**, by `grep -rn -i fuel crates/elab/src/std aoc` (122 lines in 8 files).

`List.transposeN` is not really fuel: its counter is the number of columns, which is what the
function means, and it recurses structurally on it. `decreasing` wouldn't make it simpler, so
I leave it out of the migration. The same goes for day 4's `rounds grid fuel s` in the spec
(`Proofs/Core.sw:241`): the spec is about a number of rounds.

### 1.2 What fuel costs

Take `Nat.digits` (`Nat/Digits.sw:7-12`) **[checked]**:

```
def Nat.digitsFuel: Nat -> Nat -> List Nat -> List Nat
  | Zero,      n, acc => Cons n acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then Cons n acc else Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc)

def Nat.digits (n: Nat): List Nat := Nat.digitsFuel (Succ n) n Nil
```

Three things are wrong with it, none of them fatal:

1. **A made-up answer.** `| Zero, n, acc => Cons n acc` never happens with fuel `n + 1`, but
   it has to say something. A reader has to work out that it's unreachable.
2. **Lemmas that are only about the fuel.** To prove anything, you first prove that the
   amount of fuel doesn't matter (`Nat.digitsFuelIndep`, `Digits.sw:120`, 9 lines) and
   restate the two steps of the definition (`digitsFuelSmall`, `digitsFuelBig`). Every
   other lemma carries `n < f` and threads `Nat.leTrans (Succ (n / 10)) n f (Nat.divTenLess n
   b) h` through its recursive call.
3. **Statements about the helper, not the function.** `Nat.digitsDigits` is proved through
   `Nat.digitsFuelDigits f n acc`, then specialised to `f = Succ n`.

Day 4 shows the same at the scale of a puzzle. `settleMarked` sweeps "until a pass changes
nothing", with the number of rolls as fuel (`Day04.sw:118-127`) **[checked]**:

```
-- Sweep until a pass changes nothing. Every pass that changes something
-- removes a roll, so as many passes as there are rolls are enough.
def Grid.settle (grid: Grid): Grid :=
  { grid | rows = Vec.map Pair.fst (settleMarked (grid.rows.map (row => (row, True))) grid.rolls) }

def settleMarked (grid: Marked w h): Nat -> Marked w h
  | Zero   => grid
  | Succ n =>
    let next := sweep grid
    if next.any Pair.snd then settleMarked next n else next
```

and `settleEnds` (`Proofs/Part2.sw:124-142`) has to carry `rollCount grid (mcells m) <= fuel`
and prove it again for the next pass with `fewerRolls`.

### 1.3 What others did on the same puzzle

From [aoc-day04-community.md §3.3](../comparisons/aoc-day04-community.md#33-part-2-until-nothing-changes)
**[checked]**: three Lean files use `termination_by` the roll count (acarapetis, tenthmascot,
kim-em); nine of the 21 proof-language files give up on totality (`partial` in four Lean and
Idris files, Agda's `TERMINATING`, Dafny's `decreases *`) or use fuel (sdiehl, BrianNormant,
0xmycf). tenthmascot's is the shortest: `if _h : new.size < old.size then repeat_cycle new else
...` with `termination_by data.1.size`. The guard *is* the termination proof. Other days show
the same split: `termination_by` in day 3 (acarapetis, Dessertion; `aoc-day03-community.md:113,117`)
and day 5 (natewhite345, bjornestol; `aoc-day05-community.md:122,426`); fuel in days 6 and 7
(kim-em, septract, sdiehl; `aoc-day06-community.md:115-117`, `aoc-day07-community.md:124-125`);
`partial` in days 3 and 6 (`aoc-day03-community.md:117`, `aoc-day06-community.md:354`)
**[checked]**.

## 2. Words this note uses

- **Structural recursion**: each recursive call is on a piece of an argument (the `xs` of
  `Cons x xs`, the `n` of `Succ n`). Stitchwort's kernel checks this with size-change
  termination (`docs/core.md`, Definitions, step 4; `crates/core/src/sct.rs`), which also
  accepts lexicographic and swapped-argument recursion **[checked]**.
- **Measure**: a number computed from the arguments that gets smaller at every recursive call.
  `n / 10 < n` for digits; the roll count for day 4.
- **Well-founded recursion**: recursion justified by a measure (more generally, by an order
  with no infinite descending chains) instead of by structure.
- **Fuel**: an extra `Nat` argument the function recurses on structurally, set high enough by
  the caller.
- **Obligation**: the fact that has to be proved at each recursive call, here `m(new
  arguments) < m(old arguments)`.
- **Unfolding equation**: `f x = <f's body, with f in it>`. For a structural definition the
  kernel unfolds this by itself; for a well-founded one it's usually a lemma.

## 3. What we ran

### 3.1 Option B by hand in Stitchwort: `b2.sw`

What the compiler would generate for `decreasing n`, written out **[run: `stitchwort test` and
`check` pass]**:

```
-- The fuel carries its own "enough" proof, so running out is impossible.
def digitsGo: (k: Nat) -> (n: Nat) -> (acc: List Nat) -> n < k -> List Nat
  | Zero,   n, acc, h => Void.absurd (Bool.falseNotTrue h)
  | Succ k, n, acc, h => digitsStep k n acc h (Nat.leq n 9) rfl

def digitsStep (k: Nat) (n: Nat) (acc: List Nat) (h: n < Succ k): (b: Bool) -> Nat.leq n 9 = b -> List Nat
  | True,  e => Cons n acc
  | False, e => digitsGo k (n / 10) (Cons (n % 10) acc) (Nat.leTrans (Succ (n / 10)) n k (Nat.divTenLess n e) h)

def digitsOnto (n: Nat) (acc: List Nat): List Nat := digitsGo (Succ n) n acc (Nat.leRefl n)
def digits (n: Nat): List Nat := digitsOnto n Nil

test "digits 1234" := digits 1234 == [1, 2, 3, 4]
theorem byRfl: digits 1234 = [1, 2, 3, 4] := rfl
```

The `Zero` branch uses the same trick as `Fin.sw:21` (`Void.absurd (Bool.falseNotTrue h)`): `n
< 0` is `False = True`. In `b1.sw`, the same with `if big: Nat.leq n 9 = False` in place of the
helper, `List.length (digits 123456789012345678901234567890) == 30` passes as a test, and `run`
and `run --js` print 30. Checking a file took about 12 s in all my runs, the same with or
without these definitions, so the computation itself costs nothing visible.

Then the two lemmas the compiler would generate, also checked **[run]**:

```
-- The amount of fuel doesn't matter: by induction on it, mirroring the case tree.
theorem digitsGoIrrel: (k: Nat) -> (j: Nat) -> (n: Nat) -> (acc: List Nat) -> (h: n < k) -> (g: n < j) ->
    digitsGo k n acc h = digitsGo j n acc g
  | Zero,   j,      n, acc, h, g => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, Zero,   n, acc, h, g => Void.exfalso (Bool.falseNotTrue g)
  | Succ k, Succ j, n, acc, h, g => digitsStepIrrel k j n acc h g (Nat.leq n 9) rfl

theorem digitsStepIrrel (k: Nat) (j: Nat) (n: Nat) (acc: List Nat) (h: n < Succ k) (g: n < Succ j):
    (b: Bool) -> (e: Nat.leq n 9 = b) -> digitsStep k n acc h b e = digitsStep j n acc g b e
  | True,  e => rfl
  | False, e => digitsGoIrrel k j (n / 10) (Cons (n % 10) acc) _ _

-- The unfolding equation, with digitsOnto itself in the recursive call.
theorem digitsOntoUnfold (n: Nat) (acc: List Nat):
    digitsOnto n acc = Bool.ifThenElse (Nat.leq n 9) (u => Cons n acc) (u => digitsOnto (n / 10) (Cons (n % 10) acc)) :=
  digitsUnfoldStep n acc (Nat.leq n 9) rfl

theorem digitsUnfoldStep (n: Nat) (acc: List Nat): (b: Bool) -> (e: Nat.leq n 9 = b) ->
    digitsStep n n acc (Nat.leRefl n) b e = Bool.ifThenElse b (u => Cons n acc) (u => digitsOnto (n / 10) (Cons (n % 10) acc))
  | True,  e => rfl
  | False, e => digitsGoIrrel n (Succ (n / 10)) (n / 10) (Cons (n % 10) acc) _ (Nat.leRefl (n / 10))

theorem digitsUnfoldUse (n: Nat) (acc: List Nat):
    digitsOnto n acc = (if Nat.leq n 9 then Cons n acc else digitsOnto (n / 10) (Cons (n % 10) acc)) := digitsOntoUnfold n acc
```

What this shows:

- **The kernel needs nothing new.** `digitsGo` is structural on `k`.
- **The two generated proofs are mechanical**: the irrelevance lemma follows the case tree
  with the same splits; the unfolding lemma is one step plus irrelevance. No function
  extensionality is used.
- **One trap, found on the way.** My first try wrote the irrelevance proof with `match e:
  Nat.leq n 9 with` and got `E-MATCH-MOTIVE` ("generalising this `match`'s scrutinee makes its
  type ill-formed"), because the definition's proof term `Nat.divTenLess n big` mentions the
  scrutinee. Generating the step as a helper over `(b, e)`, as above, avoids it. The
  generator must do the same; a user writing these proofs by hand would hit it.
- **On an open `n`, `digitsOnto n acc` unfolds one level by itself** (`digitsOntoEq: digitsOnto
  n acc = digitsStep n n acc (Nat.leRefl n) (Nat.leq n 9) rfl := rfl` checks), because the
  fuel `Succ n` matches `Succ`. The helper's name then shows up in goals. [§6.4](#64-what-the-checker-shows-folding)
  says how to keep `digitsOnto n acc` folded.

### 3.2 Option A in Stitchwort: `a1.sw`, `a2.sw`

Accessibility, the textbook basis of well-founded recursion (Lean's `Acc`, Agda's `Acc`), for
`<` on `Nat`:

```
type AccLt: Nat -> Prop =
  | AccIntro [n: Nat] (below: (m: Nat) -> m < n -> AccLt m): AccLt n
```

- As a `Prop`, matching on it to build a `List Nat` is refused **[run]**: `E-PROP-ELIM`, "Matching
  on one can only produce data when the proposition has at most one constructor and every
  field is itself a proof." The implicit `n` is data. Lean allows this case (fields that
  appear in the indices) [inferred from Lean's `Acc.rec` eliminating into any `Sort`]; we'd
  need a kernel change to the elimination rule.
- As a `Type` (`a2.sw`), with `if e: Nat.leq n 9 = False` in the body, it checks, the test
  passes, `rfl` proves `digits 1234 = [1, 2, 3, 4]`, and `run --reference` and `run --js` print
  30 **[run]**. With an inner `match e:` instead of `if` it's refused (`E-TERMINATION`):
  the lifted `match` receives `below` as an ordinary argument, and the termination checker
  only trusts a recursive function field bound by the match itself **[run]**.
- **But** `stitchwort run` (the fast runtime) took 23 s for a 6-digit number, 32 s for 8 digits
  and didn't finish in 150 s for 13 digits, where checking alone takes about 12 s **[run]**.
  `run --reference` on 30 digits took 15 s in all. I haven't looked for the cause (my guess,
  **[unverified]**: something in `crates/rt` that is linear in the number, such as an erased
  proof being computed). It's a side finding for a separate ticket, not an argument either way.

### 3.3 Lean: `Digits.lean`

```
def digitsOnto (n : Nat) (acc : List Nat) : List Nat :=
  if h : n ≤ 9 then n :: acc else digitsOnto (n / 10) (n % 10 :: acc)
termination_by n
decreasing_by omega
def digits (n : Nat) : List Nat := digitsOnto n []
```

**[run, Lean 4.34.1]**:

| Check of `digits 1234 = [1, 2, 3, 4]` | Result |
|---|---|
| `#eval digits 1234` (compiled code) | `[1, 2, 3, 4]` |
| `by rfl` | fails: "The left-hand side `digits 1234` is not definitionally equal to the right-hand side" |
| `by decide` | fails: "its `Decidable` instance … did not reduce to `isTrue` or `isFalse`" |
| `unseal digitsOnto in … by rfl` | passes |
| `by simp [digits, digitsOnto]` | passes (rewrites with the equation lemmas) |
| `by native_decide` | passes (trusts the compiler) |

and Lean generated, unasked:

```
digitsOnto.eq_1 : ∀ (n : Nat) (acc : List Nat),
  digitsOnto n acc = if h : n ≤ 9 then n :: acc else digitsOnto (n / 10) (n % 10 :: acc)
digitsOnto.induct : ∀ (motive : Nat → List Nat → Prop),
  (∀ (n : Nat) (acc : List Nat), n ≤ 9 → motive n acc) →
    (∀ (n : Nat) (acc : List Nat), ¬n ≤ 9 → motive (n / 10) (n % 10 :: acc) → motive n acc) →
      ∀ (n : Nat) (acc : List Nat), motive n acc
'digitsOnto.eq_1' depends on axioms: [propext, Quot.sound]
```

So a Lean user gets the equation and an induction principle for free, but a test by `rfl` or
`decide` doesn't work without `unseal`. `Quot.sound` is where Lean's function extensionality
comes from **[inferred]**; Stitchwort has no function extensionality (`docs/proposals/calc-rewrite.md:182`)
**[checked]**, so we can't copy Lean's proof of `eq_1`, but §3.1 shows we don't need to.

## 4. How other languages do it

### 4.1 Summary

| System | How you say it | What the kernel sees | Computes in the kernel? | Unfolding lemma | Induction |
|---|---|---|---|---|---|
| Lean 4 | `termination_by m`, `decreasing_by tactic` | `WellFounded.fix` over `Acc` | badly; irreducible by default since 4.9 [L2] | `f.eq_1`, `f.eq_def` generated [run] | `f.induct`, `fun_induction` [L3] |
| Rocq `Program Fixpoint` | `{measure m}` | `Fix_sub` over `Acc` | only if obligations are transparent [C1] | `fix_sub_eq_ext`, needs function extensionality [C2] | by hand |
| Rocq Equations | `by wf m` | `Acc`-based | opaque by default, on purpose [C3] | generated; uses function extensionality [C4] | `funelim` [C4] |
| Rocq `Function` | `{measure m}` | `Acc`-based | [unverified] | generated | `f_ind`, functional induction [unverified] |
| Agda | sized types, or `Acc` from the library, or Bove–Capretta | sizes / `Acc` | sizes: yes; `Acc`: when the proof reduces [unverified] | clauses are the definition | ordinary recursion |
| Idris 2 | `assert_smaller`, `assert_total` | trusts the assertion | yes | n/a | n/a |
| F\* | `decreases m` | SMT-checked obligation | the normaliser unfolds [unverified] | n/a | ordinary recursion |
| Dafny | `decreases m` | SMT-checked obligation | n/a (verifier unrolls with fuel [D2]) | n/a | ordinary recursion |

### 4.2 Lean 4

- **What it is.** "By default, a `termination_by` clause will cause the function to be
  constructed using well-founded recursion" [L1]. The obligations are discharged by
  `decreasing_tactic`, or by your own: "Use `decreasing_by` to specify your own tactic for
  discharging this kind of goal" [L1] **[checked]**.
- **It doesn't compute well.** "Applications of functions defined via well-founded recursion
  are not necessarily definitionally equal to their return values"; "Even when the reduction
  behavior happens to hold definitionally, it is often much slower than structurally
  recursive definitions in the kernel"; "using these functions in types typically does not
  work well" [L1] **[checked]**. Since 4.9.0 (#4061) "functions defined by well-founded
  recursion are marked with `@[irreducible]` by default", "to prevent the expensive and often
  unfruitful unfolding"; to get the old behaviour, "`unseal f in`" or "`@[semireducible]`" [L2]
  **[checked]**. §3.3 shows the effect.
- **"The reductions do hold as propositional equalities, however, and Lean automatically
  proves them"** [L1]: the `eq_N` lemmas.
- **Compiled code doesn't go through the proof.** "The compiler generates code from these
  provisional definitions" [L1], i.e. the recursive definition as written, before it's
  turned into `WellFounded.fix` **[checked; that "provisional definitions" means the
  pre-`fix` form is my reading]**. This is what §6.5 proposes for our runtimes.
- **Higher-order calls.** A recursive call inside `xs.map (fun y => f y)` has no proof that
  `y` is smaller. Lean now rewrites `xs.map` to `xs.attach.map`, which hands each element
  over with a proof that it's in `xs` ("auto-attach", Lean 4.18, PR #6744) [L4]; the
  reference calls the mechanism `wfParam` preprocessing and notes it "requires special setup
  for the higher-order function" [L1] **[checked]**.
- **Functional induction** ("functional induction principle tailored to proofs about that
  function", Lean 4.8) [L3] **[checked]**; §3.3 shows `digitsOnto.induct`.

### 4.3 Rocq: `Program Fixpoint`, Equations, `Function`

- `Program Fixpoint f … {measure m}`: "The `measure f R` and `wf R x` annotations add an
  implicit argument to the functions being defined" [C1] **[checked]**. The unfolding
  equation `fix_sub_eq_ext` lives in `WfExtensionality`: "This module provides the fixpoint
  equation provided one assumes functional extensionality" [C2] **[checked]**. The plain
  `fix_sub_eq` instead takes an explicit hypothesis that the body respects pointwise-equal
  recursive calls [C2] **[checked]**. That hypothesis is exactly our irrelevance lemma, stated
  for an arbitrary body.
- Equations: "Functions defined using Equations cannot be unfolded with unfold nor simplified
  with simpl or cbn. This is on purpose to prevent uncontrolled unfolding which can easily
  happen, particularly when doing well-founded recursion" [C3] **[checked]**. It generates the
  unfolding lemma and the elimination principle (`funelim`) [C4], and "uses FE to prove the
  unfolding equation" for well-founded definitions [C5] **[checked: a forum post]**. "Mutual
  well-founded definitions are not supported" in its `by wf` form [C6] **[checked: a forum
  post, may be out of date]**.

### 4.4 Agda

- **Sized types**: "Sizes help the termination checker by tracking the depth of data
  structures across definition boundaries" [A1] **[checked]**. Since Agda 2.6.2, because of
  "several known soundness issues with sized types (see #1201, #1946, #2820, #3026)", the
  `--sized-types` flag "can no longer be used while `--safe` is active" [A2] **[checked]**.
- **Accessibility** (`Induction.WellFounded` in the standard library) is the same idea as
  Lean's, without Lean's proof irrelevance; whether it computes depends on the accessibility
  proof reducing **[unverified]**.
- **Bove–Capretta** [B1]: define an inductive "domain" predicate whose constructors follow
  the function's recursive calls, and recurse structurally on a proof of it. Clean in theory;
  in practice one more type per function, and the domain proof is still a well-foundedness
  argument. `partial.md` §10.2 discusses it for promoting `{Partial}` code.

### 4.5 Idris 2

No well-founded recursion in the language; the totality checker is size-change based, and
`assert_smaller` "simply evaluates to its second argument, but also asserts to the totality
checker that `y` is structurally smaller than `x`", with `assert_total` as the last resort
("In general, this function should be avoided") [I1] **[checked]**. That's an unchecked
promise, which Stitchwort's kernel doesn't allow.

### 4.6 F\* and Dafny

- F\*: `decreases e`; "this measure strictly decreases on each recursive call", in the
  well-founded order `<<`, with lexicographic tuples `%[m; n]` and a default of all
  non-function arguments left to right [F1] **[checked]**. The obligations go to the SMT
  solver **[unverified from that page; well known]**.
- Dafny: `decreases e`, checked by the verifier; `decreases *` gives up. For proofs, the
  verifier gives each function a fuel parameter and "each recursive call receives one less
  fuel than its caller", and you can raise it with `{:fuel}` [D1, D2] **[checked: the FAQ and
  the Boogie page]**. So even Dafny bounds unfolding with fuel internally; it just hides it.

### 4.7 What to take

1. **Kernel computation is the deciding constraint for Stitchwort**, and only fuel-like
   encodings keep it (Lean: no; Rocq: no, by default; Dafny: fuel internally).
2. **Generate the unfolding equation** (Lean, Equations), so users rewrite with `f`'s own
   definition and never see the encoding.
3. **Run the definition as written** at run time (Lean's compiler).
4. **Expect the higher-order problem** (Lean's auto-attach) and plan for it separately.
5. **A guard is the cheapest termination proof** (tenthmascot's `if _h : new.size < old.size`).

## 5. Options

The criteria: soundness and what we have to trust; evaluation in the kernel and in tests;
proof ergonomics; error messages; effort.

### (A) Accessibility (Lean's `termination_by`)

Compile `decreasing m` to recursion on an `Acc` proof for `<` on `Nat`.

- **Trusted base:** an `Acc` type and its elimination rule. As a `Prop`, today's kernel
  refuses to eliminate it into data (§3.2), so the elimination rule would change. As a `Type`,
  it's ordinary data, but it's then not erased.
- **Kernel and tests:** computes only if the accessibility proof reduces to its constructor.
  Our `accLt` reduces quickly because it's a `def` on native numbers (§3.2), but any proof built
  from library theorems has to be unfolded too, and theorems are full terms the kernel must
  evaluate. Lean's experience ([§4.2](#42-lean-4)) is that this is slow and it gave up.
- **Proofs:** the unfolding equation needs proof irrelevance for `Acc` (Lean has it
  definitionally; our [proof-irrelevance.md](proof-irrelevance.md) is not built) or function
  extensionality (Rocq). Neither exists.
- **Messages:** obligations as goals; fine.
- **Effort:** large, and it touches the kernel.

### (B) A measure compiled to proof-carrying fuel (recommended)

The elaborator turns `decreasing m` into a helper that recurses structurally on a fuel `k`,
with a proof `m x < k`, and a wrapper that starts it with `k = m x + 1`.

- **Trusted base:** unchanged. Everything the kernel sees is structural recursion and proofs
  it checks. A bug in the elaborator gives a refused definition or lemma, never a wrong one.
- **Kernel and tests:** computes, at the cost of computing `m x` once per outside call and one
  native decrement per step (§3.1).
- **Proofs:** the generated `f.unfold` gives the definition's own equation; theorems can use
  `decreasing` to recurse the way the function does. No extensionality needed (§3.1).
- **Messages:** an obligation the compiler can't discharge is reported at the call, with the
  goal `m(new) < m(old)` and the hypotheses in scope (§6.3).
- **Effort:** medium: elaborator and generator (stage 1, §8), erasure in two runtimes, docs.

A variant, **B0**, keeps plain fuel with a default answer, exactly as users write today, and
only automates it. It's simpler to generate but needs an inhabited result type (there's no
default `Vec a n`), and the "fuel is enough" lemma then has to be proved per definition instead
of being impossible by construction. B with the proof is strictly better.

### (C) A kernel primitive (Dafny-like)

The kernel accepts a definition with a measure and checked obligations, and unfolds it like any
other definition.

- **Trusted base:** grows: a new kind of definition, and its interaction with the unfolding
  policy and conversion.
- **Kernel and tests:** computes. **But** the kernel unfolds a definition whenever its case tree
  can take a step (`docs/core.md`, Unfolding policy) **[checked]**, and for a well-founded
  definition that can go on forever on open terms (the measure decreases only for actual
  numbers). Type checking could loop. Dafny avoids this with fuel in the verifier [D2]; we'd end
  up adding fuel inside the kernel, which is option B in a more trusted place.
- **Proofs:** as nice as structural recursion: the definition unfolds by itself.
- **Effort:** large, in the kernel.

### (D) Sized types

Types carry a size bound; the termination checker uses it.

- **Trusted base:** a large change to the type system. Agda's version has known soundness
  problems and is not allowed with `--safe` [A2].
- **Kernel and tests:** sizes are erased; computing is fine.
- **Proofs:** sizes appear in every signature that passes through the recursion.
- **Doesn't fit our cases**: `n / 10` and "a sweep that changes something removes a roll" are
  facts about numbers, not about the depth of a data structure.
- **Effort:** very large.

### Side by side

| | A: `Acc` | B: proof-carrying fuel | C: kernel primitive | D: sized types |
|---|---|---|---|---|
| Kernel change | yes | **no** | yes | yes, large |
| `test` / `rfl` on `Nat.digits 1234` | only if proofs reduce; Lean: no | **yes** [run] | yes | yes |
| Type checking always terminates | yes | **yes** | needs care | yes |
| Unfolding equation | needs proof irrelevance or extensionality | **generated, plain proof** [run] | definitional | definitional |
| Runtime | `Acc` erased or carried | fuel erased (§6.5) | as written | as written |
| Effort | large | **medium** | large | very large |

## 6. The proposal in detail (option B)

### 6.1 What you write

```
def Nat.digitsOnto (n: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then Nat.digitsOnto (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n big]
  else Cons n acc
```

- `decreasing e` goes after the result type, before `:=` or the clauses (Dafny's place, and
  where a reader looks for the signature) (D474). `e` is a `Nat` expression over the header
  parameters. Clause-style definitions (`def f: A -> B | …`) name the parameters it uses in
  the header.
- At each recursive call, the obligation `e[new arguments] < e[parameters]` is found by `auto`
  (hypotheses in scope, then decision procedures, as for `[auto ok: d != 0]` today), or given by
  name: `[decreasing := proof]`, the same form as `[ord := descending]` (D474).
- **The guard style needs no lemma.** `if h: rolls next < rolls grid then settle next else
  next` puts `h` in scope, and `auto` finds it (§7.2). This is tenthmascot's pattern.
- `decreasing` is allowed on `theorem`s too: a proof that recurses on the same measure as
  the function is the induction a proof about it needs (§6.6).
- Structural recursion stays the default: a definition the termination checker already accepts
  doesn't need `decreasing`, and gets a note saying so if it has one.

### 6.2 What the compiler generates

For `def f (x: A): B decreasing m x := body` (more parameters work the same way):

1. **`f.go: (k: Nat) -> (x: A) -> m x < k -> B`**, structural on `k`. The `Zero` case is
   `Void.absurd` of the proof (`m x < 0` is `False = True`). The `Succ k` case is `body`, with
   each recursive call `f y [decreasing := p]` replaced by `f.go k y q`, where `q: m y < k`
   comes from `p: m y < m x` and the parameter `h: m x < Succ k` by `Nat.leTrans` (§3.1). Any
   `match` or `if` whose scrutinee a proof in the body mentions is generated as a helper over
   `(b, e)` (§3.1's trap).
2. **`f (x: A): B := f.go (Succ (m x)) x (Nat.leRefl (m x))`**, the name users see.
3. **`f.go.irrel`**: two fuels give the same result, by induction on the fuels following the case
   tree (`digitsGoIrrel`).
4. **`f.unfold: (x: A) -> f x = body`**, with `f` itself in the recursive calls, and the body's
   inner `match`es as their own named helpers, which call `f` and so are no longer recursive.
   This is Lean's `f.eq_def`; [equation-lemmas.md](equation-lemmas.md) §6(b) found it "not
   viable" for ordinary definitions because a `match` in the statement would be a new helper;
   here the compiler makes the helper once and the statement uses that one. Per-leaf lemmas
   (`f.eq_1`, … , D231) are not part of stage 1.

The kernel checks all four as ordinary declarations: `go` and `irrel` are a structural group;
`f`, the helpers and `unfold` come after. Nothing is trusted that isn't checked
**[inferred from §3.1]**.

### 6.3 Errors

- **Obligation not found:** reported at the call, with the goal and what's in scope:
  "can't show `n / 10 < n` here, which `decreasing n` needs for this call. In scope: `big:
  Nat.leq n 9 = False`. Give a proof with `[decreasing := …]`, or test it with `if h: n / 10 <
  n then …`." This is better than today's `E-TERMINATION` for a non-structural call, which can
  only say "no argument is known to be smaller" (§3.2's message).
- **Measure not a `Nat`, or mentions a non-parameter:** at the `decreasing` clause.
- **A recursive call under a lambda** (`List.map (y => f y) xs`, day 2's `d => weightFuel f
  False d`): stage 1 refuses it, saying the call has no proof that `y` is smaller and suggesting
  fuel for now (§8, stage 3). An `if`'s branches don't count as lambdas here.
- **Generator failure** (a shape the irrelevance proof doesn't cover): an internal error naming
  the definition. The kernel would refuse a wrong proof, so this is a usability bug, never a
  soundness one.

### 6.4 What the checker shows (folding)

As §3.1 showed, `f x` with an open `x` unfolds one level by itself, because the fuel is `Succ (m
x)`, and goals would then show `f.go (m x) …`. Requirement: **`f x` stays folded unless `m x`
computes to a number.** The natural way is a case on the measure inside the wrapper, so its
case tree is stuck on an open measure, as any definition's is (`docs/core.md`, "unfolds only if
its case tree can take a step"). If that encoding turns out awkward, a flag like the dictionaries'
`Def::fold` (which "doesn't change what's equal, only when it's computed") is the fallback. Either
way the goal shows `f x`, and `rewrite f.unfold` takes one step.

### 6.5 Tests, the fast runtime and JS

| Where | What runs | Fuel |
|---|---|---|
| `stitchwort check` (types that compute, `rfl`) | the kernel's evaluator | kept: `m x` once, then one native `Succ` match per call |
| `stitchwort test` | the kernel's evaluator, with erasure (`docs/core.md`, Running a program) | kept, as above; the proofs are erased already |
| `stitchwort run` (`crates/rt`) | erased IR | **dropped**: `f.go`'s fuel parameter is marked, erased like a proof, and its `Zero` case is unreachable; `m x` is never computed |
| `run --js`, `build --js` | erased JS | **dropped**, the same way |

Dropping the fuel is safe because `f.unfold`, checked by the kernel, says `f` satisfies its
written equation, and the kernel has accepted the termination argument, so running the written
recursion gives the same answer. The runtimes are already untrusted (`docs/core.md`: "Its output
can be wrong, but a proof never depends on it") and differential-tested against the reference
evaluator; the new examples join those tests. Natives: `Nat.divFuel` stays native and unchanged
until `/` itself moves (§8).

### 6.6 Proofs about such a function

Two tools, no new principle:

- **`f.unfold`**, to take one step of `f` in a proof.
- **`decreasing` on the theorem**, so the proof calls itself on the smaller arguments, the same
  calls the function makes. For digits [inferred; not run]:

```
theorem Nat.digitsOntoDigits (n: Nat) (acc: List Nat) (ha: Nat.Digits acc): Nat.Digits (Nat.digitsOnto n acc)
  decreasing n
:=
  rewrite Nat.digitsOnto.unfold n acc in
  match e: Nat.leq n 9 with
    | True  => Both (Nat.digitBound n e) ha
    | False => Nat.digitsOntoDigits (n / 10) (Cons (n % 10) acc) (Both (Nat.modLt n 10) ha)
                 [decreasing := Nat.divTenLess n e]
```

(`Nat.digitBound`, `n < 10` from `Nat.leq n 9 = True`, is a placeholder name.) Compared with
`Nat.digitsFuelDigits` today: no `f`, no `n < f`, no `Nat.leTrans` glue, and no
`digitsFuelSmall`/`Big`/`Indep`. A generated per-branch `f.induct` like Lean's (§3.3) is left
for later (§8, stage 3), when a proof wants it.

### 6.7 How it interacts with the rest

- **Termination checking (`docs/core.md`, Definitions step 4):** unchanged. `f.go` passes it
  because the fuel shrinks; the user's measure is checked by the obligations instead.
- **Equation lemmas, stages 1 and 2 (D226 to D230, built):** the helpers that `f.go` and
  `f.unfold` lift from inner `match`es follow D228's capture order, and messages about them
  get D229's note. Stage 1 here builds a narrow D231: one generated `f.unfold` per `decreasing`
  definition, which is needed because, unlike an ordinary definition, `f x` no longer unfolds
  by itself on open arguments.
- **Erasure:** a new erased kind (fuel), next to proofs and types.
- **Hashes:** a definition that moves from fuel to `decreasing` changes hash, as do its users.
  Not a goal to avoid; the migration oracle (only the moved definitions and their users change)
  still applies.
- **`{Partial}`** stays for code that may really not end; `decreasing` is for code that does.

## 7. Before and after

### 7.1 `Nat.digits`

Before (`Nat/Digits.sw:7-12`, plus lemmas at 45-62 and 112-201 that carry the fuel) **[checked]**:

```
def Nat.digitsFuel: Nat -> Nat -> List Nat -> List Nat
  | Zero,      n, acc => Cons n acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then Cons n acc else Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc)

def Nat.digits (n: Nat): List Nat := Nat.digitsFuel (Succ n) n Nil
```

After:

```
def Nat.digitsOnto (n: Nat) (acc: List Nat): List Nat
  decreasing n
:=
  if big: Nat.leq n 9 = False
  then Nat.digitsOnto (n / 10) (Cons (n % 10) acc) [decreasing := Nat.divTenLess n big]
  else Cons n acc

def Nat.digits (n: Nat): List Nat := Nat.digitsOnto n Nil
```

`test "digits" := Nat.digits 1234 == [1, 2, 3, 4]` runs as it does today (§3.1). Lemmas that go:
`digitsFuelSmall`, `digitsFuelBig`, `digitsFuelIndep` (replaced by the generated
`Nat.digitsOnto.unfold`); the rest lose their fuel parameter and its glue. The same for the
character version in `core.sw:546`, which `Nat.toText` uses.

### 7.2 Day 4's `settle`

Before: §1.2. After, guard style, so the program needs no lemma (`rolls` of a marked grid is
the `sumBy` that `Grid.rolls` already does):

```
-- Sweep until a pass removes no roll.
def Grid.settle (grid: Grid): Grid :=
  { grid | rows = Vec.map Pair.fst (settleMarked (grid.rows.map (row => (row, True)))) }

def settleMarked (grid: Marked w h): Marked w h
  decreasing markedRolls grid
:=
  let next := sweep grid
  if markedRolls next < markedRolls grid then settleMarked next else next
```

The obligation `markedRolls next < markedRolls grid` is the `if`'s hypothesis, found by `auto`.
The cost is one count of the grid per pass, the same order of work as the sweep itself
**[inferred]**. The proof changes shape [inferred; not run]: `settleEnds` loses its fuel and the
`rollCount … <= fuel` hypothesis and recurses with `decreasing`; `fewerRolls` is no longer
needed for termination, but the stop case now needs "a pass that removes nothing leaves the
grid stable", which the proofs already have the parts for (`countEqSame`, `sameMarks`,
`settledStable` in `Proofs/Part2.sw` and `Proofs/Sweep.sw`).

The alternative keeps today's stop test (`next.any Pair.snd`) and proves the decrease in the
program: `[decreasing := fewerRolls …]`. But `fewerRolls` needs `Keeps grid s0 (mcells m)`
(`Proofs/Part2.sw:114`), an invariant the program doesn't have, and the parts of `Sweep.sw`
behind it, so a large piece of the proof would move into the program file. That's D475.

### 7.3 `List.chunksOf`

```
def List.chunksOf (xs: List a) (n: Nat): List (List a)
  decreasing List.length xs
:=
  match xs with
    | Nil       => Nil
    | Cons x ys =>
      let k := if n == 0 then List.length xs else n
      Cons (List.take k xs) (List.chunksOf (List.drop k xs) n [decreasing := List.dropConsLess …])
```

needs one lemma (dropping at least one element of a non-empty list makes it shorter) where
today it needs none proved yet [inferred; the lemma name is a placeholder].

### 7.4 What stays on fuel after stage 1

- **Day 2's `weightFuel`**: the recursive call is `d => weightFuel f False d` passed to
  `divisorWeights`, which doesn't say that `d < n`. It needs `divisorWeights` to pass a proof to
  its callback (`(d: Nat) -> d < m -> Nat`), as Lean's `attach` does. Stage 3.
- **`Nat.divFuel`**: native, with its lemmas written. Moving it gains little; stage 3 at most.

## 8. Staged plan

**Stage 1: `decreasing` for single definitions and theorems (elaborator, erasure; medium).**

- Parse `decreasing e` and `[decreasing := p]` (D474).
- Elaborate to `f.go` / `f` / `f.go.irrel` / `f.unfold` (§6.2), with the wrapper folded on open
  measures (§6.4); obligations by `auto` or by name; messages of §6.3.
- Mark the fuel parameter erased; drop it in `crates/core/src/erase.rs`, `crates/rt` lowering and
  JS extraction (§6.5).
- Docs: `docs/syntax.md` (the clause), `docs/core.md` (Definitions: what `decreasing` elaborates
  to; Evaluation: erased fuel).
- Acceptance: `examples/accept/` with §3.1's digits and §7.2's guard shape, including `test`s
  and an `rfl` theorem on a closed value, and a theorem using `f.unfold` and `decreasing`;
  `examples/reject/` snapshots for a missing obligation, a call under a lambda, and a measure
  that isn't a `Nat`; the differential runtime tests include the new examples; a goal on an open
  argument prints `f x`, not `f.go`.

**Stage 2: migrate (mechanical; one lane for `std`, one for `aoc/`).**

- `Nat.digits` and `Nat/Digits.sw`'s lemmas; `Nat.digitsOnto` in `core.sw`; `List.chunksOf`.
- Day 4's `settle` and its proofs, per D475.
- Add the library loops D423 deferred (`List.unfold`, iterate-until-stable) with `decreasing`.
- Acceptance: no fuel left in those files; `stitchwort check` and the tests of `std` and `aoc`
  pass; the hash-change test shows only the moved definitions and their users.

**Stage 3: later, each on its own trigger.**

- Calls under lambdas (Lean's attach) when day 2's shape comes up again.
- A generated per-branch `f.induct` when proofs by `decreasing` theorems repeat boilerplate.
- Mutual groups with `decreasing`; lexicographic measures (pairs).
- `Nat.div` via `decreasing`, if the native's registration can move with it.

## 9. Critical review

Written as an adversarial pass over draft 1; each point says what I changed or why not.

1. **"Proof-carrying fuel is `Acc` on `Nat` in disguise."** Yes, with the difference that matters
   here: the evidence is a number the kernel already computes natively, not a proof term. Kept.
2. **"The generator is a large new piece of the elaborator."** True: two proof generators
   (irrelevance, unfold) that must follow every case-tree shape. §3.1 found one trap on the
   first try (`E-MATCH-MOTIVE`). Mitigation: stage 1 refuses shapes it doesn't cover (calls under
   lambdas), and failures are refusals, never unsoundness. Effort is the main risk; stage 1 is
   priced as medium, not small.
3. **"Folding on open terms isn't solved."** Correct: §6.4 states the requirement and two ways,
   but neither was tried. Added to stage 1's acceptance.
4. **"Computing the measure in the kernel can be expensive."** `m x` is computed once per
   outside call. A measure like `List.length` on a large list in a test costs one pass, which the
   test pays anyway. Not changed.
5. **"Day 4's after doesn't keep the program's stop test."** The guard version stops on "no roll
   removed" rather than "no row marked". The answers are the same, since a pass that marks no row
   removes no roll and vice versa [inferred from `fewerRolls` and `sameMarks`], but the proof
   changes. Recorded as D475 instead of hidden.
6. **"Programs plain" (the AoC layout) is in tension with obligations in program files.** Real.
   The guard style keeps programs lemma-free; D475 asks Matt.
7. **"Isn't C simpler for users?"** Its proofs are nicer (no `unfold` lemma), but the kernel
   would have to bound unfolding on open terms itself, which reintroduces fuel in the trusted
   part. Not changed.
8. **"Day 2 is a motivating example and stage 1 doesn't fix it."** True; stated in §0 and §7.4.
9. **"Lean's `induct` is better than recursion in theorems."** It names the cases for you; ours
   makes you split them the way the function does. Generated `induct` is stage 3, on evidence.
10. **"The `stitchwort run` slowdown in §3.2 might also hit B."** B's `stitchwort run` printed 30
    at once for a 30-digit number [run], so no; the `Acc`-as-data slowdown needs its own ticket.

## 10. Decisions

- **D473. Adopt option B**: `decreasing <Nat measure>` compiled by the elaborator to
  proof-carrying fuel, with a generated `f.unfold`, fuel erased by `stitchwort run` and JS, and
  the kernel unchanged; build stages 1 and 2 of §8; stage 3 items only on their triggers.
  [yes]
- **D474. Syntax**: `decreasing e` after the result type, before `:=` or the clauses; per-call
  evidence as the named argument `[decreasing := proof]`, otherwise found by `auto`; also
  allowed on `theorem`s. (Lean writes `termination_by e` after the body and `decreasing_by
  tactic`; Dafny and F\* write `decreases e` in the signature.) [yes: Dafny's place, our
  named-argument form]
- **D475. AoC programs and termination arguments**: prefer the guard style (`if h: m next < m
  x then … else …`), which needs no lemma in the program; when a guard would change what the
  program means or costs too much, allow the decrease lemma in the program file, as an
  exception to "programs plain, theorems in `Proofs/`". [yes; day 4 uses the guard]

## Sources

- [L1] Lean language reference, Recursive definitions (well-founded recursion, `termination_by`,
  `decreasing_by`, preprocessing):
  https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/
- [L2] Lean 4.9.0 release notes, #4061:
  https://lean-lang.org/doc/reference/latest/releases/v4.9.0/
- [L3] Lean `FunInd` (functional induction), and Lean 4.8.0 release notes:
  https://eshelyaron.com/man/lean4/Lean/Meta/Tactic/FunInd.html,
  https://lean-lang.org/blog/2024-6-1-lean-480 (now redirected; not read)
- [L4] Joachim Breitner, "Extrinsic termination proofs for well-founded recursion in Lean":
  https://www.joachim-breitner.de/blog/816-Extrinsic_termination_proofs_for_well-founded_recursion_in_Lean
- [C1] Rocq reference manual, Program: https://rocq-prover.org/doc/master/refman/addendum/program.html
- [C2] Rocq stdlib, `WfExtensionality`:
  https://docs.rocq-prover.org/master/stdlib/Stdlib.Program.WfExtensionality.html
- [C3] Equations tutorial, basics: https://coq.inria.fr/platform-docs/Tutorial_Equations_basics.html
- [C4] Equations tutorial, well-founded recursion:
  https://coq.inria.fr/platform-docs/Tutorial_Equations_wf.html
- [C5] "Equations and FE", Rocq discourse: https://discourse.rocq-prover.org/t/equations-and-fe/127
- [C6] "Mutual recursion with function unfolding", Rocq discourse:
  https://discourse.rocq-prover.org/t/mutual-recursion-with-function-unfolding/869
- [A1] Agda documentation, sized types: https://agda.readthedocs.io/en/latest/language/sized-types.html
- [A2] Agda 2.6.2 release notes:
  https://hackage-content.haskell.org/package/Agda-2.6.2.0.20211129/candidate/src/doc/release-notes/2.6.2.md
- [B1] Ana Bove and Venanzio Capretta, "Modelling general recursion in type theory",
  Mathematical Structures in Computer Science 15(4), 2005 (cited, not re-read).
- [I1] Idris 2 tutorial, Theorem proving: https://idris2.readthedocs.io/en/latest/tutorial/theorems.html
- [F1] F\* tutorial, termination: https://fstar-lang.org/tutorial/book/part1/part1_termination.html
- [D1] Dafny FAQ, function unrolling: https://dafny.org/dafny/HowToFAQ/FAQFunctionUnroll
- [D2] Dafny compilation to Boogie: https://dafny.org/dafny/Compilation/Boogie
- Stitchwort: `docs/core.md`; `docs/proposals/equation-lemmas.md`; `docs/proposals/partial.md`;
  `docs/proposals/fast-runtime.md`; `docs/comparisons/aoc-day0{3,4,5,6,7}-community.md`; the
  files in §1.1.
