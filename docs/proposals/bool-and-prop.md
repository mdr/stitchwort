# Bool and Prop: where a decidable fact lives (SW-2692)

**Status:** draft 1, 10 November 2026. Design only; nothing built. Started
under D3478. Open decisions: D3479 to D3482 ([§9](#9-questions-for-matt)).
Code was read at `1a8d531aa`. Migration cost is not counted (D2303).

How claims are marked:

- **[measured]**: run today with the release CLI, on the probe files in
  [bool-and-prop/](bool-and-prop/), or counted with `grep` at that commit.
  Counts of theorems look at one-line statements only, so they undercount.
- **[checked]**: read in the code or a note, at the file and line given.
- **[cited]**: read today at the link given ([Sources](#sources)).
- **[memory]**: prior art recalled, not re-read today.
- **[inferred]**: my reasoning; not run and not cited.

## 1. The problem

A fact like "`a` is at most `b`" or "`key` is in the set" can be written two
ways.

- **As a test**: a function that computes `True` or `False`
  (`Nat.leq a b`, `set.contains key`). A program can branch on it. The fact
  is then "the test gives `True`".
- **As a proposition**: a type whose values are proofs (`And p q`, an
  inductive `Le a b`). A proof can take it apart by its constructors. A
  program can branch on it only through a decision procedure.

Every proof language has both, and each has to choose which one its library
is built on, and how you get from one to the other. Stitchwort has grown
both without a rule. This shows up as:

- an `if` on a comparison and a `match` on its decision that don't refine
  each other (SW-1688);
- lemmas written twice, once as an equation between tests and once as an
  `↔` between propositions;
- `↔` lemmas that `rewrite` refuses, because there is no propositional
  extensionality;
- facts about tests that can't be taken apart by a pattern, so proofs call
  `Bool.andLeft`, `List.anyTrueElim` and `Bool.falseNotTrue` by hand;
- proofs that name the internal test (`match Nat.leq 10 value with`).

Matt's question: which world should Stitchwort prefer, as an end state?

**The short answer.** Prefer tests for what programs test, and make the
test and the proposition one term instead of two things joined by a lemma.
Keep propositions for what can't be tested. Change `Decidable` so that every
decidable proposition's `if` is its test by computation. Add no axiom.
Details in [§6](#6-recommendation).

## 2. Where Stitchwort is today

### 2.1 Three encodings, not two

Std writes a predicate in one of three ways **[measured: 106 `Prop`-valued
`def`s in std, classified by a script]**:

| Encoding | Count | Examples |
|---|---|---|
| A test equals `True` | 9 named, plus tests with no named proposition | `Nat.LessEq m n := Nat.leq m n = True` (`core/Data.sw:69`), `Int`, `Float`; `Set.contains s k = True` |
| A proposition computed by recursion on data | 49 | `List.All`, `List.Any`, so `List.Mem` (`core/ListOptionPair.sw:98-110`), `List.Sorted`, `List.Distinct`, `Map.Tree.Within` |
| A statement built from `∀`, `∃`, `∧`, `=` | 48 | `List.Perm`, `Parse.Reads`, `Graph.Shortest` |
| An inductive family | 2 | `Nat.LexLess` (`core/Division.sw:92`), `Effect.AlwaysTreeOf` |

The second row matters. `x ∈ [a, b]` is not an inductive relation: it
computes to `a = x ∨ b = x ∨ Void`. Once the list's shape is known, the
proposition has constructors to match. So Stitchwort already leans on
computation in the `Prop` world too.

By area **[measured]**:

| Area | Tests (`Bool`) | Propositions | How facts are stated |
|---|---|---|---|
| Order on `Nat`, `Int`, `Float` | `leq`, `less` | `LessEq`, `LessThan` are the test `= True` | `a ≤ b`, one term for both |
| Order on other types | `compare` | `compare x y = Less` (`core/Ord.sw:52`) | `a < b`, an equation on computed data |
| Equality | `==` is `Decidable.toBool` of a `DecEq` decision | `=` is the kernel's | both |
| Sets, maps | 7 and 12 | 0 for membership | `s.contains k = True`; `k ∈ s` already means that (measured, `computing.sw`) |
| Lists | 10 (`all`, `any`, `contains`) | 21 (`All`, `Any`, `Mem`, `Sorted`) | mixed, joined by `↔` lemmas |
| `Char`, `Text` | 9 and 10 | 0 | `c.isAsciiDigit = True` |

Theorem statements **[measured, one-line statements]**: in std 311 mention
`= True` and 154 `= False`, of 3,076; in `aoc/` 342 and 81, of 2,868.

### 2.2 What the test-backed `≤` gives

`3 ≤ 5` is `Nat.leq 3 5 = True`, which computes to `True = True`, so `rfl`
proves it. `Nat.leq` has a native implementation (`docs/core.md`,
"Numbers"), so this holds at any size. All **[measured, `computing.sw`]**:

- a 30-digit comparison by `rfl`, in 0.2 s for the whole file;
- with unknowns: `2 ≤ n + 5 := rfl`; from `h: Succ a ≤ Succ b`, `h` itself
  proves `a ≤ b`; likewise `a + 3 ≤ b + 3` gives `a ≤ b`;
- an impossible premise needs no arm: for `Succ m ≤ 0` the pattern `()` is
  accepted, since it computes to `False = True`;
- **the hypothesis is the program's test.** For `def pick … := if
  s.contains k && k ≤ 10 then 1 else 2`, the proof of `pick s k = 1` from
  `has: k ∈ s` and `small: k ≤ 10` is `rewrite has, small in rfl`.

The last point is the important one. A program's `if a ≤ b` and a
theorem's `a ≤ b` hold the same `Bool`, so a hypothesis rewrites the
program, and a `match h: a ≤ b with | True | False` refines both
(`docs/syntax.md`, "match"; `matching.rs:588`, `tested_bool`). SW-2639's
fix for `decreasing` uses this: the bound it finds by testing is already
the proof (`docs/reviews/SW-2639-decreasing-memory.md:141-150`).

Goals print the proposition, not the test **[measured]**: `h1: a ≤ b`,
`⊢ a < c`. The `False` arm of a match prints `h: (a <= b) = False`.

### 2.3 `Decidable` and the two `if`s

`Decidable p` is `Yes (proof: p) | No (refutation: ¬p)`
(`core/Decidable.sw:11`). An `if` on a proposition is `Decidable.elim` of
its decision; if no branch uses the proof it is rewritten to a plain `Bool`
test (`check.rs:5352`, `unused_proof_if`), and for the standard comparisons
that `Bool` is the comparison itself, by a special case (`bind.rs:212`).

The trouble is that a `Yes | No` decision's `Bool` is stuck until the
decision is a constructor. All three of these fail with `E-REFL`
**[measured, `stuck-today.sw`]**:

```
Decidable.toBool (Nat.decLessEq a b) = Nat.leq a b
Decidable.toBool (Decidable.and (Nat.decLessEq a b) (Nat.decLessEq c d)) = (Nat.leq a b && Nat.leq c d)
(a == b) = Nat.equal a b
```

So the two forms of `if` are different terms that no computation joins.
That is SW-1688: which form a definition's `if` takes depends on whether
its branches use the proof, and a `match` on the decision refines only one
of them (decision-match-refines-bool-if.md §1). The fix so far is a warning
(`W-MATCH-DECISION-IF`, built) and lemmas that exist only to bridge the two
forms (`Decidable.elimIf`, `Bool.elimDecTrueIf`, `core/Decidable.sw:67`, `:73`).
Three natives exist partly to make decisions compute fast with their proofs
inside (`Nat.decEq`, `Nat.equalRefl`, `Nat.equalSound`; `docs/core.md`,
"Native implementations").

### 2.4 The cost of each world, counted

**In the test world**, a fact has no constructors. `match h with | Both l r`
on `h: (a && b) = True` is a type error **[measured, `two-worlds.sw`]**. So
proofs call helpers **[measured, uses across std, aoc and rogue]**:
`Bool.falseNotTrue` 420, `Bool.andIntro` 84, `List.anyOfMem` 47,
`List.anyTrueElim` 43, `Bool.orElim` 39. And 113 `match`es are on the
internal name `Nat.leq`.

**In the proposition world**, an `↔` is a record (`Logic/Logic.sw:7`), not
an equation, so `rewrite` refuses it (`E-REWRITE-RULE`, measured,
`two-worlds.sw`). Proofs move facts across by hand: 488 uses of `.forward`
or `.backward`. `cases` can't split a variable inside `key ∈ keys`, which
is why 2024 day 21 went through `keys.contains key = True` (decide.md §2).

**Between them**, lemmas come in pairs. `Set.containsUnion` is the
equation `contains (union a b) k = (contains a k ∨ contains b k)`;
`Set.containsUnionIff` restates it as an `↔` and takes nine lines to prove
from the first (`Set/Spec.sw:230`, `:434`). Std has 27 one-line `= True ↔`
lemmas and `aoc/` 33 **[measured]**.

### 2.5 The kernel facts that bear on this

All **[checked, `docs/core.md`]**:

- `Prop` is impredicative; a proof can be matched to produce data only for
  one-constructor propositions with proof fields (`E-PROP-ELIM`, Lean's
  rule). So a two-constructor inductive `Le` can't drive a program (measured:
  `E-PROP-ELIM`).
- Proofs are compared as equal only at proof positions (constructor fields,
  proof parameters, inert arguments). Axiom K holds, so two proofs of any
  equation are provably equal.
- One axiom, `Quot.sound`. No `propext`. `J` computes only on `rfl`.
- "Computing stays the way to decide", and no `simp` (D2541).

## 3. Prior art

### 3.1 Rocq with SSReflect and MathComp: tests first

- **The rule.** "if a predicate is decidable, it should be defined through
  a boolean predicate, possibly accompanied with logical specifications".
  The reason given: "Prop and bool are truly complementary: the former
  supports robust natural deduction, the latter allows brute-force
  evaluation" **[cited: G1 §4.1]**.
- **Hiding `= true`.** `Coercion is_true (b : bool) := b = true`, and
  "Coercions are elided by the pretty-printer, so they are essentially
  transparent to the user" **[cited: G1 §4.1]**.
- **`≤` is a test.** `Definition leq m n := m - n == 0`, with `m < n` as
  notation for `m.+1 <= n`, so every inequality is one function
  **[cited: M1]**.
- **The bridge is `reflect`.** `Inductive reflect (P: Prop): bool -> Type`
  with `Reflect_true: P -> reflect P true` and `Reflect_false: ~P ->
  reflect P false`. The paper: "double implication is not the most
  efficient way to relate booleans and logical interpretations"; a case
  split on a `reflect` gives the proof and rewrites the `Bool` at once
  **[cited: G1 §4.1.4]**. `andP: reflect (b1 /\ b2) (b1 && b2)`.
- **Views.** A reflection lemma is applied while introducing or splitting
  a hypothesis (`move=> /andP [h1 h2]`), so the proposition's shape is
  there when wanted and the `Bool` otherwise **[cited: G1 §4.1.1]**.
- **Case-split lemmas** such as `leqP m n : leq_xor_gtn …` rewrite every
  comparison, `minn` and `maxn` of the two numbers in each case
  **[cited: M1]**.
- **Proofs are unique.** Proofs of `b = true` are equal, which is what
  makes records with a tested condition behave (`eq_irrelevance`)
  **[cited: G1 §4.3, §6.2]**.
- **What it costs.** Lemmas are stated as equations between `Bool`s where
  possible, and anything not decidable still lives in `Prop`; membership
  needs an `eqType` **[memory]**. Newcomers find the view syntax dense
  **[memory]**.

### 3.2 Rocq's standard library: propositions first

`le` is inductive (`le_n`, `le_S`); `Nat.leb` is a separate test, joined by
`Nat.leb_le: (n <=? m) = true <-> n <= m`; `lia` decides arithmetic
**[memory]**. Software Foundations compares the two worlds in a table:
`bool` is decidable and usable with `match`, `Prop` is neither, and "The
crucial difference between the two worlds is decidability"; "In general,
both can be useful" **[cited: SF]**. "rewrite and
reflexivity can be used with iff statements, not just equalities" **[cited:
SF]**: this is generalized (setoid) rewriting, where each connective is
registered as respecting `iff` and the tactic builds the proof, with no
axiom **[cited: S1, abstract; the mechanism from memory]**.

### 3.3 Lean 4: propositions first, with coercions both ways

- `Nat.le` is inductive (`Nat.le.refl`, `Nat.le.step`), and `<` is defined
  from it. The kernel overrides `Nat.ble`, `Nat.beq`, `Nat.blt` and
  `Nat.decEq`, among others, with GMP **[cited: L1]**. So big comparisons
  are decided through the test and carried back by a lemma.
- "There is a coercion from every `Bool` `b` to the proposition `b =
  true`", and `Decidable.decide` "is also a coercion from decidable
  propositions to `Bool`" **[cited: L2]**. `if` takes a decidable
  proposition.
- `simp` turns `Bool` facts into propositions and relies on `propext` to
  rewrite with `↔` (simp.md §4.2, **[checked]**).
- **The friction is between the worlds.** On stating `List.filter` with
  `Bool`: "It's so much hassle going between `Prop` and `Bool`" (Chris
  Hughes); "right now we aren't being consistent" (Johan Commelin); Mario
  Carneiro wanted simp lemmas that "push decide to the leaves"
  **[cited: Z1, January 2023]**.
- **`decide` gets stuck** when a `Decidable` instance doesn't reduce: built
  with a tactic (so it holds `Eq.rec`), or by well-founded recursion
  **[cited: L3, Z2]**. "there is no point providing Decidable instances
  that don't reduce" (Kim Morrison) **[cited: Z2]**.
- **A `Bool`-shaped `Decidable` was proposed for Lean** by Gabriel Ebner
  (`decide : Bool` plus a proof that it agrees), in lean4#2038; it went on
  hold because the compiler has assumptions about `Decidable` built in
  **[cited: search summary of the Zulip thread "Definition of Decidable";
  not read in full]**.

### 3.4 Agda: propositions first, moving to a `Bool` underneath

- `_≤_` is inductive (`z≤n`, `s≤s`). The decision `_≤?_` is built from the
  built-in test: `m ≤? n = map′ (≤ᵇ⇒≤ m n) ≤⇒≤ᵇ (T? (m ≤ᵇ n))`, with the
  comment "we use the builtin function `_<ᵇ_` here so that the function
  quickly decides whether to return `yes` or `no`. It still takes a linear
  amount of time to generate the proof if it is inspected" **[cited: A1]**.
- **`Dec` was redesigned as a record**: `does : Bool` and `proof : Reflects
  P does`. The reason is exactly §2.3's problem: with `yes | no`, "this
  equality does not hold definitionally, because we always do a case
  split"; so "we can return the `does` part separately, before any pattern
  matching" **[cited: A2]**. The v1.3 changelog: "All definitions branching
  on a `Dec` value have been rewritten, wherever possible, to branch only
  on the boolean `does` field" **[cited: A3]**.
- `T : Bool → Set` turns a test into a type, as `is_true` does **[memory]**.

### 3.5 Idris 2

`LTE` is inductive (`LTEZero`, `LTESucc`), `lte` is a separate `Bool` test,
and `lteReflectsLTE` joins them **[cited: I1]**. `So : Bool -> Type` wraps a
test as a type; the community finds proofs about it hard to use, the
"boolean blindness" argument (Harper): a `Bool` says that something holds
but not why **[cited: search summary; Harper's post from memory]**.

### 3.6 Systems with one world

- **Isabelle/HOL.** `bool` is the type of propositions. `=` on `bool` is
  `↔`, so the simplifier rewrites with any equivalence, and the code
  generator runs the executable ones. This works because HOL is classical
  and has no proof terms to compute with **[memory]**.
- **Dafny, F\*, Liquid Haskell.** A predicate is a `bool`-valued function
  that an SMT solver reasons about. Dafny adds ghost predicates for
  quantified specs and least/greatest predicates for inductive ones; F\*
  coerces `bool` to a proposition (`b2t`); Liquid Haskell reflects a
  function's code into its type and proves by evaluation ("Proof by Logical
  Evaluation") **[memory; LH abstract cited: V1]**. These are the tools
  programmers meet first, and all of them start from the test.
- **ACL2.** Everything is an executable function; there is no separate
  proposition type **[memory]**.

### 3.7 Making `↔` an equation without an axiom

Observational type theory gives `propext` and function extensionality by
computation rules instead of axioms (Pujet and Tabareau, POPL 2022)
**[cited: P1, abstract]**. It is a different kernel: equality is defined by
recursion on types. Not a small change, and not proposed here.

### 3.8 What the prior art says, taken together

1. Nobody has only one world, except by being classical (Isabelle) or by
   having no proofs to take apart (ACL2).
2. The systems that put propositions first (Lean, Agda, Idris) all ended up
   computing through a `Bool` underneath, and their stated pain is crossing
   between the two.
3. The system that put tests first (SSReflect) needed two things to make it
   pleasant: the `= true` hidden, and views to get the proposition's shape
   on demand.
4. Agda's and Lean's experts independently want the decision to *be* a
   `Bool` with proofs beside it.

## 4. The options

1. **Propositions first.** `≤` becomes an inductive relation; sets get a
   `Mem` proposition; tests are joined to them by `Decidable` (Lean, Agda).
2. **Tests first, everywhere.** Every decidable fact is `test = True`,
   including list membership (which then needs `DecEq`), and `∧` on facts is
   `&&` (pure SSReflect).
3. **A hybrid with a rule and one bridge.** Each predicate has one home,
   chosen by a rule; `Decidable` is the only bridge, shaped so that the
   proposition's `if` is the test by computation.
4. **One thing through coercions** (Lean 4's surface): write either,
   convert silently. Stitchwort already does this in part: `if c` and `&&`
   take a `Bool` or a decidable proposition (`logic.rs:1-19`).

Option 4 is a surface, not a foundation: underneath it still needs 1, 2 or
3. The recommendation ([§6](#6-recommendation)) is 3, with 4's surface.

## 5. The options compared

### 5.1 By criterion

| | 1. Propositions first | 2. Tests everywhere | 3. Hybrid, one bridge |
|---|---|---|---|
| **Big numbers** | Fine, through a bridge lemma applied to `rfl` (measured, `inductive.sw`: 30 digits in 0.2 s). `rfl` alone no longer proves `3 ≤ 5`. | `rfl` (measured) | `rfl` (measured) |
| **Computing with unknowns** | Lost: `2 ≤ n + 5`, and `a ≤ b` from `Succ a ≤ Succ b`, need lemmas | Kept (measured, §2.2) | Kept |
| **Induction on proofs** | Yes. `Le.trans` is two arms (measured) | No; induct on the data. `Nat.leTrans` is four arms | On data for tests; on proofs where a relation is inductive |
| **Specs and goals** | `a ≤ b`, `k ∈ s` | The same, if `= True` is hidden; otherwise noisy | The same |
| **`if` and `match`** | A hypothesis doesn't rewrite the program's `if`; needs `if_pos`-style lemmas or `simp` | One `Bool`, refined by both | One `Bool`, for every decidable proposition (§7.2) |
| **`omega`** | Reads the relation by name; emits bridge terms | Reads the test (today, `omega.rs:24-38`) | As today |
| **`cases`, `auto`** | Nothing to split on in a proposition; decisions must compute | Splits on stuck tests | As 2; `auto` runs the test only |
| **A future `simp`** | Wants `propext` | `Bool` equations; no axiom | `Bool` equations, plus `↔` under connectives (§7.4) |
| **`propext`** | Needed for comfortable rewriting | Not needed: equal tests is a theorem (`Bool.eqOf`) | Not needed |
| **Kernel** | Unchanged | Unchanged | Unchanged; three natives may go (§7.2) |
| **Newcomers** | Natural to Lean and Agda users | Natural to programmers; `= True` and no constructors surprise | Programs read as programs, specs as maths; one rule to learn |
| **Element types without equality** | Fine | Membership impossible to state | Fine (lists stay propositions) |

### 5.2 Five real proofs under each option

The "today" lines are checked in the code; the sketches under each option
are inferred unless marked measured.

**(a) `Nat.leTrans`** (`core/Division.sw:52`). Today, four arms on the
numbers; two are `Void.exfalso (Bool.falseNotTrue h1)`.

- Option 1: two arms by induction on the proof (measured, `inductive.sw`).
  This is option 1's best case.
- Options 2 and 3: as today, but the impossible arms can be `()` (measured
  for `leZero`), so it is four short arms. The inversion that option 1 does
  by matching `LeSucc h`, the test does by computing: `h` is already the
  smaller fact.

**(b) 2021 day 18, `split`** (`Day18.sw:66`; SW-1688). The program has `if
10 ≤ value then Some … else None`; the proofs split on it.

- Today: `match Nat.leq 10 value with | True => … | False => …`, after the
  match on the decision silently stopped working.
- Option 1: the `if` is `Decidable.elim`; proofs match on the decision and
  get an inductive proof, which `omega` must read through a bridge. Works,
  but a hypothesis `h: 10 ≤ value` can't rewrite the `if`.
- Options 2 and 3: `if h: 10 ≤ value then … else …` in the proof, the same
  words as the program. It refines the program's `if` whether or not its
  branches use the proof, because there is one `Bool` (§7.2). The trap
  can't happen.

**(c) 2024 day 8, `part2IncludesPart1`** (`Day08/Proofs/Part2.sw:191`).
Sets and `any`, all tests. Today it rewrites with `Set.containsFilter`
twice, then takes the facts apart with `Bool.andLeft`, `Bool.andRight` and
two nested `List.anyTrueElim` calls with their lambdas written out.

- Option 1: `Set.containsFilter` becomes an `↔`; the rewrites become
  `.forward` and `.backward`, and the facts come apart by pattern: `Both
  inSet (Witness first (Both firstIn inner))`. Better at taking apart,
  worse at rewriting.
- Option 2: as today.
- Option 3: keeps the rewrites, and gets the patterns: the `Bool` fact
  `(s.contains k && xs.any p) = True` is read as `k ∈ s ∧ ∃ x ∈ xs, …`
  through the decisions' proofs (§7.3). The best of both.

**(d) 2020 day 20, `roughAtIff`** (`Day20/Proofs/Monsters.sw:9`). A
proposition-world proof: `at ∈ image.roughAt ↔ ∃ row column, …`, 24 lines,
seven `.forward`/`.backward` calls around `List.memFlatMap`,
`List.memFilterMap` and `List.memWithIndex`.

- Option 1 with `propext` (Lean): three rewrites and a `simp`.
- Option 2: can't be stated as a test; `∃ row` ranges over all numbers.
- Option 3: stays a proposition. It gets shorter only when `rewrite` takes
  an `↔` under connectives (§7.4). This is the proof that shows `↔`
  rewriting is worth having whichever world wins.

**(e) 2024 day 21, `everyNumericKey`** (decide.md §2). `key ∈ numericKeys`
for every key.

- As a proposition it computes to eleven disjuncts that `cases` can't
  split (measured there). The lane proved `numericKeys.contains key = True
  := cases` instead, then crossed with `List.memContains`.
- Option 3: the decision for `key ∈ keys` has `keys.contains key` as its
  `Bool` by computation, so `cases` on the proposition can run the test
  directly, and the crossing lemma is the decision's own `sound` field.

### 5.3 What the comparison shows

- Option 1's real gains are induction on proofs and patterns on facts. For
  facts that follow the data's shape, the test gives the same inversions by
  computing (measured). For patterns, a reader over decisions gives them
  to tests (§7.3).
- Option 1's costs fall on what Stitchwort is for. Proofs follow programs,
  and programs test `Bool`s. Putting an inductive relation between the
  program's test and the theorem's fact adds a crossing to most proofs,
  which is the pain Lean's users report **[cited: Z1]**. It also gives up
  D2541's direction, since less computes.
- Option 2 goes too far: lists of things without equality, `∀` and `∃`
  have no test.
- Naming premises. Today's theorem-binders sweep found 325 theorems with
  a premise taken apart by a pattern (`Both l r`, `Refl`, `()`), which has
  to become a scrutinee of the `match` instead of a named header premise
  (theorem-binders.md §5, item 4, **[checked]**). A test-backed premise is
  never taken apart: it stays in the header under its name and is refined
  as the data is matched (`h1` in `Nat.leTrans`). Propositions first would
  make more premises of the first kind; tests first, fewer **[inferred]**.
- Nothing needs a kernel change, and nothing needs `propext`.

## 6. Recommendation

**Tests first, one term for both, propositions for the rest** (option 3
with option 4's surface). In full:

1. **A fact that a program can test is defined as its test giving `True`.**
   One definition serves the program and the proof. `≤` and `<` on numbers
   stay as they are. `k ∈ s` for sets and maps is `contains … = True`
   (as today).
2. **A fact that can't be tested in general is a proposition**: by
   recursion on the data where it follows the data's shape (as std does 49
   times), and an inductive family only for derivations that the indices
   don't determine (walks, parses, closures).
3. **`Decidable` becomes a `Bool` with its two proofs** (Agda's `Dec`), so
   that for every decidable proposition, `if`, `&&`, `==` and `filter` all
   compute to the one test. This removes the second form of `if` and with
   it the SW-1688 family of traps. Measured to work today as a library
   record (`decision-record.sw`).
4. **Facts about tests are stated once, as equations between `Bool`s**, so
   `rewrite` works. The proposition reading comes from the decision, not
   from a second lemma.
5. **The surface never shows the seam.** A `Bool` where a proposition is
   expected means `b = True`; goals print it without `= True`; a `Bool`
   fact can be matched with `∧`'s, `∨`'s and `∃`'s patterns.
6. **No `propext`.** Equal tests is already a theorem. `rewrite` learns to
   take an `↔` under the logical connectives, with no axiom.

Why this and not propositions first: Stitchwort's own direction is that
computing decides (D2541); its proofs are about programs, which test
`Bool`s; its kernel compares numbers natively; and its `Prop` world already
computes (§2.1). The test-backed `≤` is the part of today's design that
works best (§2.2). The friction listed in §1 comes from the bridge and the
surface, not from the choice of tests, and each item has a fix that needs
no axiom and no kernel change (§7).

What it costs, honestly:

- Two worlds remain, and an author has to place each predicate (§6.1).
- Lists stay mostly propositions and sets mostly tests, so lemmas about
  `∈` have two shapes until §7.4.
- The reader that lets patterns take a `Bool` fact apart (§7.3) is new
  elaborator work and needs its own design note.
- A test's proof can't be inducted on. Where the derivation matters, the
  author must notice and choose an inductive family.

### 6.1 The rule a std author follows

Ask, in order:

1. **Will a program branch on it, filter by it or store it?** Then write
   the test, a function to `Bool`, and let the fact be `test = True`. Give
   it a notation or a method name that reads as the fact (`a ≤ b`, `k ∈
   s`, `c.isDigit`). Don't also define a proposition for it.
2. **Otherwise, does it follow the shape of some data?** (Every element,
   some element, sorted, distinct.) Then define the proposition by
   recursion on that data. If it is decidable when the parts are, give it
   a `Decidable` instance whose `Bool` is the obvious test (`List.all`,
   `List.contains`).
3. **Otherwise, is it a derivation with choices**: several ways to reach
   the same conclusion, or steps that aren't determined by the things
   related? Then an inductive family.
4. **Otherwise** it is a statement: `∀`, `∃`, `∧`, `=` over the above.

And for lemmas:

- About a test: an equation between `Bool`s when both sides are tests
  (`contains (union a b) k = (contains a k ∨ contains b k)`); an
  implication with named premises otherwise. Never the `= True ↔` twin.
- About a proposition: `↔` when it holds both ways, so that one lemma
  serves both directions.
- A negative fact is stated as `¬p`. `test = False` is what a split gives
  and what `rewrite` wants; the two convert without ceremony (§7.3).

## 7. What changes, in sketch

### 7.1 Std

- `Decidable` as in §7.2; instances restated; `deriving (DecEq)` writes a
  test and its two proofs.
- The 27 `= True ↔` twins in std go, once §7.3 exists; `List.memContains`
  and its like become the `sound` and `complete` fields of instances.
- Statements say `k ∈ s`, `a ≤ b`, `c.isDigit`, not `… = True`; proofs say
  `if h: a ≤ b` or `match h: a ≤ b`, not `match Nat.leq a b` (113 places).
- `Ord` keeps its shape. Its relation and decision fields already let
  `Nat` supply its own test.

### 7.2 `Decidable` as a `Bool` with proofs; one `if`

```
type Decidable (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }

instance Nat.decLessEq (m n: Nat): Decidable (m ≤ n) := { does = Nat.leq m n, sound = h => h, complete = h => h }
```

(`test` would be the better field name but is a keyword.) Measured, as a
library type in `decision-record.sw`:

- `(decLe m n).does = Nat.leq m n` by `rfl`, with `m` and `n` unknown;
- `(Dec.and (decLe a b) (decLe c d)).does = (Nat.leq a b && Nat.leq c d)`
  by `rfl`; both fail for today's `Decidable` (§2.3);
- a 30-digit fact by `(…).sound rfl`: the kernel runs only the test;
- one `match h: Nat.leq lo x` refines an `if` written either way.

In the elaborator **[inferred]**:

- `if c then a else b` on a proposition is `Bool.ifThenElse d.does …`. `if
  h: c` is the same test, with the branch given the equation (`does =
  True` or `does = False`) and `h` built from `d.sound` or `d.complete`.
  Both are stuck on the same `Bool`, so anything that refines one refines
  the other. `unused_proof_if`, the comparison special case
  (`bind.rs:212`), `tested_bool`, `Decidable.elimIf`, `Bool.elimDecTrueIf`
  and `W-MATCH-DECISION-IF` have nothing left to do.
- `a == b` is `(DecEq.decide a b).does`: for `Nat`, `Nat.equal a b` itself.
- `&&` on decisions is `&&` on their `Bool`s, so it short-circuits without
  `Decidable.andThen`'s thunk, except where the right side needs the left
  side's proof.
- `auto` and `byDecision` write `d.sound rfl`. `Decidable.IsYes` and
  `fromYes` go.
- A split for evidence, today `match Nat.decLessThan 9 value with | Yes h |
  No r`, is written `if h: 9 < value`, as in the program.
- The kernel never needs a decision's proofs to compute. The natives
  `Nat.decEq`, `Nat.equalRefl` and `Nat.equalSound` exist to make them
  cheap, and could be removed. Needs checking against `decreasing`'s
  generated proofs.

At run time a decision is just its `Bool`: the proof fields are erased.

### 7.3 Reading a `Bool` fact as a proposition

SSReflect's views, without the syntax. The elaborator gets one reader:
given a `Bool` expression, the proposition it decides, found from the
`Decidable` instances whose `does` computes to it:

| `Bool` | Read as |
|---|---|
| `x && y`, `x \|\| y`, `not x` | `P ∧ Q`, `P ∨ Q`, `¬P` |
| `Nat.leq a b`, `s.contains k` | itself: `a ≤ b`, `k ∈ s` |
| `a == b` | `a = b` |
| `xs.all f`, `xs.any f`, `xs.contains x` | `List.All …`, `List.Any …`, `x ∈ xs` |

Used in three places **[inferred]**:

- **Patterns.** A `match` whose scrutinee is `h: e = True` and whose
  patterns are a proposition's constructors (`Both l r`, `Inl`, `Witness`)
  matches on `d.sound h`. Building works the other way: `Both x y` where
  `e = True` is wanted goes through `d.complete`.
- **Negation.** `e = False` is accepted where `¬(e = True)` is wanted, and
  back.
- **Tactics.** `omega` already has a private copy of this table
  (`omega.rs:24-38`: `(p && q) = True` through `Bool.andLeft`, and so on).
  `omega`, `auto` and `cases` share the one reader.

This is the least settled part. It needs its own note: how instances are
found from a `Bool`, what happens when two fit, and how errors read.

### 7.4 `↔` and `propext`

- **Decidable facts need neither.** Two tests that imply each other are
  equal (`Bool.eqOf`, `Bool/Bool.sw`), a theorem. An equation between
  `Bool`s is rewritten by `J` and computes.
- **For propositions, teach `rewrite` the connectives.** To rewrite `P` to
  `Q` by `e: P ↔ Q` inside a goal built from `∧`, `∨`, `¬`, `→`, `∀`, `∃`
  and `↔`, the elaborator builds the proof from one congruence lemma per
  connective. This is Rocq's generalized rewriting **[cited: S1]**, cut
  down to the fixed connectives plus, later, registered ones (`List.All`).
  No axiom; the proof is an ordinary term. It can't rewrite under an
  unknown `r: Prop → Prop`, which a goal rarely has.
- **Not `propext`.** It would be a second axiom, on the path of most
  theorems that rewrite, so `stitchwort axioms` would stop saying "no
  axioms are used" for them. It is consistent with this kernel's rules,
  which are Lean's (subsingleton elimination, K, quotients) **[inferred;
  Lean's consistency proof from memory]**. Its computational cost is that
  `J` along it is stuck, which is how Lean's `decide` gets stuck on
  instances built by rewriting **[cited: L3]**. Stitchwort decides by
  computing, so that cost lands in the wrong place. And adding an axiom
  later is easy; removing one isn't.

### 7.5 Surface and printing

- A `Bool` where a proposition is expected is read as `b = True` (today:
  `E-NOT-A-TYPE` with a note saying to write that). Goals print such a fact
  as `b`, as SSReflect and Lean do.
- `(a <= b) = False` prints with `≤`, like its positive form.
- Errors and `rfl` notes fold `Nat.leq a b` back to `a ≤ b` where they
  print a `Bool` (today a note can show `(a <= b).decTrue.toBool`,
  measured).

### 7.6 Kernel

No change. `docs/core.md` changes only if the three natives go.

## 8. What this note did not do

- No build and no test run; probes only, with the CLI built at 11:34 on
  10 November.
- The reader of §7.3 is a sketch, not a design.
- `Ord`'s shape, and whether `x < y` on a derived order should be a test
  rather than `compare x y = Less`, is left alone.
- Counts are by `grep` over one-line statements.
- Several systems in §3 are cited from memory, as marked. The Lean
  proposal for a `Bool`-shaped `Decidable` was read only in a search
  summary.

## 9. Questions for Matt

- **D3479:** Take "tests first" as the end state: what a program can test
  is defined as its test giving `True` (as `≤` is today), propositions are
  for what can't be tested, and std follows the rule in §6.1? **[rec:
  yes]** The alternative is propositions first, as in Lean: `≤` inductive,
  with a decision joining it to the test.
- **D3480:** Change `Decidable` to a `Bool` with its two proofs (§7.2), so
  there is one form of `if`, and `==`, `&&` and `if` on any decidable
  proposition compute to its test? **[rec: yes]** It touches std core,
  `deriving`, `auto`, `decreasing` and three natives; no kernel rule
  changes. It should get a short design note of its own before it is
  built.
- **D3481:** No `propext` axiom; instead, facts about tests are `Bool`
  equations, and `rewrite` later learns to take an `↔` under the logical
  connectives (§7.4)? **[rec: yes, no axiom]**
- **D3482:** On the surface, let a `Bool` stand where a proposition is
  expected, meaning `b = True`, print it without `= True`, and let a
  `Bool` fact be matched with `∧`, `∨` and `∃` patterns through its
  decision (§7.3, §7.5)? **[rec: yes, after a design note for the
  reader]**

## Sources

- **[G1]** G. Gonthier, A. Mahboubi, "An introduction to small scale
  reflection in Coq", Journal of Formalized Reasoning 3(2), 2010,
  pp. 95-152. <https://jfr.unibo.it/article/view/1979> (PDF read today;
  quotes from §4.1, §4.1.4, §4.3).
- **[M1]** MathComp, `boot/ssrnat.v`.
  <https://github.com/math-comp/math-comp/blob/master/boot/ssrnat.v>
- **[SF]** Software Foundations, vol. 1, "Logic".
  <https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html>
- **[S1]** M. Sozeau, "A New Look at Generalized Rewriting in Type
  Theory", Journal of Formalized Reasoning 2(1), 2009, pp. 41-62.
  <https://jfr.unibo.it/article/view/1574> (abstract and Rocq manual
  summary read; paper not read in full).
- **[L1]** The Lean Language Reference, "Natural Numbers".
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/>
- **[L2]** The Lean Language Reference, "Booleans".
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Booleans/>
- **[L3]** lean4 PR 4674, hints when `decide` fails.
  <https://github.com/leanprover/lean4/pull/4674>
- **[Z1]** Lean Zulip, "Prop -> Bool regression", January 2023.
  <https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Prop.20-.3E.20Bool.20regression.html>
- **[Z2]** Lean Zulip, "bad Decidable instances", 2024-2025.
  <https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/bad.20Decidable.20instances.html>
- **[A1]** agda-stdlib, `Data/Nat/Properties.agda`.
  <https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Properties.agda>
- **[A2]** agda-stdlib, `README.Design.Decidability`.
  <https://agda.github.io/agda-stdlib/master/README.Design.Decidability.html>
- **[A3]** agda-stdlib changelog, v1.3.
  <https://github.com/agda/agda-stdlib/blob/master/CHANGELOG/v1.3.md>
- **[I1]** Idris 2, `libs/base/Data/Nat.idr`.
  <https://github.com/idris-lang/Idris2/blob/main/libs/base/Data/Nat.idr>
- **[V1]** N. Vazou et al., "Refinement Reflection: Complete Verification
  with SMT", POPL 2018. <https://arxiv.org/abs/1711.03842>
- **[P1]** L. Pujet, N. Tabareau, "Observational Equality: Now for Good",
  POPL 2022. <https://hal.science/hal-03367052>
- From memory, not re-read: R. Harper, "Boolean Blindness" (2011); the
  Isabelle/HOL, Dafny, F\* and ACL2 manuals; M. Carneiro, "The Type Theory
  of Lean" (2019).

Stitchwort notes this builds on: decision-match-refines-bool-if.md,
simp.md §3 and §7, decide.md, bounded-readback.md (D2541), map-equality.md,
theorem-binders.md, `docs/core.md`.
