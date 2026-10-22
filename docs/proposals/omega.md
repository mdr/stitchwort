# Proposal: `omega`, linear arithmetic proved by a checked certificate

**Status:** draft 1, 22 October 2026, for review. Docs only: nothing is built. Ticket SW-101
(from SW-96, recommendation 4; D434 made day 5 the acceptance example). Decisions D545 to
D547 ([§10](#10-decisions)) are for Matt. Related: [calc-rewrite.md](calc-rewrite.md) (built;
much of the cheap benefit), [proof-check-speed.md](proof-check-speed.md) and
[../evaluator-speed.md](../evaluator-speed.md) (what checking costs),
[folded-calls.md](folded-calls.md) (SW-257), [integers.md](integers.md),
[well-founded-recursion.md](well-founded-recursion.md) (`decreasing`, whose proofs `auto`
finds), and the day 5 comparison ([aoc-day05-community.md](../comparisons/aoc-day05-community.md)
§1 item 4).

**The short answer.** Add a proof term `omega` that proves linear facts about `Nat` (and later
`Int`) from the facts in scope: `a <= b`, `a < b`, `a = b`, over `+`, `-`, multiplication by a
number, `Nat.max`/`Nat.min`, and `/` or `%` by a number. It works the way Rocq's `lia` does,
not the way Lean's `omega` does: the compiler's own (untrusted) search finds a **certificate**,
a short list of numbers saying how to add the facts up to get `0 < 0`; a **checker written in
Stitchwort**, in the library, with a soundness theorem proved once, checks it. The proof term
is an ordinary application of that theorem, so the kernel re-checks every `omega` by running the
checker, and **nothing new is trusted**. A hand-written prototype of the checker
([§3](#3-what-we-ran)) checks day 5's arithmetic steps in about 10,000 evaluation steps (under
2 ms); a 40-variable chain takes 557,000 steps (17 ms). Day 5's four arithmetic lemmas go
from 49 lines to 28, and from about 25 arithmetic lemma calls to none
([§7](#7-before-and-after)). Recommendation: **build it, in three
stages**, the first only for `<=`, `<`, `=`, `+` and literal `*` (§8).

This note can be read without knowing type theory. Code references were checked at commit
`610b8d5a`. Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given, or in a source
  listed at the end ([S1] and so on), fetched on 22 October 2026;
- **[run]**: a Stitchwort program run on 22 October 2026 (the release CLI from the main
  checkout, built 22 October 20:41). The programs are scratch files, not committed; the
  important parts are quoted where they're used;
- **[cited]**: seen in a search result or secondary source, not opened;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [0. Summary](#0-summary)
- [1. The problem, with our own code](#1-the-problem-with-our-own-code)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. What we ran](#3-what-we-ran)
- [4. How other systems do it](#4-how-other-systems-do-it)
- [5. Options](#5-options)
- [6. The proposal in detail](#6-the-proposal-in-detail)
- [7. Before and after](#7-before-and-after)
- [8. Staged plan and cost](#8-staged-plan-and-cost)
- [9. Risks and critical review](#9-risks-and-critical-review)
- [10. Decisions](#10-decisions)
- [Sources](#sources)

## 0. Summary

- **The problem.** AoC proofs spend a third of their lines on small facts like "`id <= last.to`
  and `last.to + 1 < r.from`, so `id < r.from`", each written as a chain of `Nat.leTrans`,
  `Nat.addOne`, `Nat.leqFalse` and `Nat.leMaxRight` calls (§1). Lean users write `omega`.
- **The idea.** Linear arithmetic over whole numbers is decidable, and for the kind of goal
  above, a proof that the facts can't all hold together is just a list of multipliers: add
  the facts up, each times its multiplier, and the unknowns cancel, leaving something false
  like `0 <= -1` (Farkas's lemma, for the rational version). Finding the multipliers is
  search; checking them is a few additions. Search goes in the compiler (untrusted, in
  Rust), checking goes in the library (a Stitchwort function the kernel runs).
- **What the user writes.** `omega` where a proof is expected; `omega [e1, e2]` to add facts
  that aren't in scope by name (the result of a lemma). It uses every arithmetic hypothesis
  in scope, including the equations `match e: …` and `if h: …` put there (§6.1).
- **What the kernel sees.** `Omega.prove n atoms facts goal cert rfl proofs`: the reified
  problem (numbered unknowns, the facts as syntax trees), the certificate, `rfl` for
  "the checker says yes", and the hypotheses' proofs. Its type computes to the goal, so the
  kernel needs nothing new (§6.3).
- **Cost to check:** measured with a prototype, 5,600 to 55,000 evaluation steps for the
  realistic examples (0.5 to 4 ms per `omega`, elaboration and kernel together), against
  131 ms for today's slowest AoC proof declaration (§3).
- **Cost to build:** a library module (syntax trees, denotations, checker, and the
  soundness proof, perhaps 400 to 600 lines) and an elaborator module (reading goals into
  syntax trees, the search, messages; perhaps 1,000 to 1,500 lines of Rust), in three
  stages (§8) **[inferred]**.
- **Recommendation:** build it as option A (§5): stage 1 is linear facts over `+` and literal
  `*`; stage 2 adds the case splits (`-`, `max`/`min`, `if`, `/` and `%` by literals) and
  `Int`; stage 3 adds goals that are `Bool` equations (day 5's `mergedContains` as one word)
  and, if D547 says so, lets `auto` use it.

## 1. The problem, with our own code

The language has no tactics and no arithmetic automation (`docs/aoc-2025.md:96`
**[checked]**). Comparisons are computed: `m <= n` is `Nat.leq m n = True` and `m < n` is
`Nat.leq (Succ m) n = True` (`crates/elab/src/std/core/Data.sw:56-63` **[checked]**). So a
match on a comparison (`match e: Nat.leq r.from (last.to + 1) with | False => …`) gives a
`Bool` equation, and turning it back into a fact needs `Nat.leqFalse`; `x + 1` and `Succ x`
need `Nat.addOne` between them; and every step of `a <= b <= c` is a `Nat.leTrans` with all
three numbers written out.

Counts at `610b8d5a` **[checked: grep]**: the twenty most common arithmetic lemmas
(`Nat.leTrans`, `Nat.addOne`, `Nat.leqFalse`, `Nat.addSub`, `Nat.addComm` and so on) are
called 43 times in `aoc/src/Aoc/Day02/Proofs/Part2.sw`, 25 in `Day02/Proofs/Repeated.sw`,
16 in `Common/Proofs/Range.sw`, 15 in `Day03/Proofs/Best.sw`, 12 in `Day07/Proofs/Part1.sw`,
and 97 in the library's own `Nat/Arith.sw`. `Nat.addOne` alone is used 32 times.

The day 5 comparison measured it: `topGe`, `coveredTop`, `mergedContains`, `absorbLo` and
`absorbStacked` are 55 of `Proofs/Part2.sw`'s 162 non-comment lines, and the Lean solutions
close the same side goals with one `omega` (kim-em) or `grind` (acarapetis, 18 uses)
(`docs/comparisons/aoc-day05-community.md:69-76` **[checked]**). `docs/compared.md:206`
records that Lean's `simp`, `omega` and `grind` roughly halved proof size on day 1.

Some files even keep lemmas whose only job is arithmetic: `Day07/Proofs/Part1.sw` has
`ltSelfSucc (r: Nat): r < r + 1`, `shift (k r: Nat): k + (r + 1) = Succ (k + r)` and
`ltSucc (h: m < n): m < n + 1` (lines 52-53, 121-123 **[checked]**).

What `calc` and `rewrite` (built) already fix is the *shape* of these proofs: a chain reads
as a chain. They don't remove the steps.

## 2. Words this note uses

- **Linear fact:** a comparison (`<=`, `<`, `=`) between sums of unknowns each multiplied by a
  fixed number, plus a number: `3 * x + y + 7 <= z`. `x * y` with both unknown isn't linear.
- **Atom:** anything the procedure treats as an unknown: a variable, or any term it doesn't
  understand, such as `List.length xs`, `r.to`, `x * y` or `rs.foldLeft f z`. Two atoms are the
  same if they're equal by computation (the same test the type checker uses).
- **Certificate (Farkas):** a natural-number multiplier for each fact. Write each fact as
  `0 <= (some linear expression)`; multiply each by its multiplier and add them all. If every
  unknown cancels and the constant left over is negative, the facts can't all hold. To prove
  a goal, add its negation as a fact (`not (a <= b)` is `b + 1 <= a`) and refute the lot.
- **Tightening:** a step only whole numbers allow: from `2 * x <= 3`, divide by 2 and round
  down to `x <= 1`. Without it, `2 * x = 1` can't be refuted, because `x = 1/2` satisfies it.
- **Proof by reflection:** write the decision procedure (here, the certificate checker) as an
  ordinary function returning `Bool`, prove once that `True` means the goal holds, and prove
  each goal by running the function. Stitchwort already does a small version of this:
  `auto`'s proof of a closed fact is `Decidable.fromYes d Trivial`, which the kernel checks by
  running `d` (`crates/elab/src/auto.rs:9-23` **[checked]**).
- **Reify:** turn a goal the compiler sees (a value, like `Nat.leq (Succ id) r.from = True`)
  into a syntax tree in the language (`Lt (V 0) (V 2)`) whose meaning computes back to it.

## 3. What we ran

A prototype of the checker, in the scratch file `omega1.sw` (about 100 lines). It is the
stage 1 checker without the soundness theorem: `Sound` is passed in as a hypothesis, so the
kernel does everything it would do for a real `omega` except check the one-off proof of
`Sound`. The important parts **[run]**:

```
type NExpr: Type =                     -- Nat expressions over numbered atoms
  | V (i: Nat) | Lit (n: Nat) | Add (a: NExpr) (b: NExpr) | Scale (k: Nat) (a: NExpr)

def NExpr.eval (env: List Nat): NExpr -> Nat
  | V i       => List.getOr 0 i env
  | Lit n     => n
  | Add a b   => NExpr.eval env a + NExpr.eval env b
  | Scale k a => k * NExpr.eval env a

type Fact: Type = | Le (a: NExpr) (b: NExpr) | Lt (a: NExpr) (b: NExpr)

def Fact.holds (env: List Nat): Fact -> Prop
  | Le a b => NExpr.eval env a <= NExpr.eval env b
  | Lt a b => NExpr.eval env a < NExpr.eval env b

-- Linear forms `c + a1*x1 + a2*x2 + …` over Int; each fact becomes `0 <= form`; the goal's
-- negation too; `check` multiplies, adds, and asks "all coefficients 0, constant < 0?".
def check (n: Nat) (hyps: List Fact) (goal: Fact) (cert: List Nat): Bool := …

def Sound: Prop :=
  (n: Nat) -> (env: List Nat) -> (hyps: List Fact) -> (goal: Fact) -> (cert: List Nat) ->
    check n hyps goal cert = True -> Facts.holds env hyps -> Fact.holds env goal

-- absorbStacked's step: id <= last.to and last.to + 1 <= r.from give id < r.from.
theorem stacked (sound: Sound) (id: Nat) (lastTo: Nat) (rFrom: Nat)
    (h1: id <= lastTo) (h2: lastTo + 1 <= rFrom): id < rFrom :=
  sound 3 [id, lastTo, rFrom] [Le (V 0) (V 1), Le (Add (V 1) (Lit 1)) (V 2)] (Lt (V 0) (V 2))
    [1, 1, 1] rfl (Both h1 (Both h2 Trivial))
```

The last line is what `omega` would elaborate to. The kernel checks it by computing
`check … = True` (the `rfl`) and by comparing the type of `sound …`, which computes to
`Nat.leq (Succ id) rFrom = True`, with the goal.

`STITCHWORT_TIMINGS=decls stitchwort check --no-cache` per declaration (elaboration and kernel
together, one run on a busy machine) **[run]**:

| theorem | unknowns | facts | steps | ms (elab + kernel) |
|---|---:|---:|---:|---:|
| `lenTwice` (day 2: `1 <= len` gives `len + 1 <= len + len`) | 1 | 1 | 5,574 | 0.5 |
| `trans3` (`a <= b`, `b <= c` give `a <= c`) | 3 | 2 | 9,422 | 1.2 |
| `stacked` (day 5, above) | 3 | 2 | 9,755 | 0.8 |
| `chain10` (9 facts, goal `3 * x0 <= x9 + 2 * x9 + 7`) | 10 | 9 | 54,751 | 3.6 |
| `chain20` | 20 | 19 | 159,362 | 4.7 |
| `chain40` | 40 | 39 | 557,022 | 16.7 |

For scale: the slowest AoC proof declaration, `twiceTerms`, is 2.9 million steps and 131 ms
(`docs/proposals/proof-check-speed.md`, table "slowest declarations" **[checked]**). The
checker's own definitions cost under 0.2 ms each; the data types cost more (`NExpr` 41 ms,
for its derived instances), once per library load, and would be in the check cache.

Two findings beyond the numbers:

1. **The reified tree has to mirror the goal's shape exactly.** My first `chain10` wrote the
   right side as `Add (V 9) (Add (Scale 2 (V 9)) (Lit 7))`, which means `x9 + (2 * x9 + 7)`;
   the goal was `(x9 + 2 * x9) + 7`. The kernel refused it: "expected `Nat.leq (x0 + (x0 + (x0
   + 0))) (x9 + (x9 + (x9 + 0)) + 7) = True`, but this has type `Nat.leq … (x9 + (x9 + (x9 + 0)
   + 7)) = True`" **[run]**. So a reification mistake is a type error, never a wrong proof,
   and the reifier must read the goal's own tree (§6.2). It also shows `3 * x0` evaluating to
   `x0 + (x0 + (x0 + 0))` (docs/core.md "Numbers": `k * x` unfolds `k` times **[checked]**);
   the denotation `Scale 3 (V 0)` evaluates to the same thing, so they match.
2. **Growth is about quadratic in the number of unknowns** (each fact is a vector as long as
   the number of unknowns), which is harmless at AoC sizes (3 to 10 unknowns).

Not run: the soundness proof, and the search. A checker that also *searched* (option C, §5)
wasn't prototyped; its cost is estimated in §5.

## 4. How other systems do it

### 4.1 Summary

| System | What it decides | How the proof is checked | Trusted extra code |
|---|---|---|---|
| Lean 4 `omega` | linear `Nat`/`Int` facts, `/` `%` by literals, `-`, `max`/`min`, `∧ ∨ ¬ ↔` | the tactic builds a proof term from lemmas, step by step | none |
| Lean `decide` | any closed decidable proposition | kernel evaluates the `Decidable` instance | kernel GMP numbers |
| Mathlib `linarith` | linear facts over ordered fields | simplex finds multipliers; `ring` checks the sum | none |
| Lean `grind` (2025) | includes linear integer arithmetic, complete | own proof terms | none |
| Rocq `lia` / `lra` (micromega) | linear integer / real arithmetic | **reflection**: an oracle finds a certificate, a Rocq checker checks it | none |
| Rocq `romega` (removed) | as `omega` | reflection over a trace | none |
| Isabelle `presburger` | full Presburger arithmetic (Cooper) | **reflection**, verified procedure | none |
| Agda, Idris 2 | rings (`Data.Nat.Solver`, `Algebra.Solver.Ring`) | reflection; no linear-order solver in the libraries | none |
| Dafny, F\* | everything Z3 does | Z3 says so | the SMT solver |

### 4.2 Lean 4 `omega`

Written by Kim Morrison (Lean FRO, 2023), in Lean core since 4.7 (April 2024) [S3]. The
docstring: it "is not yet a full decision procedure (no "dark" or "grey" shadows), but should
be effective on many problems"; it handles `=`, `<`, `≤` and `k ∣ x` over `Nat` and `Int`,
"along with negations of these statements"; `x / k` and `x % k` for a literal `k` become new
variables with bounds; Nat subtraction is split only if a first try fails; `splitDisjunctions`,
`splitNatSub`, `splitNatAbs` and `splitMinMax` are on by default [S1] **[checked]**.
Products of two unknowns become atoms [S2] **[checked]**.

**It is not reflective.** It records how each derived fact was made (a `Justification`:
`assumption | tidy | combine | combo | bmod`) and, once it finds a contradiction, turns that
into a proof term applying lemmas such as `Constraint.combine_sat'` and `tidy_sat`; `decide`
is used only for small closed side facts [S2] **[checked]**. The linear forms appear in the
proof as data. So Lean's `omega` is close to option B below.

The algorithm follows Pugh's Omega test [S4] **[cited]**: eliminate equalities (with Pugh's
"balanced mod" when no coefficient is ±1), then eliminate unknowns one by one by
Fourier–Motzkin (the "real shadow"), tightening by the greatest common divisor as it goes
[S2] **[checked]**. The full test adds "dark" and "grey" shadows to handle the gap between
rational and whole-number solutions; Lean skips them, so it can fail on some true goals
("if the real shadow is satisfiable we must fail") [S2] **[checked]**. In practice the
community uses it on exactly our kind of goal (§1).

### 4.3 Rocq `lia` (micromega): the design this note copies

Besson, "Fast reflexive arithmetic tactics: the linear case and beyond" (TYPES 2006) [S5]
**[cited]**. An untrusted oracle searches for a refutation certificate (a Positivstellensatz
certificate; for linear problems, Farkas multipliers); a checker written in Rocq, proved
sound once, checks it; the goal enters the proof term as a reified syntax tree ("`__ff` is a
reified representation of the goal"). For integers, `lia` adds cutting planes (rounding
bounds up or down) and case splits on expressions with a small range; `zify` moves `nat`
goals to `Z` first [S6] **[checked]**. Rocq's earlier `omega` implemented "a small subset" of
Pugh's algorithm and was partial; its reflective `romega` was deprecated in 8.9 in favour of
`lia` [S7] **[checked]**.

### 4.4 Others

- **Mathlib `linarith`**: the oracle (simplex by default) finds natural-number coefficients;
  the sum is checked by `ring` normalisation, not reflection; complete over ordered fields, not
  over the integers [S8] **[checked]**.
- **Lean `decide`**: the kernel evaluates the `Decidable` instance; the kernel has GMP numbers
  and overrides `Nat.add`, `sub`, `mul`, `ble`, `beq` and others [S9] **[checked]**, much as
  Stitchwort's kernel has native `Nat.add`, `Nat.leq` and others (docs/core.md "Numbers"
  **[checked]**). Stitchwort's `auto` is already a `decide` for closed goals (§2).
- **Lean `grind`** has a "model-based" linear integer arithmetic solver, "complete for LIA";
  Lean's `lia` is now a thin wrapper around it [S10] **[checked]**.
- **Isabelle**: Chaieb and Nipkow verified Cooper's algorithm (full Presburger arithmetic) and
  ran it by reflection; the reflective version was "one to two orders of magnitude faster" than
  proof by tactics [S11] **[cited]**.
- **Agda, Idris 2**: reflective ring solvers in the libraries (`Data.Nat.Solver` on
  `Algebra.Solver.Ring.Simple` [S12] **[checked]**; Idris's `Algebra.Solver.Ring` [S13]
  **[cited]**). No `<=` solver found in either library **[cited]**.
- **Dafny, F\***: arithmetic goes to Z3, which is trusted; nonlinear arithmetic is undecidable
  and unstable, so F\* advises turning it off and stepping by hand [S14] **[checked]**.
- **Literature:** Boutin introduced proof by reflection in Coq (1997) [S15] **[cited]**;
  Chlipala's CPDT chapter "Reflection" is the readable account: "such a proof is checked by
  running the decision procedure" [S16] **[checked]**. Grégoire and Leroy's compiled reduction
  (Rocq's `vm_compute`) [S17] **[cited]** exists because reflective proofs are only as fast as
  the kernel's evaluator.
- **Theory:** Presburger arithmetic (whole numbers with `+`, `<=`, quantifiers) is decidable,
  but the full theory needs doubly exponential time in the worst case (Fischer and Rabin, 1974
  [S18] **[cited]**). Goals with no quantifiers, which is all `omega` takes, are integer linear
  programming: NP-complete in general **[unverified]**, fast on the sizes here.

### 4.5 What to take

From Rocq: the split between untrusted search and a small checked certificate. From Lean: the
fragment (including the case splits on `-`, `max`/`min`, `/` and `%` by literals), gathering
facts from the context, the name, and accepting incompleteness (no dark or grey shadows). From
Stitchwort itself: `auto`'s "run a `Bool` function in the kernel" pattern, which is already
trusted and fast for numbers.

## 5. Options

### (A) Certificate checker by reflection (recommended)

The elaborator reifies the goal and the facts, searches for multipliers (Fourier–Motzkin, in
Rust), and emits `Omega.prove … cert rfl proofs`. The library holds the checker and its
soundness theorem. **Kernel work per use:** run the checker (measured, §3). **Trusted code
added:** none. **Soundness proof:** about linear forms (adding and scaling preserve meaning,
non-negative combinations of non-negative things are non-negative), not about the search.
**Completeness:** whatever the Rust search finds; it can be improved without touching the
library or the kernel.

### (B) Proof built from lemmas (Lean's way)

The elaborator searches the same way and then writes the proof as `Nat.leTrans`,
`Nat.leAddCong` and friends, with the normalisation of sums done by `Nat.addComm` and
`Nat.addAssoc` rewrites. No soundness theorem needed. But each normalisation step is a term
whose hidden arguments restate the sums, and proof-check-speed.md found that hidden arguments
are 81% of the nodes in the slow AoC proofs and that checking time follows term size
(`docs/proposals/proof-check-speed.md`, "Causes" 1 **[checked]**). Reflection replaces those
rewrites by computation, which is the point of it (CPDT: the reflective proof is linear in the
input, the tactic one superlinear [S16] **[checked]**). **[inferred]**

### (C) The whole decision procedure in the language

As (A), but the search itself is a Stitchwort function the kernel runs (Isabelle's Cooper,
Rocq's `romega`). No Rust search; but the kernel runs Fourier–Motzkin on every check, twice
(the elaborator evaluates too, proof-check-speed.md "fourChecked … computed by both"
**[checked]**). Eliminating one unknown pairs every lower bound with every upper bound; for
day 5's sizes (3 to 6 unknowns, 5 to 10 facts) that's perhaps tens to hundreds of
combinations, each costing what the whole stage 1 check costs in §3: **[inferred]** 10 to 100
times the checking cost, still tens of milliseconds, but the soundness proof must then cover
the search (termination, the elimination order), and every improvement to the search is a
library change with proofs. Not recommended; (A) can always grow a small in-language fallback.

### (D) A trusted solver (Dafny's way)

Add the procedure, or an SMT solver, to the kernel's trusted base. Contrary to the project's
"small trusted kernel" rule (DESIGN.md §13) and unnecessary given §3. Not considered further.

### (E) Don't build: a lemma pack instead

Add `Nat.leAddOne`, `Nat.ltOfLeqFalse`, a `Nat.max` lemma set, and similar, and leave proofs as
they are. Cheap, helps a little; doesn't change the shape (§7 shows lines dominated by the
steps themselves, not by missing lemmas).

### Side by side

| | A: certificate | B: lemma chain | C: in-language search | E: lemmas |
|---|---|---|---|---|
| New trusted code | none | none | none | none |
| Kernel cost per use | small (measured) | grows with term size | 10–100× A (guess) | n/a |
| Proof term size | small: tree + numbers | large | small | n/a |
| One-off proof work | soundness of the checker | none | soundness of the search | lemmas |
| Search improvements | Rust only | Rust only | library + proofs | n/a |
| Precedent | Rocq `lia` | Lean `omega` | Isabelle, `romega` | — |

## 6. The proposal in detail

### 6.1 What you write

```
theorem absorbLo (r: Range) (b: Nat) (h: r.from <= b): (merged: List Range) -> LoAtMost r.from merged -> LoAtMost b (absorb merged r)
  | Nil,               ok => h
  | Cons last earlier, ok =>
    match e: Nat.leq r.from (last.to + 1) with
      | True  => omega            -- from ok: last.from <= r.from and h: r.from <= b
      | False => h
```

- **`omega`** is a term, like `rfl`, checked against the expected type, which must be (after
  computing) a fact in the fragment, or `Void` (prove the facts in scope contradictory).
- **Facts used:** every hypothesis in scope whose type is a fact in the fragment: parameters,
  `let`s, and what `match e: …` and `if h: …` add, including `Nat.leq a b = False` (read as
  `b < a`) and `(p && q) = True` (read as both). Others are ignored.
- **`omega [e1, e2]`** adds facts by term, for a lemma's result that isn't in scope:
  `omega [topGe (Nat.max z r.to) rs]`. It's the same as `let`-binding them first.
- In a `calc` step (`_ <= r.from := omega`) or a `rewrite` (`rewrite (omega: a + b - b = a)`),
  as any proof term.

### 6.2 The fragment, by stage

| Construct | Stage | How |
|---|---|---|
| `<=`, `<`, `=` between `Nat` expressions, in goal and facts | 1 | linear forms; `=` as two `<=`; goal `=` refuted twice |
| `Nat.leq a b = True` / `= False`, `(p && q) = True`, `Not (a <= b)`, `Void` goal | 1 | read as the facts they mean |
| `+`, `Succ`, numbers, `k * x` and `x * k` for a number `k` | 1 | coefficients |
| any other term (`List.length xs`, `r.to`, `x * y`, a call) | 1 | an atom; atoms compared by computation |
| `a - b` (truncated) | 2 | new atom `t`, split: `b <= a` and `t + b = a`, or `a < b` and `t = 0` |
| `if c then x else y` on a comparison, so `Nat.max`, `Nat.min` | 2 | new atom, split on `c` |
| `x / k`, `x % k` for a number `k` | 2 | new atoms `q`, `r` with `x = k * q + r`, `r < k` |
| `a != b` as a fact; `(p \|\| q) = True` | 2 | split |
| `Int` (`+`, `-`, negation, `<=`, `<`, `=`), `Nat.toInt` | 2 | the checker works over `Int` anyway |
| tightening (divide by the gcd, round) | 2 | a certificate step |
| goals that are `Bool` equations of comparisons (`(p && q) = (r \|\| s)`) | 3 | split on each comparison |

Out of scope, as in Lean: `x * y` with both unknown (an atom, no laws), `/` and `%` by an
unknown, `Nat.pow` with an unknown exponent, quantifiers in facts (`(id: Nat) -> covered rs id =
True -> id < b` is used by applying it, `omega [b id h]`).

**Reading goals (the reifier).** The elaborator has the goal as a value, already computed:
`Range.contains r id` has unfolded to its `&&` of two `Nat.leq`s, `Nat.max a b` to a stuck
`if`, `3 * x` to `x + (x + (x + 0))` (§3). That helps: user definitions that are really
arithmetic (`Range.size`, `Range.contains`) are seen through with no `simp` step, which Lean
needs (kim-em's `simp only […] at *; omega`, aoc-day05-community.md:437 **[checked]**). The
reifier walks the value, recognises the library's arithmetic heads, and makes every other
subterm an atom. The tree it builds must evaluate back to *exactly* the same value (§3,
finding 1): it reads the value's own shape, `k + x` and all, and the library's denotation uses
the same definitions the surface syntax does. Before emitting the term, the elaborator checks
the denotation against the goal itself, so a reifier bug is reported as an internal error
naming `omega`, not as a confusing type mismatch. With glued values on (SW-257,
docs/core.md "Glued calls" **[checked]**), the reifier forces calls as it walks, as `rewrite`
and decision search already do (D484).

### 6.3 The library side: `Std.Omega`

Shapes, not final code:

```
namespace Std.Omega
type Term  = V (i: Nat) | Lit (n: Nat) | Add … | Scale (k: Nat) (t: Term) | Sub … | IntTerm …
type Fact  = Le (a b: Term) | Lt … | Eq … | Not (f: Fact) | And …
def Fact.holds (atoms: List Nat): Fact -> Prop       -- computes to the user's own statement
def Cert = …                                          -- multipliers; later: splits, tightening
def check (facts: List Fact) (goal: Fact) (cert: Cert): Bool
theorem prove (atoms: List Nat) (facts: List Fact) (goal: Fact) (cert: Cert)
    (ok: check facts goal cert = True) (hs: Facts.holds atoms facts): Fact.holds atoms goal
```

`prove` is the soundness theorem, proved once. What it needs **[inferred]**:

1. the linear form of a term means the term: `Lin.eval atoms (Term.lin t) = Nat.toInt (Term.eval
   atoms t)`, by induction, from the `Int` ring laws the library already has (`Int.addAssoc`,
   `Int.addComm`, `Int.mulDistribLeft`, `Int.toIntAdd`, `Int.toIntMul` and others,
   `crates/elab/src/std/Int/Int.sw` **[checked]**);
2. a fact holds exactly when its form is non-negative, and the negated goal's form is
   non-negative when the goal fails; this needs some `Int` order lemmas the library lacks
   today (adding preserves `<=`, multiplying by a non-negative number does) **[checked: no
   `Int.le…` theorems in `std/Int`, `std/core`]**;
3. a combination with natural multipliers of non-negative forms is non-negative (induction);
4. a form whose coefficients are all zero means its constant, and a negative constant
   isn't non-negative;
5. the goal is decided by computing (`Nat.leq`), so "if it failed, its negation holds" is a
   `match` on the `Bool`, not classical logic.

Stage 2 adds a lemma per split (`a - b`, `if`, `/`, `%`; the library already has
`Nat.divMod`, `Nat.modLess`, `Nat.addSub`) and tightening (needs an `Int` floor-division
lemma; `Int.fdiv` exists, its laws may not). The checker works over `Int` inside, which the
prototype shows is cheap enough even though `Int` has no natives (decision K1, docs/core.md
"Numbers" **[checked]**).

### 6.4 The elaborator side

`crates/elab/src/omega.rs` **[inferred]**: gather facts (§6.1); reify (§6.2), keeping an atom
table up to conversion; turn facts into linear forms with rational or integer coefficients;
search (Fourier–Motzkin with the multipliers carried along, plus tightening; simplex if
problems grow); on success, build the certificate and the term; on failure, report.

**Messages** (`E-OMEGA`): the goal, the facts used, the atoms (so a user sees that
`r.to` and `Range.to r` were one atom, or that `x * y` was opaque), and a counterexample when
the search finds one (Fourier–Motzkin's leftover constraints give values for the unknowns,
which may be fractions; Lean prints "a possible counterexample" this way **[unverified]**).
For example:

```
[E-OMEGA] omega can't prove `id < r.from`
  from:  id <= last.to          (i)
         last.from <= r.from    (ok)
  it doesn't follow: for example id = 5, last.to = 5, last.from = 0, r.from = 5
  (an `if`, `-`, `max` or `min` needs stage 2; `x * y` is treated as one unknown)
```

The elaborator also runs the checker before emitting the term (it must, to type-check `rfl`),
so the check is computed twice, once by each side, as for `auto` today
(proof-check-speed.md: "computed by both, which is the price of re-checking in the kernel"
**[checked]**). The numbers in §3 already include both.

### 6.5 Interactions

- **`auto`**: unchanged in stages 1 and 2. D547 asks whether `auto` should try `omega` after
  hypotheses and decision procedures fail, for arithmetic obligations only. That would
  discharge `[auto ok: i < xs.length]`, the `%` and `/` side conditions and `decreasing`
  obligations from facts in scope, which today need the exact fact in scope. The cost is
  failing obligations get slower (a search) and proofs succeed for less visible reasons.
- **`calc` and `rewrite`**: `omega` is a term, so it works as a step's justification or as the
  equation `rewrite` uses (with a type ascription). They remain the tools for everything that
  isn't arithmetic.
- **`match` and `if h:`**: the facts they add are used automatically, so the common
  `match e: Nat.leq … with | False => Nat.leqFalse …` pattern loses its lemma calls. `omega`
  doesn't remove the need to match on a program's own `if` when the goal mentions what the
  `if` computes (a list, in day 5's `absorb`).
- **Folded and glued values (SW-257)**: see §6.2. The emitted term carries the atoms as
  terms; an atom like `rs.foldLeft (m r => Nat.max m r.to) z` is quoted once into the
  `atoms` list. With glue on in the elaborator, atoms stay folded and small.
- **Erasure and JS**: proofs are erased at run time (docs/core.md "Erasure"): `omega` costs
  nothing when a program runs.
- **Check cache**: an `omega` proof is part of its declaration and cached with it.
- **Hashes**: `Std.Omega` changes when its checker grows, which changes the hashes of proofs
  using it; acceptable (no users).

## 7. Before and after

Line counts are non-blank lines of the theorem. "After" is a sketch, not run; the stage needed
is given for each.

### 7.1 Day 5 (`aoc/src/Aoc/Day05/Proofs/Part2.sw`)

**`absorbLo`** (stage 1): 9 lines → 6. Shown in §6.1; the `True` arm's three-line `calc`
becomes `omega`.

**`absorbStacked`** (stage 1): 19 lines → 12.

```
-- before
      | False =>
        Both
          (id h =>
            match i: last.contains id with
              | True =>
                calc id
                  _ < Succ last.to := containsHi last id i
                  _ = last.to + 1  := Eq.sym (Nat.addOne last.to)
                  _ <= r.from        := Nat.lessLe (last.to + 1) r.from (Nat.leqFalse r.from (last.to + 1) e)
              | False =>
                calc Succ id
                  _ <= last.from := b id h
                  _ <= r.from    := ok)
          (Both b rest)
-- after
      | False =>
        Both
          (id h =>
            match i: last.contains id with
              | True  => omega              -- i: (last.from <= id && id <= last.to) = True; e: Nat.leq r.from (last.to + 1) = False
              | False => omega [b id h])    -- b id h: id < last.from; ok: last.from <= r.from
          (Both b rest)
```

**`coveredTop`** (stage 2, for `Nat.max`): 10 lines → 7; the three-step `calc` becomes
`omega [topGe (Nat.max z r.to) rs]` (the fold is one atom; `e` gives `id <= r.to`; the
`if` inside `Nat.max` is split).

**`mergedContains`** (stage 3, a `Bool` equation): 11 lines and 13 lemma calls → 3:

```
theorem mergedContains (a: Range) (r: Range) (id: Nat) (h1: a.from <= r.from) (h2: r.from <= a.to + 1):
    Range.contains { from = a.from, to = Nat.max a.to r.to } id = (a.contains id || r.contains id) :=
  omega
```

With stage 2 only, the match on the two comparisons stays and each of the three arms is
`omega` (5 lines).

Day 5's four lemmas: 49 lines → 28 after stage 3 (about 31 after stage 2) **[checked: line
counts at `610b8d5a`; after-counts from the sketches]**. Nearly every arithmetic lemma call
goes; what's left is the case analysis on the program's own `if` (the `match` on
`Nat.leq r.from (last.to + 1)`) and the list structure. `topGe` is an induction and stays.

### 7.2 Day 2, `repBlockLength` (`Day02/Proofs/Part2.sw:54-64`, stage 1)

The first two `calc` steps (two lines of about 300 characters each, five lemma calls) become
one, with `len` for `List.length (Nat.digits x)` (an atom):

```
        _ <= len + (len + List.length (List.concat (List.replicate m (Nat.digits x))))
            := omega [Nat.digitsNonEmpty x]        -- 1 <= len
```

### 7.3 Day 2, `periodSub` (`Day02/Proofs/Part2.sw:349-356`, stage 2, for `-`)

```
-- before
          := Eq.cong (y => g (y % len)) (Eq.trans (Nat.addAssoc i (p - q) q) (Eq.cong (t => i + t) (Eq.trans (Nat.addComm (p - q) q) (Nat.addSubCancel q p hle))))
-- after
          := Eq.cong (y => g (y % len)) (omega: i + (p - q) + q = i + p)     -- uses hle: q <= p
```

### 7.4 `Common/Proofs/Range.sw`, `countFrom` (stage 2)

Its first arm, `Eq.sym (Nat.subEqZero (Succ r.to) (Nat.max r.from s) (Nat.leTrans … (Nat.leCongRight
… (Nat.addZero s) h) (Nat.leMaxRight r.from s)))`, becomes `omega` (goal `0 = Succ r.to - Nat.max
r.from s` from `h: r.to < s + 0`); the `Nat.maxRight`/`Nat.subSuccRight` steps of the other arms
become `omega` steps in their `calc`s.

### 7.5 Day 7's arithmetic-only lemmas (stage 1)

`ltSelfSucc`, `shift` and `ltSucc` (`Day07/Proofs/Part1.sw:52-53, 121-123`) each become `omega`,
or disappear with their call sites writing `omega` instead.

### 7.6 What stays

Day 2's `blockAtMost` needs `k <= k * n` from `2 <= n` with both unknown: nonlinear, out of
scope (Lean's `omega` can't either; Lean users reach for `nlinarith` or a lemma). Day 1's
`% (Succ highest)` is `%` by an unknown: out of scope, though its side conditions
(`highest - j < Succ highest`) are in scope at stage 2. Induction (`topGe`, `stackedCount`)
is untouched.

## 8. Staged plan and cost

Sizes are guesses **[inferred]**, from the prototype (100 lines for a stage 1 checker without
proofs) and from the library's existing `Nat`/`Int` proofs.

| Stage | What | Library | Elaborator | Acceptance | Who |
|---|---|---|---|---|---|
| 1 | `Std.Omega`: terms, facts, linear forms, Farkas checker, `prove` and its proof; `omega` and `omega [..]`; facts from the context; FM search; `E-OMEGA` with a counterexample | 300–450 lines (half proofs, plus the `Int` order lemmas) | 700–1,000 lines Rust | `absorbLo`, `absorbStacked`, `repBlockLength`, Day 7's three lemmas, a test file of 30+ goals and 10+ refusals | Opus (the soundness proof, reifier design); Sonnet for the search and messages |
| 2 | splits (`-`, `if`/`max`/`min`, `/` `%` by literals, `!=`, `\|\|`); `Int`; tightening | 150–250 lines | 300–500 lines | `coveredTop`, `countFrom`, `periodSub`, `mergedContains` with its match | Opus |
| 3 | `Bool`-equation goals; `auto` fallback if D547 | 50–100 lines | 200–300 lines | `mergedContains` as `omega` | Opus |
| then | convert AoC proofs (one lane per day or two), measure lines and check time | | | the day 5 count in §7.1 | DeepSeek with a list, Sonnet review |

Each stage: one fresh lane, design review of the soundness statement before the proof is
written (the statement is the trusted part, in the sense that a wrong statement proves the
wrong thing), the targeted tests named in the lane, and the check-time numbers of §3 rerun.

**Checking cost to expect:** 0.5 to 5 ms per `omega` on AoC-sized goals, each split doubling
it (stage 2 splits multiply: three `-`s are up to 8 cases; the search should split only what it
needs, as Lean does). A proof file with 30 `omega`s would add 15 to 150 ms; today's whole AoC
project checks in about 1.3 s (proof-check-speed.md, "Before and after" **[checked]**).
Removing the lemma chains should also shrink terms, which proof-check-speed.md found is what
checking time follows **[inferred]**.

## 9. Risks and critical review

- **The soundness proof is real work in a language with no tactics.** Several hundred lines
  of `Int` algebra by `calc` and `rewrite`. Mitigation: the prototype's checker is small, the
  `Int` ring laws exist, and it's done once. If it stalls, stage 1 could run over `Nat` only
  (keep each fact as `left <= right` with both sides `Nat` forms, cancel common terms), where
  the library has far more lemmas; that's an implementation choice for the lane.
- **Incomplete, like Lean's.** No dark or grey shadows: a few true whole-number goals fail.
  The message says the search found a rational counterexample. Can be fixed later in Rust
  alone, adding case-split certificates; the library only needs a split step.
- **Shape matching is brittle (§3, finding 1).** Mitigated by reifying from the value and
  checking the denotation before emitting; tested by a property test that reifies random
  arithmetic expressions and checks `rfl`.
- **Magic hides reasons.** A proof that says `omega` doesn't show *why*. Lean users accept
  this; the `calc` style is still there when the reasoning matters for a reader. Keep tests
  beside proofs, as now.
- **Growth of facts in scope.** Inside long proofs many facts are in scope; all are passed.
  Fourier–Motzkin can blow up (doubly exponential in the worst case). Mitigation: drop facts
  that share no atom with the goal (transitively), and cap the search with a clear error.
- **Overlap with SW-257 (glue).** The reifier must force calls; if glue lands first, a
  reifier written for unglued values needs `force` added. Small; noted for the lane.
- **Is it worth it versus option E?** §7 shows about 40% fewer lines in day 5's arithmetic
  lemmas, nearly all lemma calls gone, and single steps in place of 300-character ones
  (day 2); a lemma pack wouldn't remove the steps. The line saving is smaller than "Lean
  halves it" suggests, because our proofs still match on the program's `if`s, which Lean's
  `simp`/`split` do for it.
  The cost is three lanes of mostly Opus work. On balance yes, but this is the decision D545
  asks for.

## 10. Decisions

**D545. Build `omega`, as a certificate checked by a library function (option A), in the three
stages of §8?** Recommendation: **yes**, stage 1 now, stages 2 and 3 after the AoC proofs
using stage 1 are measured. Alternatives: B (Lean's lemma chains: no soundness proof, bigger
terms, slower checks), C (search in the language: slower checks, harder proof), E (a lemma
pack; don't build).

**D546. Surface: a term `omega` (a new keyword) that uses every arithmetic fact in scope, plus
`omega [e1, e2]` for extra facts?** Recommendation: **yes**. Alternatives: only an explicit
list (`omega [h1, h2]`: clearer, but most uses would list every hypothesis); a different name
(`arith`, `linear`: plainer English, but `omega` is what Lean users know, and Lean's
fragment is what this covers); `by omega` (no: there is no tactic language).

**D547. Should `auto` try `omega` for arithmetic obligations once it has failed to find a
hypothesis or decision procedure** (index bounds, `/` and `%` side conditions, `decreasing`)?
Recommendation: **yes, in stage 3**, after stage 1 and 2 have shown the cost of a failing
search; until then `[ok := omega]` passes one by hand. Alternative: never (keep `auto`
predictable: it only finds what's there).

## Sources

Fetched 22 October 2026 by a research sub-agent, which recorded what each page says; labels
as given in the text.

- [S1] Lean 4 `omega` docstring, `src/Init/Tactics.lean`:
  https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Tactics.lean **[checked]**
- [S2] Lean 4 `omega` implementation notes and source: https://lean-lang.org/doc/api/Lean/Elab/Tactic/Omega.html
  and https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Omega/Core.lean
  (`Justification`, `Justification.proof`; "Authors: Kim Morrison") **[checked]**
- [S3] Lean 4.7.0 release post: https://lean-lang.org/blog/2024-4-4-lean-470 **[cited]**
- [S4] W. Pugh, "The Omega test: a fast and practical integer programming algorithm for
  dependence analysis", Supercomputing '91 (CACM 1992); slides:
  https://www.cmi.ac.in/~madhavan/courses/theorem-proving-2014/slides/linear-omega.pdf **[cited]**
- [S5] F. Besson, "Fast reflexive arithmetic tactics: the linear case and beyond", TYPES 2006,
  LNCS 4502, pp. 48–62: https://researchr.org/publication/Besson06/bibtex **[cited]**
- [S6] Rocq reference manual, micromega (`lia`, `lra`, `zify`):
  https://rocq-prover.org/doc/master/refman/addendum/micromega.html **[checked]**
- [S7] Coq 8.9 reference manual, omega and `romega`:
  https://rocq-prover.org/doc/v8.9/refman/addendum/omega.html **[checked]**
- [S8] Mathlib `linarith`:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Linarith/Frontend.html **[checked]**
- [S9] Lean reference, natural numbers (kernel GMP, overridden operations):
  https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/ **[checked]**
- [S10] Lean `grind` (tactic reference; examples):
  https://lean-lang.org/doc/reference/4.26.0/The--grind--tactic/Bigger-Examples/ **[checked]**
- [S11] A. Chaieb, T. Nipkow, "Proof synthesis and reflection for linear arithmetic", JAR 41
  (2008): https://www.proof.cit.tum.de/~nipkow/pubs/jar08.html **[cited]**
- [S12] agda-stdlib `Data.Nat.Solver`:
  https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Solver.agda **[checked]**
- [S13] Idris 2 `Algebra.Solver.Ring`:
  https://idris2docs.sinyax.net/data/algebra/docs/Algebra.Solver.Ring.html **[cited]**
- [S14] F\* and SMT: https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html
  **[checked]**; Dafny FAQ: https://github.com/microsoft/dafny/wiki/FAQ **[cited]**
- [S15] S. Boutin, "Using reflection to build efficient and certified decision procedures",
  TACS '97, LNCS 1281 **[cited]**
- [S16] A. Chlipala, *Certified Programming with Dependent Types*, "Reflection":
  http://adam.chlipala.net/cpdt/html/Reflection.html **[checked]**
- [S17] B. Grégoire, X. Leroy, "A compiled implementation of strong reduction", ICFP 2002:
  https://xavierleroy.org/publi/strong-reduction.pdf **[cited]**
- [S18] M. Fischer, M. Rabin, "Super-exponential complexity of Presburger arithmetic" (1974):
  https://dspace.mit.edu/handle/1721.1/148872 **[cited]**
