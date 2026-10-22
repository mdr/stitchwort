# Proposal: `omega`, linear arithmetic proved by a checked certificate

**Status:** draft 2, 22 October 2026, after an external expert review (D548). Docs only:
nothing is built. Ticket SW-101 (from SW-96, recommendation 4; D434 made day 5 the acceptance
example). Decisions D545 to D547 ([§10](#10-decisions)) are for Matt; the review agreed with
all three, with changes this draft folds in ([Response to review](#response-to-review-draft-2)).
Related: [calc-rewrite.md](calc-rewrite.md) (built; much of the cheap benefit),
[proof-check-speed.md](proof-check-speed.md) and [../evaluator-speed.md](../evaluator-speed.md)
(what checking costs), [folded-calls.md](folded-calls.md) (SW-257), [integers.md](integers.md),
[well-founded-recursion.md](well-founded-recursion.md) (`decreasing`, whose proofs `auto`
finds), and the day 5 comparison ([aoc-day05-community.md](../comparisons/aoc-day05-community.md)
§1 item 4).

**The short answer.** Add a proof term `omega` that proves linear facts about `Nat` (and later
`Int`) from the facts in scope: `a <= b`, `a < b`, `a = b`, over `+`, multiplication by a
number on either side, and later `-`, `Nat.max`/`Nat.min`, and `/` or `%` by a number. It
works the way Rocq's `lia` does, not the way Lean's `omega` does: the compiler's own
(untrusted) search finds a **certificate**, a short derivation saying how to combine the
facts (add them with multipliers, divide and round, split into two cases) until every case
reaches something false like `0 <= -1`; a **checker written in Stitchwort**, in the library,
with a soundness theorem proved once, checks it. The proof term is an ordinary application of
that theorem, so the kernel re-checks every `omega` by running the checker, and **nothing new
is trusted**. A hand-written prototype of the checker ([§3](#3-what-we-ran)) replays day 5's
certificates in about 10,000 evaluation steps (under 2 ms); a 40-variable chain takes 557,000
steps (17 ms). Those numbers are for replaying a certificate only, not for a whole `omega`.
Day 5's four arithmetic lemmas go from 49 lines to 28, and from about 25 arithmetic lemma
calls to none ([§7](#7-before-and-after)). Recommendation: **build it**, and make the first
milestone a **complete small vertical slice**: real reading of goals, real bridge proofs, the
proved soundness theorem, the search, and kernel checking, judged by the review's acceptance
table ([§8](#8-staged-plan-and-cost)).

This note can be read without knowing type theory. Draft 1's code references were checked at
`610b8d5a`; draft 2's new ones at `bc1cf9ee`. Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given, or in a source
  listed at the end ([S1] and so on), fetched on 22 October 2026;
- **[run]**: a program run on 22 October 2026: a Stitchwort program (the release CLI from the
  main checkout, built 22 October), or, where said, a small Python script. The programs are
  scratch files, not committed; the important parts are quoted where they're used;
- **[cited]**: seen in a search result, a secondary source, or the external review, not opened;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [Response to review (draft 2)](#response-to-review-draft-2)
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

## Response to review (draft 2)

An external reviewer read draft 1 and the review pack (the brief we sent with it). Their
verdict: build it, with the proposed reflective certificate checker; yes to D545, D546 and
(provisionally) D547; but tighten the interfaces between source propositions, syntax trees
and integer constraints, fix a multiplication gap in stage 1, make a dimension rule explicit,
and soften some cost and completeness claims. Matt agreed to adopt the changes. Point by
point:

| # | Review point | What changed |
|---|---|---|
| 1 | The checker's separate `n` (number of unknowns) could drop a coefficient: with `n = 0`, `env = [1]`, goal `V 0 <= Lit 0` (false: `1 <= 0`), a checker that sizes vectors by `n` sees `-1 >= 0` and accepts. | No separate `n`: coefficient vectors grow to cover every index the syntax mentions, so nothing is dropped. This is what the prototype already does (`addCoeffs` keeps the longer list, `unit i` has length `i + 1`; `omega1.sw` **[checked]**), but draft 1 didn't say so. The contract is now part of the soundness theorem (§6.6), and the counterexample is a malformed-input test (§8). |
| 2 | State one arithmetic convention; equality goals by two refutations; represent `Void` explicitly. | New §6.3: the convention table, used by both the implementation and the proof. `Void` is a goal constructor whose meaning is `Void`. |
| 3 | Conversion only justifies quoting; turning `Nat.leq a b = False` into `b < a`, `&&` into two facts, `Not (a <= b)` and `=` into inequalities are logical steps that need proofs. | New §6.4: stage 1 emits applications of proved **bridge lemmas** (`Nat.leqFalse`, `Bool.andLeft`/`andRight`, `Nat.leAntisym`, two small new ones), named with their files. Invariant: every input constraint is justified by a checked proof or a proved normalisation rule. |
| 4 | `3 * x` and `x * 3` aren't convertible, so one `Scale` node can't quote both. | Confirmed: `Nat.mul` recurses on its first argument (`std/core/Data.sw:31-33` **[checked]**), and `x * 3` stays stuck **[run]**. Syntax now has `MulLeft k t` and `MulRight t k`; acceptance tests `x * 3 = x + x + x`, `* 0` and `* 1` on both sides (§6.6, §8). |
| 5 | Nat non-negativity for every Nat atom from stage 1, never for Int atoms; sorted atom environments now. | §6.6: an environment with a `Nat` list and an `Int` list from stage 1; `NatNonneg i` is a certificate input for Nat atoms only. (The prototype already added `0 <= x_i` for its atoms; draft 1 didn't say so.) |
| 6 | Stage 2 is auxiliary atoms with operation relationships, not one unconditional linearisation; `/` and `%` need `k > 0` and a stated Int convention; cheap bounds before splitting; cache. | New §6.7. The environment holds the real source term (`a - b`); each branch's facts follow from a checked operation lemma. Positive literal divisors first; `Int.div` is Euclidean (`std/core/Int.sw:123-135` **[checked]**), equal to floor division for positive divisors. Unconditional bounds (`max`, `min`, `-`) go in before any split; reflected subterms are cached, as Lean does [S19] **[checked]**. |
| 7 | A flat list of multipliers isn't an extensible integer proof language; "completeness can improve without touching the library" is only true for reasoning the checker can already express. | New certificate calculus from stage 1 (§6.6): `Input`, `Combine`, `Divide` (Rust picks the divisor; the checker checks it divides every variable coefficient and rounds the constant **down**), `Split` (`L >= 0` or `-L - 1 >= 0`), `Close`; rows referred to by number, branch rows local to their branch. Rocq's `romega` trace has the same steps [S20] **[checked]**. The completeness claim is qualified (§5). The reviewer's example is a regression test, checked here: gcd tightening alone fails, a split on `y` with `Divide` succeeds **[run: Python]** (§6.6). |
| 8 | Reading computed values needs a contract: recognise arithmetic before forcing; inconclusive conversion; metavariables; proof arguments. | New §6.5. One correction to the review's premise: in our evaluator a stuck definition stays *folded* (`Int.add x y` stays `Int.add x y`, `crates/core/src/value.rs:1197-1203` **[checked]**, **[run]**), so the head isn't lost; but a call that takes some steps can change head (`x - 1` computes to `x + (-1)` **[run]**), so the policy still applies. |
| 9 | The 0.5–5 ms figure is certificate replay only; risks from large literals, shared subterms, proofs consumed by `rewrite`/`J`; optimise allocation before adding trust; a fused checker must still check every coefficient cancels; `native_decide` vs the Rocq VM. | §0, §3, §8 and §9 reworded and extended; no trusted `Int` native; `native_decide` and `vm_compute` described correctly (§4.4). |
| 10 | Gather broadly, emit narrowly; connectivity pruning can drop the contradiction (`h: y < y ⊢ x < 0`). | §6.8: only premises the certificate uses are emitted, renumbered. Connectivity sets the search *order* (goal component first, closed constraints kept, other components next, `Void` goals use everything), never what's excluded. `h: y < y ⊢ x < 0` is an acceptance test. |
| 11 | Failure messages: label what kind of "model" was found; draft 1 misdescribed Lean's message. | §6.8: four labelled outcomes (rational relaxation, integer model of the abstraction, unsupported structure, budget). Lean prints residual constraints and atoms as "a possible counterexample may satisfy the constraints", not a numeric assignment [S21] **[checked]**. |
| 12 | Prior-art corrections (`romega`, Isabelle, `linarith`, Lean's records); soften A vs B. | §4 and §5 corrected, each rechecked where reachable: `romega` replays a trace (`t_omega`, `execute_omega`, `omega_valid`) [S20] **[checked]**; Isabelle's `presburger` calls `Cooper.tac` from `cooper.ML` [S22] **[checked]** (that it works by theorem-producing conversions **[cited]**, the file wouldn't load); `linarith` runs on ℕ, ℤ and ordered rings, incomplete on ℤ, simplex by default [S8] **[checked]**. The case for A is now the small proved checker separate from search, not speed. |
| 13 | `auto` fallback needs a failure policy; cite Lean's `decreasing_trivial_pre_omega`. | §6.9 and D547: eligibility check, smaller deterministic budget, no metavariable solving, ordinary failure, no re-entry. Lean precedent [S23] **[checked]**. `omega only [facts]` noted as a later addition. |
| 14 | First milestone: a complete small vertical slice, with acceptance cases and malformed-certificate tests. | §8 rewritten around it; the review's acceptance table is the milestone's done criteria. |

**Where this draft differs from the review**, in small ways (details in the sections named):

- **Rounding (§6.6).** The review says truncating the constant "is wrong". It isn't unsound:
  rounding toward zero gives a weaker row (`2x - 1 >= 0` divided by 2 becomes `x >= 0`), which
  is still true; it just throws away the strengthening the rule exists for. Rounding *up* would
  be unsound. Floor is the right rule either way, and the test checks that the checker floors.
- **Lost heads (§6.5).** As above: the specific worry, `Int.add x y` unfolding to an anonymous
  stuck match, doesn't happen here, because stuck case trees stay folded. Head changes after
  partial computation do happen, so the contract stays.
- **Dimension (§6.6).** The counterexample is right for a checker that sizes vectors by `n`;
  the prototype doesn't, so draft 1's checker wasn't unsound, only unspecified. We drop `n`
  anyway, as the review's third option suggests.

## 0. Summary

- **The problem.** AoC proofs spend a third of their lines on small facts like "`id <= last.to`
  and `last.to + 1 < r.from`, so `id < r.from`", each written as a chain of `Nat.leTrans`,
  `Nat.addOne`, `Nat.leqFalse` and `Nat.leMaxRight` calls (§1). Lean users write `omega`.
- **The idea.** Linear arithmetic over whole numbers is decidable, and for the kind of goal
  above, a proof that the facts can't all hold together is mostly a list of multipliers: add
  the facts up, each times its multiplier, and the unknowns cancel, leaving something false
  like `0 <= -1` (Farkas's lemma, for the rational version). Whole numbers sometimes need two
  more steps: divide a fact by a number and round down, and split into two cases. Finding
  the steps is search; checking them is arithmetic. Search goes in the compiler (untrusted,
  in Rust), checking goes in the library (a Stitchwort function the kernel runs).
- **What the user writes.** `omega` where a proof is expected; `omega [e1, e2]` to add facts
  that aren't in scope by name (the result of a lemma). It considers every arithmetic
  hypothesis in scope, including the equations `match e: …` and `if h: …` put there, and the
  emitted proof mentions only the ones it used (§6.1, §6.8).
- **What the kernel sees.** `Omega.prove env facts goal cert rfl proofs`: the atoms, the
  facts and goal as syntax trees, the certificate, `rfl` for "the checker says yes", and the
  facts' proofs, some wrapped in small bridge lemmas (`Nat.leqFalse …`). Its type computes to
  the goal, so the kernel needs nothing new (§6.4, §6.6).
- **Cost to check:** measured with a prototype, *replaying* a certificate costs 5,600 to
  55,000 evaluation steps on the realistic examples (0.5 to 4 ms, elaboration and kernel
  together), against 131 ms for today's slowest AoC proof declaration (§3). A whole `omega`
  also pays for reading the goal, the search, conversion of the goal against the syntax tree,
  and the bridge lemmas; those aren't measured yet, and finding out is part of the first
  milestone (§8).
- **Cost to build:** a library module (syntax trees, meanings, the certificate checker, and
  the soundness proof, perhaps 500 to 800 lines) and an elaborator module (reading goals,
  bridge proofs, the search, messages; perhaps 1,000 to 1,500 lines of Rust)
  **[inferred]**.
- **Recommendation:** build it as option A (§5), first as a complete vertical slice for
  `Nat` with `+`, literal `*` on either side, `<=`, `<`, `=`, `Void`, Boolean hypotheses, and
  the full certificate calculus (§8); then the operation relationships (`-`, `max`/`min`,
  `if`, `/` and `%` by literals) and `Int`; then `Bool`-equation goals and, if D547 says so, the
  `auto` fallback.

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
  same only if the type checker's own test (conversion) says so (§6.5).
- **Row:** a fact written as `0 <= c + a1*x1 + a2*x2 + …` with whole-number (`Int`) `c` and
  `a`s. Every fact and the goal's negation become rows by one fixed convention (§6.3).
- **Certificate:** a short derivation over rows: combine rows with natural-number
  multipliers, divide a row by a number and round down, split into two cases, and finish each
  case with a row whose unknowns have all cancelled and whose constant is negative (§6.6).
  When only combining is needed, it's the classic **Farkas certificate**: one multiplier per
  fact.
- **Tightening (the `Divide` step):** a step only whole numbers allow: from `2 * x <= 3`,
  divide by 2 and round down to `x <= 1`. Without it, `2 * x = 1` can't be refuted, because
  `x = 1/2` satisfies it.
- **Bridge lemma:** a proved theorem that turns a hypothesis in its source form into the form
  the checker reads, such as `Nat.leqFalse: Nat.leq d n = False -> n < d` (§6.4).
- **Proof by reflection:** write the decision procedure (here, the certificate checker) as an
  ordinary function returning `Bool`, prove once that `True` means the goal holds, and prove
  each goal by running the function. Stitchwort already does a small version of this:
  `auto`'s proof of a closed fact is `Decidable.fromYes d Trivial`, which the kernel checks by
  running `d` (`crates/elab/src/auto.rs:9-23` **[checked]**).
- **Reify (quote):** turn a goal the compiler sees (a value, like `Nat.leq (Succ id) r.from =
  True`) into a syntax tree in the language (`Lt (V 0) (V 2)`) whose meaning computes back to
  it. Quoting is justified by computation alone; anything that needs a logical step goes
  through a bridge lemma instead.

## 3. What we ran

A prototype of the checker, in the scratch file `omega1.sw` (about 120 lines). It is a
stage 1 checker with flat multipliers and no soundness theorem: `Sound` is passed in as a
hypothesis, so the kernel does everything it would do to *replay a certificate* except check
the one-off proof of `Sound`. The important parts **[run]**:

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

-- Linear forms `c + a1*x1 + a2*x2 + …` over Int. Adding two forms keeps the longer
-- coefficient list, and `V i` has a list of length i + 1, so no coefficient is ever dropped.
-- Each fact becomes `0 <= form`; the goal's negation too; plus `0 <= x_i` for i < n;
-- `check` multiplies, adds, and asks "all coefficients 0, constant < 0?".
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

The last line is what `omega` would elaborate to, for a flat certificate. The kernel checks it
by computing `check … = True` (the `rfl`) and by comparing the type of `sound …`, which
computes to `Nat.leq (Succ id) rFrom = True`, with the goal.

In the prototype, `n` only says how many `0 <= x_i` rows to add (`atomsNonneg n`); those rows
are true for any environment, since every entry is a `Nat`, so the prototype's `Sound` is
true as stated (reading `omega1.sw` **[inferred]**). Draft 2 still drops `n` (§6.6).

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

**What these numbers cover.** Certificate replay, plus the kernel's comparison of the quoted
goal with the real one, for hand-written syntax and flat multipliers. Not covered: reading
the goal, the search, bridge lemmas, `Divide` and `Split` steps, large literal coefficients,
and a proof that is later taken apart by `rewrite` or `J` (§9). So the measurements support
"small certificate replay looks cheap", not yet "a whole `omega` costs 0.5 to 5 ms".

Two findings beyond the numbers:

1. **The quoted tree has to mirror the goal's shape exactly.** My first `chain10` wrote the
   right side as `Add (V 9) (Add (Scale 2 (V 9)) (Lit 7))`, which means `x9 + (2 * x9 + 7)`;
   the goal was `(x9 + 2 * x9) + 7`. The kernel refused it: "expected `Nat.leq (x0 + (x0 + (x0
   + 0))) (x9 + (x9 + (x9 + 0)) + 7) = True`, but this has type `Nat.leq … (x9 + (x9 + (x9 + 0)
   + 7)) = True`" **[run]**. So a quoting mistake is a type error, never a wrong proof, and
   the reifier must read the goal's own tree (§6.5). It also shows `3 * x0` evaluating to
   `x0 + (x0 + (x0 + 0))` (docs/core.md "Numbers": `k * x` unfolds `k` times **[checked]**).
   The other order doesn't compute: `x * 3` stays `x * 3`, since `Nat.mul` recurses on its
   first argument (`std/core/Data.sw:31-33` **[checked]**; `x * 3 = x + x + x := rfl` is
   refused **[run]**), so the syntax needs a node for each order (§6.6).
2. **Growth is about quadratic in the number of unknowns** for these chains: with `m` dense
   rows of `n` coefficients, combining costs about `m * n` operations, and the chains have `m`
   close to `n`. Harmless at AoC sizes (3 to 10 unknowns); other costs (§9) aren't
   quadratic in the same way.

Not run: the soundness proof, the search, `Divide`/`Split` steps, and a checker that also
searched (option C, §5).

## 4. How other systems do it

### 4.1 Summary

| System | What it decides | How the proof is checked | Trusted extra code |
|---|---|---|---|
| Lean 4 `omega` | linear `Nat`/`Int` facts, `/` `%` by literals, `-`, `max`/`min`, `∧ ∨ ¬ ↔` | the tactic builds a proof term from lemmas, following recorded `Justification`s | none |
| Lean `decide` | any closed decidable proposition | kernel evaluates the `Decidable` instance | kernel GMP numbers |
| Mathlib `linarith` | linear facts over ordered fields; also runs on ℕ, ℤ and ordered rings, incomplete on ℤ | simplex finds multipliers; `ring` normalisation checks the sum | none |
| Lean `grind` (2025) | includes linear integer arithmetic, complete up to a step limit | own proof terms | none |
| Rocq `lia` / `lra` (micromega) | linear integer / real arithmetic | **reflection**: an oracle finds a certificate, a Rocq checker checks it | none |
| Rocq `romega` (deprecated 8.9) | as `omega` | **reflection**: the OCaml omega's trace is replayed by a proved Rocq function | none |
| Isabelle `presburger` | full Presburger arithmetic (Cooper) | ML implementation producing theorems; a separate verified-by-reflection Cooper exists | none |
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
`assumption | tidy | combine | combo | bmod`, the last for Pugh's balanced-modulus step on
equalities with no ±1 coefficient) and, once it finds a contradiction, turns that into a proof
term applying lemmas such as `Constraint.combine_sat'` and `tidy_sat`; `decide` is used only for
small closed side facts [S2] **[checked]**. The linear forms appear in the proof as data, and
the lemmas work on whole linear combinations, so its proofs are much more compact than chains
of elementary `+` rewrites. It is close to option B below.

When it first meets an atom it adds cheap unconditional facts: `0 <= a` for a `Nat` cast,
`min a b <= a` and `min a b <= b`, `a <= max a b` and `b <= max a b`, bounds for `x / k` and
`x % k`, and a recorded dichotomy for `a - b` (split later); it caches each visited expression
with its linear combination, and atoms "up to defeq" (`analyzeAtom`, `Cache`, `State.atoms`
in `OmegaM.lean` [S19] **[checked]**). We copy all of these (§6.7, §6.5).

The algorithm follows Pugh's Omega test [S4] **[cited]**: eliminate equalities (with
balanced mod when no coefficient is ±1), then eliminate unknowns one by one by
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
goals to `Z` first [S6] **[checked]**. The manual presents linear refutations plus cutting
planes as a complete proof principle for linear integer arithmetic, with the bounded case
splits as an extra search strategy [S6] **[cited, from the review]**.

### 4.4 Rocq `romega`: a richer certificate, replayed

Rocq's earlier `omega` was partial; its reflective variant `romega` was deprecated in 8.9:
"Use lia instead" [S7] **[checked]**. Draft 1 listed `romega` as running the whole search in
the object language; that was wrong. Its reflective core (`ReflOmegaCore.v`, Pierre Crégut,
2001) defines a trace type, "steps as they can be found in the trace coming from the decision
procedure Omega":

```
Inductive t_omega : Set :=
  | O_BAD_CONSTANT : idx -> t_omega
  | O_NOT_EXACT_DIVIDE : idx -> int -> t_omega
  | O_DIVIDE : idx -> int -> t_omega -> t_omega
  | O_SUM : int -> idx -> int -> idx -> t_omega -> t_omega
  | O_MERGE_EQ : idx -> idx -> t_omega -> t_omega
  | O_SPLIT_INEQ : idx -> t_omega -> t_omega -> t_omega.
```

and proves `omega_valid : forall tr, valid_list_hyps (execute_omega tr)` [S20]
**[checked]**. That is our certificate calculus (§6.6) almost step for step: combine two rows
(`O_SUM`), divide (`O_DIVIDE`), split (`O_SPLIT_INEQ`), close on a bad constant. It is
precedent that a richer replayed certificate is practical.

### 4.5 Others

- **Mathlib `linarith`**: "will run over concrete types like ℕ, ℚ, and ℝ, as well as abstract
  types that are instances of `CommRing`, `LinearOrder` and `IsStrictOrderedRing`"; on ℤ it
  "will fail to prove `False` on some unsatisfiable problems"; the default oracle is the simplex
  algorithm; the sum is checked by `ring` normalisation, not reflection [S8] **[checked]**.
- **Lean `decide`**: the kernel evaluates the `Decidable` instance; the kernel has GMP numbers
  and overrides `Nat.add`, `sub`, `mul`, `ble`, `beq` and others [S9] **[checked]**, much as
  Stitchwort's kernel has native `Nat.add`, `Nat.leq` and others (docs/core.md "Numbers"
  **[checked]**). Stitchwort's `auto` is already a `decide` for closed goals (§2).
- **Faster evaluation, and what it trusts.** Lean's `native_decide` compiles the decision
  procedure and trusts the compiled code through an axiom (`Lean.ofReduceBool`), so it widens
  the trusted base **[cited, from the review and general knowledge]**. Rocq's `vm_compute` (Grégoire and Leroy's compiled strong reduction
  [S17] **[cited]**) is a faster evaluator *inside* the checker, part of the trusted kernel
  but with no new axiom. For `omega` neither is needed now: an untrusted fast runner may speed
  up search and the elaborator's pre-check, and the kernel still checks the result (§9).
- **Lean `grind`** has a "model-based" linear integer arithmetic solver, "complete for LIA";
  Lean's `lia` is now a thin wrapper around it [S10] **[checked]**. A step limit bounds it, so a
  bounded run can still fail on a true goal **[cited, from the review]**. A good reference for a
  later search.
- **Isabelle**: the `presburger` method is `Cooper.tac`, from `Tools/Qelim/cooper.ML`, an ML
  implementation of Cooper's algorithm ("Cooper's algorithm for Presburger arithmetic") [S22]
  **[checked]**; it produces its theorems by conversions inside the LCF kernel **[cited, from
  the review; the ML file didn't load]**. Separately, Chaieb and Nipkow verified Cooper's
  algorithm and ran it by reflection; that version was "one to two orders of magnitude faster"
  than proof by tactics [S11] **[cited]**. Draft 1 conflated the two.
- **Agda, Idris 2**: reflective ring solvers in the libraries (`Data.Nat.Solver` on
  `Algebra.Solver.Ring.Simple` [S12] **[checked]**; Idris's `Algebra.Solver.Ring` [S13]
  **[cited]**). No `<=` solver found in either library **[cited]**.
- **Dafny, F\***: arithmetic goes to Z3, which is trusted; nonlinear arithmetic is undecidable
  and unstable, so F\* advises turning it off and stepping by hand [S14] **[checked]**.
- **Literature:** Boutin introduced proof by reflection in Coq (1997) [S15] **[cited]**;
  Chlipala's CPDT chapter "Reflection" is the readable account: "such a proof is checked by
  running the decision procedure" [S16] **[checked]**.
- **Theory:** Presburger arithmetic (whole numbers with `+`, `<=`, quantifiers) is decidable,
  but the full theory needs doubly exponential time in the worst case (Fischer and Rabin, 1974
  [S18] **[cited]**). Goals with no quantifiers, which is all `omega` takes, are integer linear
  programming: NP-complete in general **[unverified]**, fast on the sizes here.

### 4.6 What to take

From Rocq: the split between untrusted search and a small checked certificate, and from
`romega`, a certificate with combine, divide and split steps. From Lean: the fragment
(including `-`, `max`/`min`, `/` and `%` by literals), the cheap unconditional facts added per
atom, caching, gathering facts from the context, the name, and accepting incompleteness (no
dark or grey shadows). From Stitchwort itself: `auto`'s "run a `Bool` function in the kernel"
pattern, which is already trusted and fast for numbers.

## 5. Options

### (A) Certificate checker by reflection (recommended)

The elaborator quotes the goal and the facts, searches (Fourier–Motzkin, in Rust), and emits
`Omega.prove … cert rfl proofs`. The library holds the checker and its soundness theorem.
**Kernel work per use:** replay the certificate (measured for small flat ones, §3) and convert
the quoted goal. **Trusted code added:** none. **Soundness proof:** about rows (adding,
scaling, dividing with floor and splitting preserve truth), not about the search.
**Completeness:** whatever the Rust search finds. Better search needs no library change *as
long as it emits steps the checker already understands*; that is why the calculus includes
`Divide` and `Split` from the start (§6.6). A new kind of step (say, a dark-shadow argument
that can't be written with these) would change the checker and its proof.

**The case for A** is the small, independently proved checker, kept apart from the search: a
search bug can lose a proof or waste time, never prove something false, and the trusted
statement is one theorem a reviewer can read. Speed is a hoped-for benefit, not yet a
measured one (below).

### (B) Proof built from lemmas (Lean's way)

The elaborator searches the same way and then writes the proof from lemmas. Done naively,
every rearrangement of a sum is a chain of `Nat.addComm`/`Nat.addAssoc` rewrites whose hidden
arguments restate the sums, and proof-check-speed.md found that hidden arguments are 81% of the
nodes in the slow AoC proofs and that checking time follows term size
(`docs/proposals/proof-check-speed.md`, "Causes" 1 **[checked]**). But B needn't be naive:
Lean's version uses lemmas about whole linear combinations (§4.2), and a B for Stitchwort
could too. **Whether A checks faster than a good B is an unmeasured guess** **[inferred]**. B
needs no soundness theorem, but every new kind of reasoning needs new proof-producing code in
the (untrusted, but bug-prone) elaborator, and the proofs are bigger terms.

### (C) The whole decision procedure in the language

As (A), but the search itself is a Stitchwort function the kernel runs (as Chaieb and
Nipkow's verified Cooper does in Isabelle, §4.5). No Rust search; but the kernel runs
Fourier–Motzkin on every check, twice (the elaborator evaluates too, proof-check-speed.md
"fourChecked … computed by both" **[checked]**). Eliminating one unknown pairs every lower
bound with every upper bound; for day 5's sizes (3 to 6 unknowns, 5 to 10 facts) that's perhaps
tens to hundreds of combinations, each costing what a whole stage 1 replay costs in §3:
**[inferred]** 10 to 100 times the checking cost, and the soundness proof must then cover the
search (termination, the elimination order), and every improvement to the search is a library
change with proofs. Not recommended; (A) can always grow a small in-language fallback.

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
| Kernel cost per use | replay measured small; rest unmeasured | unmeasured; grows with term size | 10–100× A (guess) | n/a |
| Proof term size | small: trees + certificate | larger | small | n/a |
| One-off proof work | soundness of the checker | none | soundness of the search | lemmas |
| Search improvements | Rust only, within the calculus | Rust only | library + proofs | n/a |
| Precedent | Rocq `lia`, `romega` | Lean `omega` | Isabelle's verified Cooper | — |

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
- **Facts considered:** every hypothesis in scope whose type is a fact in the fragment:
  parameters, `let`s, and what `match e: …` and `if h: …` add, including `Nat.leq a b = False`,
  `(p && q) = True`, `Not (a <= b)` and `a = b`, each turned into rows by a bridge lemma (§6.4).
  Others are ignored. Only the facts the certificate uses appear in the proof (§6.8).
- **`omega [e1, e2]`** adds facts by term, for a lemma's result that isn't in scope:
  `omega [topGe (Nat.max z r.to) rs]`. It's the same as `let`-binding them first.
- In a `calc` step (`_ <= r.from := omega`) or a `rewrite` (`rewrite (omega: a + b - b = a)`),
  as any proof term.
- **Later:** `omega only [h1, h2]`, using just the listed facts, for control over
  dependencies and speed. Not needed for the first milestone.

### 6.2 The fragment, by stage

| Construct | Stage | How |
|---|---|---|
| `<=`, `<`, `=` between `Nat` expressions, in goal and facts; `Void` goal | 1 | rows by the convention (§6.3); `=` goal by two refutations |
| `Nat.leq a b = True` / `= False`, `(p && q) = True`, `Not (a <= b)`, `Not (a < b)`, `a = b` as facts | 1 | bridge lemmas (§6.4) |
| `+`, `Succ`, numbers, `k * x` and `x * k` for a number `k` | 1 | `Add`, `Lit`, `MulLeft`, `MulRight` (§6.6) |
| any other `Nat` term (`List.length xs`, `r.to`, `x * y`, a call, and `a - b` until stage 2) | 1 | a Nat atom, with `0 <= atom` available |
| tightening and small case splits | 1 | `Divide` and `Split` certificate steps (§6.6) |
| `a - b` (truncated) | 2 | auxiliary atom for the real term `a - b`; cheap bound `a - b <= a`; split `b <= a` with `(a - b) + b = a`, or `a < b` with `a - b = 0` (§6.7) |
| `if c then x else y` on a comparison, so `Nat.max`, `Nat.min` | 2 | cheap bounds first (`a <= max a b` …), split on `c` if needed |
| `x / k`, `x % k` for a positive number `k` | 2 | auxiliary atoms with `x = k * (x / k) + x % k`, `x % k < k`: no split |
| `a != b` as a fact; `(p \|\| q) = True` | 2 | split |
| `Int` (`+`, `-`, negation, `<=`, `<`, `=`), `Nat.toInt` | 2 | Int atoms (no non-negativity), already in the environment's shape from stage 1 |
| goals that are `Bool` equations of comparisons (`(p && q) = (r \|\| s)`) | 3 | split on each comparison |

Out of scope, as in Lean: `x * y` with both unknown (an atom, no laws), `/` and `%` by an
unknown, `Nat.pow` with an unknown exponent, quantifiers in facts (`(id: Nat) -> covered rs id =
True -> id < b` is used by applying it, `omega [b id h]`).

### 6.3 The arithmetic convention

Every fact becomes one or two rows `0 <= form` by this table, and nothing else. For integer
meanings `A` and `B` of the two sides (all subtraction here is `Int` subtraction, never
`Nat.sub`, which stops at zero):

| Proposition | Row(s): this must be `>= 0` |
|---|---|
| `A <= B` | `B - A` |
| `A < B` | `B - A - 1` |
| `Not (A <= B)` | `A - B - 1` |
| `Not (A < B)` | `A - B` |
| `A = B` | both `B - A` and `A - B` |
| a `Nat` atom `x` | `x` |

**Goals.** The checker refutes the goal's negation together with the facts: a `<=` or `<`
goal adds the "Not" row; an **equality goal** is proved by two refutations, one adding
`Not (A <= B)`'s row and one adding `Not (B <= A)`'s, assembled by `Nat.leAntisym`
(`std/Nat/Arith.sw:16` **[checked]**). A **`Void` goal** is a `Goal` constructor whose meaning
is `Void`; it adds no row, so the facts alone must be contradictory. (The alternative, a
separate `refute` theorem, does the same with one more name; one theorem with a `Void`
constructor is simpler.)

### 6.4 From source to constraints: quoting and bridge lemmas

Two different operations happen between a hypothesis and a row, and draft 1 blurred them:

1. **Quoting**: building syntax whose meaning *computes to* the source. Justified by
   conversion alone: the kernel compares `Fact.holds env f` with the hypothesis's type.
2. **Normalising**: replacing a proposition with a logically equivalent one. `Nat.leq a b =
   False` and `b < a` don't compute to each other; nor do `(p && q) = True` and the two facts.
   These need proofs.

Stage 1 does normalising **in the emitted term, with proved bridge lemmas**, and passes the
resulting arithmetic proofs to the checker, so the checker stays small. (The other sound way,
keeping `Bool` structure in the syntax and proving the translation inside the soundness
proof, makes the checker bigger; it may suit stage 3's `Bool`-equation goals.)

| Source hypothesis | Bridge | Where **[checked at `bc1cf9ee`]** |
|---|---|---|
| `Nat.leq a b = False` | `Nat.leqFalse a b e : b < a` | `std/Nat/Arith.sw:85` |
| `(p && q) = True` | `Bool.andLeft p q e`, `Bool.andRight p q e`, then each part recursively | `std/List/Sort.sw:36, 40` (to move to `core` or `Std.Omega`'s imports) |
| `Not (a <= b)` | new `Bool.falseOfNotTrue: Not (x = True) -> x = False`, then `Nat.leqFalse` | none exists today (searched `std` for `Not (… = True) ->`) |
| `Not (a < b)` | the same; `b < Succ a` computes to `b <= a` | as above |
| `a = b` (fact) | new `Nat.leOfEq: a = b -> a <= b` (by `J` from `Nat.leRefl`), both directions | `Nat.leRefl` at `std/core/Division.sw:33`; no `leOfEq` today |
| `Nat.leq a b = True`, `a <= b`, `a < b` | none: quoting alone | — |
| equality goal | `Nat.leAntisym a b (prove …) (prove …)` | `std/Nat/Arith.sw:16` |

**The invariant**, for the implementation and its tests: *every input row is justified by a
checked proof (a hypothesis, possibly through a bridge lemma) or by a proved normalisation
rule inside the checker (the convention of §6.3, `NatNonneg`, and in stage 2 the operation
lemmas of §6.7) whose source proposition is faithfully quoted.* Checking only that the quoted
goal means the expected type isn't enough; the facts and the generated rows need the same
treatment, and the elaborator's pre-check (§6.8) type-checks the whole emitted term.

### 6.5 Reading goals: the reification contract

The elaborator has the goal as a value, already computed: `Range.contains r id` has unfolded
to its `&&` of two `Nat.leq`s, `Nat.max a b` to a stuck `if`, `3 * x` to `x + (x + (x + 0))`
(§3). That helps: user definitions that are really arithmetic (`Range.size`,
`Range.contains`) are seen through with no `simp` step, which Lean needs (kim-em's `simp only
[…] at *; omega`, aoc-day05-community.md:437 **[checked]**). But computing can also change
the shape the reifier wants to see. The contract:

1. **Recognise before forcing.** With glued values on (SW-257, off by default today:
   docs/core.md "Glued calls" **[checked]**), a call is kept as the call until something looks
   inside. The reifier first checks whether a call's head is a known arithmetic definition
   (`Nat.add`, `Nat.mul`, `Nat.leq`, later `Int.add`, `Int.neg`, `Int.mul`, `Int.leq`,
   `Nat.sub`, `Nat.max`, …) and only forces calls it doesn't recognise, to look for arithmetic
   inside wrappers. Unfolding is selective: a recognised head is never unfolded.
2. **Stuck calls keep their heads; partial steps may not.** In our evaluator a case tree that
   can't take a step leaves its definition folded: `Value::Neutral(Head::Def(id), spine)`
   (`stuck_tree`, `crates/core/src/value.rs:1197-1203` **[checked]**). So `x + y` on `Int` stays
   `Int.add x y` (a failed `rfl` on `x + y = y + x` shows no different computed form
   **[run]**). But a call that takes some steps first can come out under another head: `x - 1`
   on `Int` computes to `x + (-1)` **[run]** (`Int.sub` is a plain definition,
   `std/core/Int.sw:38` **[checked]**), and `Int.add (OfNat m) (NegSucc n)` steps to
   `Int.subNatNat …` (`std/core/Int.sw:31-35` **[checked]**). The reifier recognises the heads
   that partial computation of supported operations can produce, or treats the result as an
   atom (safe, may lose a proof).
3. **The tree mirrors the value's shape.** It reads the value's own shape, `k + x` and all,
   and the meaning functions use the same definitions the surface syntax does, with
   `MulLeft`/`MulRight` keeping the order of `*` (§6.6).
4. **Atoms: fast path, then bounded conversion.** Two subterms are one atom if they are the
   same syntax (or the same hash); otherwise the elaborator tries the real conversion check
   with a budget. "Not shown equal" (different, or out of budget) keeps them as **separate
   atoms**: that may lose a proof, never makes a wrong one. Conversion itself is transitive;
   only the bounded check can be inconclusive.
5. **Metavariables.** Atom comparison never solves a metavariable. A goal or fact still
   containing unsolved metavariables is quoted with them as part of atoms only if they occur
   inside an atom; if the goal's arithmetic structure itself depends on one, `omega` reports
   that the goal isn't known yet. (The `auto` fallback is stricter, §6.9.)
6. **Proof arguments.** There is no definitional proof irrelevance (docs/core.md:139
   **[checked]**), so `get xs i h1` and `get xs i h2` are one atom only if conversion says so
   (it may, if `get` ignores its proof); erasure making their run-time code equal is no
   reason. Otherwise they are two atoms, and a user needing them equal supplies an equation.
7. **Cache.** Each visited subterm is cached with its linear form, not just atom identities,
   as Lean's `omega` does [S19] **[checked]**, so a shared subexpression is read once.

Before emitting the term, the elaborator checks the whole emitted term, quoting and bridges
included, so a reifier bug is reported as an internal error naming `omega`, not as a confusing
type mismatch.

### 6.6 The library side: `Std.Omega`

Shapes, not final code:

```
namespace Std.Omega

-- Sorted environments from stage 1, though Int atoms arrive in stage 2.
type Env = MkEnv (nats: List Nat) (ints: List Int)

type NTerm =                                    -- Nat-valued syntax
  | NV (i: Nat) | NLit (n: Nat) | NAdd (a b: NTerm) | NSucc (a: NTerm)
  | MulLeft (k: Nat) (t: NTerm)                 -- means k * t   (unfolds: `3 * x`)
  | MulRight (t: NTerm) (k: Nat)                -- means t * k   (stuck: `x * 3`)
type ITerm = …                                  -- Int-valued syntax, stage 2 (IV, IAdd, INeg, ToInt …)

type Fact = Le (a b: NTerm) | Lt (a b: NTerm) | Eq (a b: NTerm) | NotLe … | NotLt … | (Int forms, stage 2)
type Goal = GLe (a b: NTerm) | GLt (a b: NTerm) | GVoid      -- equality goals: two GLe proofs

-- Rows `0 <= c + Σ a_i * nat_i + Σ b_j * int_j`. Coefficient lists grow to cover every
-- index mentioned; adding two rows keeps the longer list. No separate dimension.
type Row = MkRow (c: Int) (nat: List Int) (int: List Int)

type Step =
  | Input (f: Nat)                          -- fact number f, or the negated goal
  | NatNonneg (i: Nat)                      -- 0 <= nat atom i: true for any env
  | Combine (terms: List (Pair Nat Nat))    -- Σ k * row r, natural k, each r an earlier row
  | Divide (r: Nat) (d: Nat)                -- see below
type Cert =
  | Close (r: Nat)                          -- row r: every coefficient 0, constant < 0
  | Then (s: Step) (rest: Cert)             -- add one row, continue
  | Split (l: Row) (left: Cert) (right: Cert)    -- left adds l >= 0, right adds -l - 1 >= 0

def check (facts: List Fact) (goal: Goal) (cert: Cert): Bool
theorem prove (env: Env) (facts: List Fact) (goal: Goal) (cert: Cert)
    (ok: check facts goal cert = True) (hs: Facts.holds env facts): Goal.holds env goal
```

**The rules the checker applies.** Rows are numbered in the order they're made; a reference
must be to an existing row, else the check fails. `Split`'s branches each start from the rows
available at the split, plus their own new row; rows made inside one branch are invisible to
the other and to anything after it (the tree structure gives this for free).

- `Combine`: multipliers are natural numbers (`Nat`), so a sum of non-negative rows is
  non-negative.
- `Divide r d`: for row `c + Σ a_i x_i >= 0`, check `d > 0` and that `d` divides **every**
  variable coefficient (Nat and Int); the new row is `floor(c / d) + Σ (a_i / d) x_i >= 0`.
  Rust chooses `d` (usually the gcd); the checker needn't compute a gcd. The constant is
  rounded **down** (`Int.div` by a positive divisor, which is Euclidean and so floor,
  `std/core/Int.sw:123-135` **[checked]**; its laws `Int.divAddMod`, `Int.modNonneg`,
  `Int.modLtAbs` exist **[checked: grep]**). Example: `2x - 1 >= 0` divided by 2 is
  `x - 1 >= 0`. Rounding toward zero would give `x >= 0`: still true, but it loses exactly the
  strengthening the rule exists for. Rounding up would be unsound.
- `Split l`: for any integer value of `l`, `l >= 0` or `-l - 1 >= 0`; the checker needs no
  test, only that both branches close.
- `Close r`: every coefficient of row `r` is zero and the constant is negative. A fused checker
  that accumulates rows as it goes must still check that every coefficient cancels, not only
  the constant.

**The soundness contract.** `prove` holds for **every** environment, whatever the lengths of
its lists: an index past the end means 0 (`List.getOr 0`), which is a fine meaning; what
mustn't happen is a coefficient being dropped, and the row representation never drops one,
because rows grow to cover every index the syntax mentions. So `check` takes no `n`, and the
theorem needs no `env` length premise. `NatNonneg i` is valid for every `i` because every
`nats` entry is a `Nat`; there is no such step for `ints`. The review's counterexample,
`env = MkEnv [1] []`, no facts, goal `GLe (NV 0) (NLit 0)` (`1 <= 0`, false), with
certificate `Then (Input 0) (Close 0)`, must be **rejected**: the negated goal's row is
`x - 1 >= 0`, whose `x` coefficient isn't zero. It is a malformed-input test (§8).

**What the proof needs** **[inferred]**:

1. the linear form of a term means the term: `Row.eval env (NTerm.lin t) = Nat.toInt
   (NTerm.eval env t)`, pointwise for every `env`, by induction, from the `Int` ring laws the
   library has (`Int.addAssoc`, `Int.addComm`, `Int.mulComm`, `Int.mulDistribLeft`,
   `Int.toIntAdd`, `Int.toIntMul` and others, `std/Int/Int.sw` **[checked at `bc1cf9ee`]**).
   `MulRight` needs `Int.mulComm`. No function or propositional extensionality is involved:
   every lemma is about values at a given `env`, and the bridges between propositions are
   functions in the directions needed;
2. each row of §6.3 is non-negative when its proposition holds; this needs `Int` order
   lemmas (adding preserves `<=`, multiplying by a non-negative number does). The library
   has `Int.leOfCompare` and `Int.lessOfCompare` (`std/core/Compare.sw:140-152` **[checked]**)
   but no order algebra **[checked: grep `theorem Int.` in `std`]**;
3. a combination with natural multipliers of non-negative rows is non-negative (induction);
4. `Divide`: if `d > 0` divides every `a_i` and `c + Σ a_i x_i >= 0`, then
   `floor(c/d) + Σ (a_i/d) x_i >= 0` (from `Int.divAddMod` and the bounds on the remainder);
5. `Split`: `l >= 0` or `-l - 1 >= 0`, by computing `Int.leq`, so a `match` on a `Bool`, not
   classical logic;
6. a row whose coefficients are all zero means its constant, and a negative constant isn't
   non-negative;
7. the goal's negation: `Nat.leq` computes, so "if the goal failed, its negation holds" is
   also a `match` on the `Bool`.

The checker works over `Int` inside, which the prototype shows is cheap enough even though
`Int` has no natives (decision K1, docs/core.md "Numbers" **[checked]**). No trusted `Int`
native is proposed (§9).

**A regression for the calculus.** The review's example, checked here **[run: Python,
`omega-d2/fm.py` in the scratchpad]**:

```
x y: Nat
1 <= 2*x + 3*y      2*x + 3*y <= 4      2*y <= 3*x + 1      3*x <= 2*y + 2
```

No whole-number solution (`x <= 2`, `y <= 1`; all six pairs fail), but `x = y = 1/2` satisfies
all four. Fourier–Motzkin with gcd tightening after every step, eliminating either variable,
leaves the other in `[0, 1]` with no contradiction. Splitting on `y` (`y <= 0` or `y >= 1`) and
then eliminating `y` first with tightening closes both branches; eliminating `x` first in a
branch doesn't. So the certificate needs `Split`, `Combine` and `Divide`, and the search must
choose its elimination order with care. It also shows that per-row gcd tightening doesn't make
real-shadow elimination complete; it is an acceptance test for the milestone (§8).

**Incompleteness, concretely.** The checker can express a refutation for every unsatisfiable
problem in principle (combinations plus division are complete for linear integer arithmetic,
§4.3); what's incomplete is the search. A purely rational search would miss `2*x = 1`;
negating goals over the integers already gives some rounding for free (`2*x <= 3` proves
`x <= 1`, because the negation `x >= 2` contradicts it rationally), and `Divide` plus small
splits cover more. Lean's balanced-mod step for equalities without a ±1 coefficient (§4.2)
is a later search improvement that `Divide` can already certify **[inferred]**.

### 6.7 Stage 2: auxiliary atoms with operation relationships

Stage 1's lemma "the linear form means the term" can't extend to `-`, `if`, `/` and `%`: no
single linear form over the original atoms means `a - b`. Instead each such subterm becomes an
**auxiliary atom whose environment entry is the real source term** (the elaborator puts
`a - b` itself in `env`; no `Exists` or choice needed), and the checker may add rows that
follow from a **proved operation lemma** about that atom:

| Atom (env holds) | Unconditional rows (no split) | Split, each side from a lemma |
|---|---|---|
| `t = a - b` (Nat) | `t <= a` (`Nat.subLe`, `std/Nat/Arith.sw:47`) | `b <= a` and `t + b = a` (`Nat.addSubCancel`, `:80`), or `a < b` and `t = 0` |
| `t = Nat.max a b` | `a <= t`, `b <= t` (`Nat.leMaxLeft`/`Right`, `:428, 432`) | `a <= b` and `t = b`, or `b < a` and `t = a` |
| `t = Nat.min a b` | `t <= a`, `t <= b` (`Nat.minLeLeft`/`Right`, `:440, 443`) | likewise |
| `q = x / k`, `r = x % k`, `k` a positive literal | `x = k*q + r`, `0 <= r`, `r < k` (`Nat.divModEq`, `Nat.modLess`, `:135, 143`) | none needed |
| `if c then y else z` on a comparison | — | `c` and `t = y`, or `Not c` and `t = z` |

(All lemma names **[checked at `bc1cf9ee`]**; draft 1's "`Nat.divMod`" is `Nat.divModEq`.)

- **The search never invents a fact.** A branch's rows come from the operation lemma for the
  atom and the branch's condition, both checked; an unconstrained new unknown with arbitrary
  "branch facts" is exactly what must not happen. In the certificate this is a new step kind,
  so stage 2 does change the checker and its proof, as the review notes; the calculus is
  designed to take it (a `Split` whose branches each start with an operation row).
- **Division needs `k > 0`.** At `k = 0` the bound `r < k` is impossible, so the lemma (and the
  checker rule) take `k > 0` as a premise even though the source syntax already demands a
  non-zero divisor.
- **Int division convention.** `Int`'s `/` and `%` are Euclidean (`0 <= a % d < |d|`,
  `std/core/Int.sw:123-145` **[checked]**); `Int.fdiv`/`Int.fmod` are floor division
  (`std/Int/Basics.sw:49` **[checked]**). For a positive divisor they agree. Stage 2 supports
  positive literal divisors only, where all conventions coincide; negative divisors later, by
  the Euclidean laws.
- **Cheap bounds before splitting.** The first attempt includes the unconditional rows; only
  if it fails does the search split, one atom at a time (Lean does the same for `-` and adds
  the `min`/`max` bounds up front [S19] **[checked]**). This keeps most goals out of the
  exponential branch tree.

### 6.8 The elaborator side

`crates/elab/src/omega.rs` **[inferred]**: gather facts (§6.1); apply bridges (§6.4); quote
(§6.5), keeping an atom table and a subterm cache; turn facts into rows; search; on success,
build the certificate, keep only the facts it uses, and build the term; on failure, report.

**Gather broadly, emit narrowly.** Every arithmetic fact in scope is a candidate. After the
search succeeds, the emitted term keeps only the facts (and atoms) the certificate refers to,
renumbered, which shrinks the syntax, the conversion work, and the proof's dependencies. It
needn't be a minimal explanation.

**Search order, not exclusion.** Facts that share no atom with the goal, directly or through
other facts, can't help prove it *unless they are contradictory on their own*: `h: y < y ⊢
x < 0` holds because `h` is impossible. So connectivity only sets the order:

1. try the facts connected to the goal (with the goal's negation);
2. always include closed rows (no atoms: `0 < 0` and the like);
3. then try each other component on its own for a contradiction;
4. a `Void` goal has no atoms, so step 1 is every fact.

A budget may stop the search before every component is tried; the message then says the
search didn't finish, not that the goal doesn't follow.

**Search.** Fourier–Motzkin with tightening (`Divide`) after each elimination, preceded by
solving equalities, and small-range splits when the real shadow survives (§6.6's example);
simplex if problems grow. Splits on operation atoms (§6.7) only after the unsplit attempt.

**Messages** (`E-OMEGA`). The goal, the facts considered, the atoms (so a user sees that `r.to`
and `Range.to r` were one atom, or that `x * y` was opaque), and one of these, labelled:

- **"a rational model of the relaxation"**: the leftover constraints have a solution in
  fractions. That isn't a counterexample to a `Nat` goal; it says the search's real shadow
  didn't close.
- **"an integer model of the arithmetic abstraction"**: whole-number values for the atoms
  that satisfy every row. Still not a counterexample: atoms like `n * n` or `List.length xs`
  can get values their real meanings can't have.
- **"unsupported structure"**: what was turned into atoms because the fragment doesn't cover it
  (`x * y`, `%` by an unknown, a quantified hypothesis), with the stage that adds it where one
  does.
- **"budget exhausted"**: the search stopped; nothing is claimed.

A true source-level counterexample would need checking the values against the real terms; not
planned. (Lean's message prints the residual constraints and the atom list, "a possible
counterexample may satisfy the constraints", not a numeric assignment [S21] **[checked]**;
draft 1 said otherwise.) For example:

```
[E-OMEGA] omega can't prove `id < r.from`
  facts:  id <= last.to          (i)
          last.from <= r.from    (ok)
  atoms:  id, last.to, last.from, r.from
  an integer model of these facts (it may not be a real counterexample):
          id = 5, last.to = 5, last.from = 0, r.from = 5
  not understood: none
```

The elaborator also runs the checker before emitting the term (it must, to type-check `rfl`),
so the check is computed twice, once by each side, as for `auto` today
(proof-check-speed.md: "computed by both, which is the price of re-checking in the kernel"
**[checked]**). The numbers in §3 already include both.

### 6.9 Interactions

- **`auto` (D547)**: unchanged until explicit `omega` is stable and measured. Then `auto` may
  try `omega` for arithmetic obligations after hypotheses and decision procedures fail. That
  would discharge `[auto ok: i < xs.length]`, the `%` and `/` side conditions and `decreasing`
  obligations from facts in scope, which today need the exact fact in scope. Lean does exactly
  this for well-founded recursion: `decreasing_trivial` falls back to `omega`, and a
  `decreasing_trivial_pre_omega` variant "does not use `omega`, intended to be used in core
  modules before `omega` is available" [S23] **[checked]**. The policy:
  1. **Eligibility**: only an obligation whose type, after computing, is a fact in the
     fragment (or `Void`), checked cheaply before any search.
  2. **Budget**: deterministic (counted steps, not time), smaller than explicit `omega`'s.
  3. **Metavariables**: `auto` obligations are proved after the declaration is elaborated and
     retried in rounds (`crates/elab/src/auto.rs:1-30` **[checked]**); the fallback runs only on
     an obligation with no unsolved metavariables, and never solves one.
  4. **Failure**: running out of budget is an ordinary `auto` failure (today's message, plus a
     note that `omega` was tried), not a new error.
  5. **No re-entry**: while building an `omega` proof, `auto` doesn't call `omega` on the same
     obligation again. This matters for division: an operation lemma's own side condition
     (`k != 0`) mustn't send preprocessing back into the obligation it is solving.
- **`calc` and `rewrite`**: `omega` is a term, so it works as a step's justification or as the
  equation `rewrite` uses (with a type ascription). They remain the tools for everything that
  isn't arithmetic. A proof used by `rewrite` is taken apart by `J`, which may run the
  checker's proof term in new ways; measured in the milestone (§8, §9).
- **`match` and `if h:`**: the facts they add are used automatically, so the common
  `match e: Nat.leq … with | False => Nat.leqFalse …` pattern loses its lemma calls. `omega`
  doesn't remove the need to match on a program's own `if` when the goal mentions what the
  `if` computes (a list, in day 5's `absorb`).
- **Folded and glued values (SW-257)**: §6.5. The emitted term carries the atoms as terms; an
  atom like `rs.foldLeft (m r => Nat.max m r.to) z` is quoted once into `env`. The kernel
  always checks with gluing off (D483, docs/core.md "Glued calls" **[checked]**).
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

(The `True` arm uses two bridges, `Bool.andRight` on `i` and `Nat.leqFalse` on `e`, §6.4.)

**`coveredTop`** (stage 2, for `Nat.max`): 10 lines → 7; the three-step `calc` becomes
`omega [topGe (Nat.max z r.to) rs]` (the fold is one atom; `e` gives `id <= r.to`; the
unconditional bound `r.to <= Nat.max z r.to` may be enough without a split).

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

Sizes are guesses **[inferred]**, from the prototype (120 lines for a flat checker without
proofs) and from the library's existing `Nat`/`Int` proofs.

### 8.1 Milestone 1: a complete vertical slice

The first lane builds the whole path from source to kernel for a small fragment, so that the
two things the prototype can't tell us get answered early: whether the semantic interfaces
are convenient to prove in Stitchwort, and whether real reading, bridging and conversion keep
the promising replay timings.

**In scope:** `Std.Omega` with the sorted `Env`, `NTerm` (including `MulLeft`/`MulRight`),
`Fact`, `Goal` (with `GVoid`), `Row`, the full certificate calculus (`Input`, `NatNonneg`,
`Combine`, `Divide`, `Split`, `Close`) and `prove` **with its proof**; the two new bridge
lemmas; the elaborator's quoting (contract of §6.5), bridges, fact gathering and search order
(§6.8), Fourier–Motzkin with tightening and small-range splits, narrow emission, and
`E-OMEGA` with labelled outcomes; `omega` and `omega [..]`.

**Done when** every row of this table (the review's) has passing tests:

| Area | Required case |
|---|---|
| Atom dimensions | out-of-range syntax can't lose a coefficient (`MkEnv [1] []`, `GLe (NV 0) (NLit 0)`, `Then (Input 0) (Close 0)` rejected) |
| Nat domain | `x <= x + y` with no non-negativity hypothesis supplied |
| Multiplication shape | `x * 3 = x + x + x`; `3 * x`; `x * 0`, `0 * x`, `x * 1`, `1 * x` |
| Boolean preprocessing | `Nat.leq a b = False`, `(p && q) = True`, `Not (a <= b)`, `Not (a < b)` as hypotheses |
| Equality | an equality goal from two refutations, assembled into the original equation |
| Contradiction | closed contradictions, disconnected ones (`h: y < y ⊢ x < 0`), and a `Void` goal |
| Conversion | association preserved (`(a + b) + c` vs `a + (b + c)` quoted as written); proof-dependent atoms (`get xs i h1`, `get xs i h2`) kept apart unless convertible |
| Integer reasoning | `2 * x = 1` refuted (`Divide`); the four-constraint example of §6.6 (`Split`) |
| Cost | increasing literal coefficients (`10 * x`, `1000 * x`, `1000000 * x`, both orders) and repeated shared subexpressions: supported compactly or refused within a clear budget |
| Proof consumption | an `omega` equality used through `rewrite` (so `J`), and a dependent transport along it, timed |
| Failure reporting | a fractional model and an opaque-atom model, each labelled correctly (§6.8) |

**Malformed certificates** (each must be rejected by `check`, as unit tests of the library
function, not just wrong multipliers): a reference to a row that doesn't exist yet; a
reference from one `Split` branch to a row made in the other; `Divide` by 0; `Divide` by a
`d` that doesn't divide some coefficient (including an Int-side or a high-index one); a
certificate that only closes if the constant is rounded up or toward zero; `Close` on a row
with a non-zero coefficient beyond the facts' highest index; and the dimension case above.

Plus the AoC targets that fit the slice: `absorbLo`, `absorbStacked`, `repBlockLength`, Day 7's
three lemmas, and a test file of 30+ goals and 10+ refusals.

### 8.2 Stages

| Stage | What | Library | Elaborator | Acceptance | Who |
|---|---|---|---|---|---|
| 1 (milestone 1) | §8.1 | 450–700 lines (most of it proofs, plus the `Int` order and floor lemmas) | 900–1,300 lines Rust | §8.1's table and tests | Opus (the soundness statement and proof, reifier contract); Sonnet for the search and messages |
| 2 | operation atoms (`-`, `if`/`max`/`min`, `/` `%` by positive literals), cheap bounds, `!=`, `\|\|`; `Int` atoms | 150–300 lines | 300–500 lines | `coveredTop`, `countFrom`, `periodSub`, `mergedContains` with its match; `(x y: Int) ⊢ x + y = y + x` | Opus |
| 3 | `Bool`-equation goals; `auto` fallback if D547 (§6.9 policy) | 50–100 lines | 200–300 lines | `mergedContains` as `omega`; `decreasing` and `%` side conditions by `auto` | Opus |
| then | convert AoC proofs (one lane per day or two), measure lines and check time; `omega only [..]` if wanted | | | the day 5 count in §7.1 | DeepSeek with a list, Sonnet review |

Each stage: one fresh lane, design review of the soundness statement before the proof is
written (the statement is the trusted part, in the sense that a wrong statement proves the
wrong thing), the targeted tests named in the lane, and the check-time numbers of §3 rerun.

**Checking cost to expect.** For certificate replay on AoC-sized goals, 0.5 to 5 ms per
`omega` (§3). For a whole `omega`, unknown until the milestone measures it; the risks are in
§9. Splits multiply cost (three `-`s are up to 8 cases), which is why cheap bounds come first.
A proof file with 30 `omega`s at replay cost alone would add 15 to 150 ms; today's whole AoC
project checks in about 1.3 s (proof-check-speed.md, "Before and after" **[checked]**).
Removing the lemma chains should also shrink terms, which proof-check-speed.md found is what
checking time follows **[inferred]**.

## 9. Risks and critical review

- **The soundness proof is real work in a language with no tactics.** Several hundred lines
  of `Int` algebra by `calc` and `rewrite`, now including `Divide` (floor) and `Split`. The
  hard parts are the `Int` order library, list invariants for rows, signed arithmetic and the
  semantic bridges, not the shape of the argument: every lemma is pointwise, so missing
  function extensionality doesn't matter. Mitigation: the `Int` ring and division laws exist,
  and it's done once. If it stalls, stage 1 could run over `Nat` only (keep each fact as
  `left <= right` with both sides `Nat` forms), an implementation choice for the lane.
- **Incomplete, like Lean's.** No dark or grey shadows; the search may miss true whole-number
  goals. The calculus can express more than the search finds (§6.6), so most improvements stay
  in Rust; a genuinely new step kind changes the checker.
- **Shape matching is brittle (§3, finding 1).** Mitigated by the contract of §6.5, the
  pre-check of the emitted term, and a property test that quotes random arithmetic
  expressions (both multiplication orders, nested `Succ`, literals) and checks `rfl`.
- **Large literal coefficients.** `k * x` unfolds `k` times, so `1000000 * x` is short to write
  and may be expensive to compare: the checker handles the coefficient with `Nat` natives,
  but conversion of the goal against `MulLeft 1000000 (NV 0)` might unfold the
  multiplication. Whether conversion short-cuts identical folded calls before unfolding is
  **[unverified]**; with glue on, "conversion compares unfoldings" (docs/core.md:199
  **[checked]**). Keeping a `MulLeft` node doesn't help if conversion forces its meaning.
  Benchmarked in the milestone; supported compactly or refused within a clear budget.
- **Shared subexpressions.** A big atom repeated across facts is quoted once (cache, §6.5),
  but conversion may still compare it many times. Benchmarked.
- **Proofs taken apart by `J`.** With no definitional proof irrelevance, an `omega` equality
  used by `rewrite`, or a dependent transport along it, may make the kernel compute with the
  proof of `prove` itself, which the prototype (where `Sound` was a hypothesis) never did.
  An unmeasured risk, not evidence of slowness; measured in the milestone (§8.1).
- **Allocation before trust.** If replay is slow, first: skip zero-multiplier rows, emit only
  used facts, share quoted data, and accumulate scaled rows without intermediate lists. A
  fused checker is fine if it still checks every coefficient cancels. No trusted `Int` native
  on the evidence so far; an untrusted fast runner may speed up the search and the
  elaborator's pre-check, since the kernel still checks the result.
- **Magic hides reasons.** A proof that says `omega` doesn't show *why*. Lean users accept
  this; the `calc` style is still there when the reasoning matters for a reader. Keep tests
  beside proofs, as now.
- **Growth of facts in scope.** Inside long proofs many facts are in scope; all are
  candidates, but only used ones are emitted (§6.8). Fourier–Motzkin can blow up (doubly
  exponential in the worst case). Mitigation: search order by connectivity (never exclusion),
  and a step budget with an honest "budget exhausted" message.
- **Overlap with SW-257 (glue).** The reifier recognises heads before forcing (§6.5); written
  for glue off, it must call `force` on calls it doesn't recognise once glue is on. Small;
  noted for the lane.
- **Is it worth it versus option E?** §7 shows about 40% fewer lines in day 5's arithmetic
  lemmas, nearly all lemma calls gone, and single steps in place of 300-character ones
  (day 2); a lemma pack wouldn't remove the steps. The line saving is smaller than "Lean
  halves it" suggests, because our proofs still match on the program's `if`s, which Lean's
  `simp`/`split` do for it. The cost is three lanes of mostly Opus work, the first larger
  than draft 1 planned. On balance yes; D545.

## 10. Decisions

**D545 (revised). Build `omega` as a certificate checked by a library function (option A),
with the first milestone a complete vertical slice (§8.1): real quoting, bridge proofs, the
proved soundness theorem, search, and kernel checking, with the certificate calculus
(`Input`/`Combine`/`Divide`/`Split`/`Close`) from the start, judged by the review's
acceptance table and malformed-certificate tests?** Recommendation: **yes**; stages 2 and 3
after the milestone's measurements, especially the cost and proof-consumption rows. The
reviewer agrees. Alternatives: B (Lean's lemma chains: no soundness theorem; speed versus A
unmeasured; more proof-producing code in the elaborator), C (search in the language: slower
checks, harder proof), E (a lemma pack; don't build), or A with flat multipliers first
(simpler stage 1, but stage 2 would then change the checker and its proof).

**D546. Surface: a term `omega` (a new keyword) that considers every arithmetic fact in scope,
plus `omega [e1, e2]` for extra facts?** Recommendation: **yes**; the reviewer agrees.
`omega only [facts]` is a possible later addition and doesn't block this. Alternatives: only
an explicit list (`omega [h1, h2]`: clearer, but most uses would list every hypothesis); a
different name (`arith`, `linear`: plainer English, but `omega` is what Lean users know, and
Lean's fragment is what this covers); `by omega` (no: there is no tactic language).

**D547. Should `auto` try `omega` for arithmetic obligations once it has failed to find a
hypothesis or decision procedure** (index bounds, `/` and `%` side conditions, `decreasing`)?
Recommendation: **yes, after explicit `omega` is stable and its failing-search cost is
measured (stage 3)**, with the §6.9 policy: a cheap eligibility check, a deterministic budget
smaller than explicit `omega`'s, only on obligations with no unsolved metavariables (never
solving one), budget exhaustion as an ordinary `auto` failure, and no re-entry into the same
obligation. Lean's `decreasing_trivial` falling back to `omega` is precedent. The reviewer
agrees, provisionally. Until then `[ok := omega]` passes one by hand. Alternative: never (keep
`auto` predictable: it only finds what's there).

## Sources

Draft 1's sources were fetched on 22 October 2026 by a research sub-agent, which recorded what
each page says; draft 2 rechecked the review's corrections the same day ([S8], [S19] to [S23]).
Labels as given in the text.

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
- [S7] Coq 8.9 reference manual, omega and `romega` ("Deprecated since version 8.9: Use lia
  instead"): https://rocq-prover.org/doc/v8.9/refman/addendum/omega.html **[checked]**
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
- [S19] Lean 4 `omega`, `OmegaM.lean` (`analyzeAtom`: `Int.natCast_nonneg`,
  `Int.min_le_left`/`right`, `Int.le_max_left`/`right`, `Int.ofNat_sub_dichotomy`, `/` and `%`
  bounds; `Cache`, "Cache of expressions that have been visited, and their reflection as a
  linear combination"; `State.atoms`, "The atoms up-to-defeq encountered so far"):
  https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/Tactic/Omega/OmegaM.lean
  **[checked]**
- [S20] Rocq 8.9 `romega` reflective core, `plugins/romega/ReflOmegaCore.v` (`t_omega`,
  `execute_omega`, `omega_valid`):
  https://raw.githubusercontent.com/rocq-prover/rocq/V8.9.0/plugins/romega/ReflOmegaCore.v
  **[checked]**
- [S21] Lean 4 `omega` front end, `Frontend.lean` (`formatErrorMessage`: "a possible
  counterexample may satisfy the constraints", then the atoms):
  https://raw.githubusercontent.com/leanprover/lean4/master/src/Lean/Elab/Tactic/Omega/Frontend.lean
  **[checked]**
- [S22] Isabelle/HOL `Presburger.thy` (`ML_file ‹Tools/Qelim/cooper.ML›`, `method_setup
  presburger` calling `Cooper.tac`, "Cooper's algorithm for Presburger arithmetic"):
  https://isabelle.in.tum.de/library/HOL/HOL/Presburger.html **[checked]**; `cooper.ML` itself
  wasn't reachable (404/503), so "theorem-producing conversions" is **[cited, from the review]**
- [S23] Lean 4 `src/Init/WFTactics.lean` (`decreasing_trivial` falls back to `omega`;
  `decreasing_trivial_pre_omega`):
  https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/WFTactics.lean **[checked]**
