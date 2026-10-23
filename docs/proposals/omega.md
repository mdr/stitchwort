# Proposal: `omega`, linear arithmetic proved by a checked certificate

**Status:** draft 2, 22 October 2026, after an external expert review (D548). Milestone 1a,
the library half (`Std.Omega`, the checker and its proved soundness theorem), is built
(SW-314, [As built](#as-built-milestone-1a)); the elaborator half, the `omega` term, is
milestone 1b (SW-315, [As built](#as-built-milestone-1b)). Ticket SW-101 (from SW-96, recommendation 4; D434 made day 5 the acceptance
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
- [As built (milestone 1a)](#as-built-milestone-1a)
- [As built (milestone 1b)](#as-built-milestone-1b)
- [Stage 1 on AoC (SW-326)](#stage-1-on-aoc-sw-326)
- [As built (stage 2)](#as-built-stage-2)
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

## As built (milestone 1a)

SW-314 built the **library half** of the §8.1 slice: `Std.Omega` with the checker and its
soundness theorem, fully proved, plus the `Int` order lemmas and bridge lemmas it needs. The
elaborator half (the `omega` keyword, quoting, the search, `E-OMEGA`) is milestone 1b (SW-315).
Everything below is **[checked]** against the files named, and the costs are **[run]** with the
release CLI built from this branch.

**Files.** `crates/elab/src/std/Omega/Omega.sw` (syntax, meanings, rows, the checker, and the
checker's unit tests), `crates/elab/src/std/Omega/Sound.sw` (the soundness proof),
`crates/elab/src/std/Int/Int.sw` ("checkpoint 4": the order lemmas), `crates/elab/src/std/Bool/Bool.sw`
(new: `List/Sort.sw`'s opening `Bool` lemmas moved here so a `&&` bridge doesn't load the sorting
proofs, plus `Bool.falseOfNotTrue`), `crates/elab/src/std/Nat/Arith.sw` (three bridges), and
`examples/accept/omega-certificates.sw` (hand-written uses).

**The interface** (constructors live in their type's namespace, `Std.Omega.NTerm.NV` and so on):

```
type Omega.Env   = | MkEnv (nats: List Nat) (ints: List Int)        -- Int atoms: stage 2
type Omega.NTerm = | NV (i: Nat) | NLit (n: Nat) | NAdd (a b) | NSucc (a)
                   | MulLeft (k: Nat) (t) | MulRight (t) (k: Nat)
type Omega.Fact  = | FLe (a b) | FLt (a b) | FEq (a b) | FNotLe (a b) | FNotLt (a b)
type Omega.Goal  = | GLe (a b) | GLt (a b) | GVoid
type Omega.Row   = | MkRow (c: Int) (nats: List Int) (ints: List Int)
type Omega.Step  = | Input (i: Nat) | NegGoal | NatNonneg (i: Nat)
                   | Combine (terms: List (Pair Nat Nat)) | Divide (r: Nat) (d: Nat)
type Omega.Cert  = | Close (r: Nat) | Then (s: Step) (rest: Cert) | Split (l: Row) (left right: Cert)

def Omega.check (facts: List Omega.Fact) (goal: Omega.Goal) (cert: Omega.Cert): Bool

theorem Omega.prove (env: Omega.Env) (facts: List Omega.Fact): (goal: Omega.Goal) -> (cert: Omega.Cert) ->
    Omega.check facts goal cert = True -> Omega.Facts.holds env facts -> Omega.Goal.holds env goal

theorem Omega.proveEq (env: Omega.Env) (facts: List Omega.Fact) (a: Omega.NTerm) (b: Omega.NTerm) (c1: Omega.Cert) (c2: Omega.Cert)
    (ok1: Omega.check facts (GLe a b) c1 = True) (ok2: Omega.check facts (GLe b a) c2 = True) (hs: Omega.Facts.holds env facts):
    Omega.NTerm.eval env a = Omega.NTerm.eval env b
```

`Omega.prove` has no hypothesis beyond the two shown: no `Sound` assumption, no length premise
on `env`. `Facts.holds` is `And (holds f1) (And (holds f2) … Unit)`, so the proofs are passed
as `Both h1 (Both h2 Trivial)`. The meanings use the surface definitions, so a quoted fact
converts with its source: `FLe a b` means `eval a <= eval b`, `FNotLe a b` means
`Not (eval a <= eval b)`, `MulLeft k t` means `k * eval t` and `MulRight t k` means
`eval t * k`, `NSucc a` means `Succ (eval a)`, and `NV i` is the `i`th Nat atom, 0 past the end.

**The rules as built.** All rows go through one function, `Omega.leRow a b` (the row `b - a`),
which is §6.3's table: `FLt a b` is `leRow (NSucc a) b`, `FNotLe a b` is `leRow (NSucc b) a`,
`FNotLt a b` is `leRow b a`, `FEq a b` is two rows, and the negated goal of `GLe a b` is
`leRow (NSucc b) a`, of `GLt a b` `leRow b a`. Certificates as in §6.6, with these choices:

- `Input i` is the `i`th of the facts' rows **flattened** (`Omega.Facts.rows`: an `FEq` gives
  two), and the negated goal is its own step, `NegGoal` (rejected for `GVoid`), rather than an
  `Input` index that would shift with the goal kind.
- The certificate's rows start empty and are numbered from 0 in the order the steps make
  them; `Split l` gives the left branch `l` and the right branch `-1 - l`, each at the next
  number, and the tree keeps one branch's rows from the other.
- `Combine` pairs are `MkPair k r`: `k` times row `r`, `k` a `Nat`.
- `Divide r d` needs `d > 0` and checks that `d` divides every coefficient, Nat and Int side
  (`Int.mod … == 0`); the constant uses `Int.div`, which for a positive divisor rounds down.
- A missing row reads as the zero row (`0 <= 0`, true), so references can't make the proof
  unsound; `Step.valid` still rejects them so a malformed certificate fails. Only `Divide`'s
  validity is used in the soundness proof.
- `FEq`, `FNotLe` and `FNotLt` are in `Fact`, so an equation or a negated comparison can be
  quoted directly; the bridges below remain for the other source forms.
- Constructor names carry `F`/`G` prefixes (`FEq`, not `Eq`, which is the equality namespace).

**The proof** (`Omega/Sound.sw`) is the §6.6 list, as planned and in about that shape:
`Omega.linEval` (a term's linear form means the term, by induction, with `Nat.mulComm` for
`MulRight`); `Omega.dotAdd`/`dotScale`/`dotDiv`/`dotAllZero`/`dotUnit` (the coefficient lists,
pointwise); `Omega.leRowHolds` (the convention); `combineHolds`, `divideHolds`
(`Int.divFloorNonneg`), `splitOtherHolds` (a `Bool.inspect` on `Int.leq 0 l`, no classical
logic); `contraVoid`; then `checkCertSound` by induction on the certificate, and `prove` by
`Bool.inspect` on the goal's own `Nat.leq`. No extensionality was needed. One elaboration quirk
on the way: an `Eq.cong (t => Int.add t (c % d))` whose lambda mentions `%` (an `auto` proof)
was refused against a statement printed identically, while the same step with the `%` term
abstracted to a variable passed **[run]**; the proof avoids it by stating `Int.mulAddAddMul`
over variables. Fixed by SW-323: the lambda's proof was still an unknown applied to `t`, and once
the lambda was applied to a term (not a variable) unification couldn't solve it; an `auto`
proof's unknown may now ignore such an argument when its statement doesn't mention it.

**`Int` lemmas added** (`Int/Int.sw`, all by cases on the constructors): `Int.addCong`,
`Int.addNonneg`, `Int.mulNonneg`, `Int.notNonnegOfIsNeg`, `Int.zeroMul`, `Int.negOneMul`,
`Int.addAddSwap`, `Int.subNonnegOfLe` (`m <= n` gives `0 <= n - m`), `Int.negOneSubNonneg`
(`Int.leq 0 v = False` gives `0 <= -1 - v`), `Int.nonnegOfMulAddSmall`,
`Int.nonnegOfMulAddMod`, `Int.mulAddAddMul`, and `Int.divFloorNonneg`
(`0 <= c + (d+1) * s` gives `0 <= c / (d+1) + s`). The order algebra needed was only about
`0 <= x`, so no general `a <= b` lemmas were added.

**Bridge lemmas** for 1b, with their real names:

| Source hypothesis | Bridge | File |
|---|---|---|
| `Nat.leq a b = False` | `Nat.leqFalse a b e : b < a` (existing) | `Nat/Arith.sw` |
| `(p && q) = True` | `Bool.andLeft p q e`, `Bool.andRight p q e` (moved) | `Bool/Bool.sw` |
| `Not (x = True)` | `Bool.falseOfNotTrue x h : x = False` (new) | `Bool/Bool.sw` |
| `Not (a <= b)` | `Nat.ltOfNotLe a b h : b < a` (new), or quote as `FNotLe` | `Nat/Arith.sw` |
| `Not (a < b)` | `Nat.leOfNotLt a b h : b <= a` (new), or quote as `FNotLt` | `Nat/Arith.sw` |
| `a = b` | `Nat.leOfEq a b e : a <= b` (new), or quote as `FEq` | `Nat/Arith.sw` |
| equality goal | `Omega.proveEq` (or `Nat.leAntisym` with two `prove`s) | `Omega/Sound.sw` |

**Size.** `Omega/Omega.sw` 387 lines (about 290 of definitions and comments, then 24 `test`s),
`Omega/Sound.sw` 269 lines (237 non-blank) of proof, `Int/Int.sw` +91 lines, `Bool/Bool.sw`
61 lines (mostly moved), `Nat/Arith.sw` +10. That is inside §8.2's 450–700 for the library.

**Acceptance cases covered here** (library-side; the elaborator rows of §8.1's table are 1b's):

| Area | Where | Case |
|---|---|---|
| Atom dimensions | `Omega.sw` test `check: no dropped coefficient` | `[] ⊢ GLe (NV 0) (NLit 0)` with `Then NegGoal (Close 0)` refused |
| Nat domain | example `leAddRight` | `x <= x + y` with `NatNonneg 1`, no hypothesis |
| Multiplication shape | examples `mulRight3`, `mulLeft3`, `mulRight0`, `mulLeft0`, `mulRight1`, `mulLeft1` | `x * 3 = x + x + x`, `3 * x = …`, `* 0` and `* 1` on both sides, by `proveEq` |
| Boolean preprocessing | example `absorbTrue` | `Bool.andRight` and `Nat.leqFalse` bridges (day 5's `True` arm) |
| Equality | examples `antisym` and the `mul…` ones | an equation from two refutations |
| Contradiction | examples `threeLtTwo`, `disconnected` (`h: y < y ⊢ x < 0`), `twoFactsVoid` | closed, disconnected, and a `Void` goal |
| Integer reasoning | examples `twoXEqOne` (`Divide`), `splitRegression` (§6.6's four constraints, `Split` on `y`, four `Divide`s) | |
| Day 5 | examples `stacked`, `absorbTrue`, `absorbFalse` | `absorbStacked`'s steps |
| Malformed certificates | `Omega.sw`, 10 `check refuses: …` tests, each paired with an accepted fix | missing row in `Combine`, `Close`, `Input`; `NegGoal` for `GVoid`; a row from the other `Split` branch (in `Close` and in `Combine`); `Divide` by 0; a non-dividing `d` on a Nat coefficient at atom 7 and on an Int coefficient; `Close` with an atom beyond the facts |
| Rounding | `Omega.sw` tests `Divide floors a negative/positive constant` | certificates that close only with the floor |

"A certificate that only closes if the constant is rounded up or toward zero" (§8.1) can't be
written: those roundings give weaker rows than the floor, so anything they close the floor
closes too. The floor tests are the observable form of that requirement.

One finding for 1b: `absorbTrue` states its hypothesis as `(Nat.leq lastFrom id && Nat.leq id
lastTo) = True`. Written with `<=` inside the `&&`, as day 5 does, the `&&` operands elaborate
through `Decidable.toBool`, and `Bool.andRight` on the `Nat.leq` forms was refused **[run, by
the sub-agent]**. 1b's `&&` bridge must quote the operands as the hypothesis has them (or use
`Nat.betweenLo`/`Nat.betweenHi`, which take that form, `Nat/Arith.sw`).

**Costs [run]** (`STITCHWORT_TIMINGS=decls stitchwort check --no-cache`, one run, elaboration
and kernel together; steps are evaluation steps):

| case | steps | ms (elab + kernel) |
|---|---:|---:|
| day 5 `stacked` (3 atoms, 2 facts) | 10,814 | 0.4 |
| day 5 `absorbTrue`, with two bridges | 13,165 | 0.5 |
| `antisym` (`proveEq`, 2 facts) | 14,423 | 0.5 |
| `twoXEqOne` (two `Divide`s) | 9,407 | 0.3 |
| `splitRegression` (`Split`, four `Divide`s) | 46,195 | 1.4 |
| `chain10` (10 atoms, 9 facts; the prototype's 54,751) | 61,310 | 1.9 |
| `x * 10 <= 20`, `x * 1000 …`, `x * 1000000 <= 2000000` (`MulRight`) | 5,960 each | 0.2 each |
| `10 * x <= 20` (`MulLeft`) | 7,000 | 0.3 |
| `1000 * x <= 2000` (`MulLeft`) | 109,960 | 2.9 |
| `10000 * x <= 20000` (`MulLeft`) | 1,045,960 | 26.3 |
| `100000 * x …`, `1000000 * x …` (`MulLeft`) | stack overflow | — |
| `x * 3 = x + x + x` by `proveEq` | 6,352 | 0.3 |
| that equation used by `rewrite` (`J`) | 1,169 | 0.1 |
| a `J` transport along it, computed (`castBy 7 42 = 42 := rfl`) | 1,903 | <0.1 |
| loading the library for a first `Omega.prove` | — | about 90 (`Omega` 2.0, `Sound` 10.8, plus `Int/Int.sw` 16, `Nat/Arith.sw` 19, and `List/Toolkit.sw` 39 that `Int/Int.sw` pulls in) |

What the numbers say:

- **Replay stays cheap** with real proofs: the soundness proof is never unfolded by checking a
  use, and the day 5 step costs about what the prototype's did (§3).
- **Large `MulLeft` literals are the cost risk the review predicted**, but it isn't `omega`'s:
  `k * x` unfolds `k` times whenever the goal's own type is compared. Without any `omega`,
  `theorem (x: Nat) (h: 100000 * x <= 5): 100000 * x <= 5 := h` takes 14.4 million steps
  (664 ms), and the same with `1000000` overflows the checker's stack **[run]**. `MulRight`
  (`x * k`, stuck) costs the same for every `k`. So 1b should accept `MulLeft k` only up to a
  bound (say `k <= 1000`) and refuse larger ones with a clear message; the overflow itself is a
  separate evaluator issue, worth its own ticket.
- **Proof consumption is cheap**: `rewrite` with an `omega` equation, and a `J` that must
  compute the proof to `rfl`, cost under 2,000 steps.
- **Library load** is a one-off per program (and cached by the check cache); most of it is
  `List/Toolkit.sw`, which `Int/Int.sw` needs only for its two `List.sumBy` lemmas. Splitting
  those out would cut it to about 50 ms.

**What 1b must emit.** For a goal `A <= B` or `A < B`:
`Std.Omega.prove (Std.Omega.Env.MkEnv [atoms…] []) [facts…] (GLe a b) cert rfl (Both p1 (Both p2 … Trivial))`,
with each `p` a hypothesis or a bridge application from the table, the facts in the order of
the `Both`s, and `Input` indexes counting an `FEq` as two rows. For `Void`, goal `GVoid`. For
an equation, `Std.Omega.proveEq env facts a b c1 c2 rfl rfl hs`. The quoted trees must mirror
the goal's computed shape (§6.5); `Succ x` is `NSucc`, a literal is `NLit`. `Split` rows are
written as `MkRow c [coefficients…] []` with `Int` literals. Only used facts and atoms (§6.8).
The elaborator's pre-check runs `Omega.check` itself, which costs what the kernel's run costs.

## As built (milestone 1b)

SW-315 built the **elaborator half** of the §8.1 slice: the `omega` term, reading and quoting
goals and facts, bridge proofs in the emitted term, the search, narrow emission, the pre-check
and `E-OMEGA`. Everything below is **[checked]** against the files named, and the costs are
**[run]** with the release CLI built from this branch. User-facing description:
[docs/syntax.md](../syntax.md), "`omega`".

**Files.** `crates/syntax` (`Tok::KwOmega`, `Expr::Omega { facts, span }`, parsed as an atom:
`omega`, or `omega [e1, e2]` when a `[` follows); `crates/elab/src/omega.rs` (reading, quoting,
emission, messages); `crates/elab/src/omega_search.rs` (the search, untrusted, with unit
tests); `module.rs` (the pre-pass: an `omega` refers to the library names its proofs use, so
their files load wherever it's written, and the check cache records them as needs);
`check.rs` (dispatch, `Ctx::visible_locals`, `Ctx::name_of_level`); the keyword in the VS Code
grammar, the playground's highlighter and the syntax fuzzer. Examples:
`examples/accept/omega-basics.sw`, `examples/accept/omega-day05.sw`,
`examples/reject/omega-*.sw`.

**What it emits**, as planned in "What 1b must do": `Std.Omega.prove (MkEnv [atoms] []) [facts]
goal cert rfl (Both p1 (… Trivial))` for `<=`/`<` goals and `Void` (`GVoid`), and
`Std.Omega.proveEq env facts a b c1 c2 rfl rfl ps` for `=` on `Nat`. Around those, the goal is
taken apart first: `Not p` becomes `h => …` with `h: p` in scope and `Void` to prove; `And p q`
is `Both`; `(p && q) = True` is `Bool.andIntro`; `Nat.leq x y = False` is
`Nat.leqFalseOfLess y x (… : y < x)`; `Decidable.toBool d = True`/`False` is
`Decidable.toBoolOf`/`toBoolOfNot`. Anything else is "unsupported structure".

**Reading facts.** Every variable in the context (parameters, pattern variables, `match e:`
and `if h:` equations, `let`s, and variables `omega` itself introduced), every visible local
definition, and the listed terms, each read after computing, recursively through bridges
applied in the term: `Nat.leq a b = False` by `Nat.leqFalse`; `(p && q) = True` by
`Bool.andLeft`/`andRight` (with `q` read off the `Bool.ifThenElse p (u => q) (u => False)` that
`&&` is); `Decidable.toBool d = True`/`False` by `Decidable.toBoolSound`/`toBoolFalse`, which
resolves 1a's finding: day 5's `(last.from <= id && id <= last.to) = True` has
`Decidable.toBool (Bool.decTrue (Nat.leq …))` operands, so it is two bridges deep, and works;
`And p q` by `And.left`/`right`. What's left must be `a <= b` (`Nat.leq a b = True`), `a = b`
on `Nat`, or `Not (a <= b)`. Choices:

- `a < b` computes to `Succ a <= b` and is quoted so (`FLe (NSucc a) b`); the elaborator never
  writes `FLt`, `FNotLt` or `GLt`, which stay for hand-written certificates.
- A comparison that computed all the way is read as one: `True` is `Nat.leq 0 0` and `False`
  is `Nat.leq 1 0`. So `h: 3 < 2` (whose type is `False = True`) is the fact `FLe (NLit 1)
  (NLit 0)`, and the goal `x < 0` (also `False = True`) is `GLe (NLit 1) (NLit 0)`; both mean
  what they quote by conversion.
- `Not (a = b)` facts are skipped with an "unsupported structure" note (stage 2's splits).

**Quoting** follows §6.5 on the computed value: a number is `NLit`; `k + x` (`Value::NatAdd`,
what `Succ` and `1 + x` make) is `NSucc` for 1 and `NAdd (NLit k)` otherwise; a stuck `a + b`
is `NAdd`; `x * k` (stuck) is `MulRight`. `k * x` has already computed to
`x + (x + … + (x + 0))`, so a chain of `k >= 2` additions of the same term ending in `0` is
quoted `MulLeft k x`, whose meaning computes to the same chain; `k > 1000` is refused with
`E-OMEGA` and a note to write `x * k` (1a's costs). Everything else of type `Nat` is an atom.
Atoms are compared by the same term (`matching::same`, after read-back) and then by a
conversion check under a 20,000-step budget (`Limits`, as `unify::cheaply` does); failing or
running out keeps them apart, and no metavariable is solved. An unsolved metavariable in the
goal's arithmetic is `E-OMEGA` ("needs to know the goal"); a fact with one is skipped. With
glued values on (`STITCHWORT_GLUE=1`) the examples give the same results; `Nat.add` and
`Nat.mul` have natives, which don't glue, so "recognise before forcing" needs nothing more for
them.

**The search** (`omega_search.rs`) works on rows `0 <= c + Σ a_i x_i` with `i128`
coefficients (an overflow counts as running out of budget):

1. *Grouping.* Atoms are joined when a row mentions both. The goal's group (with every closed
   row) is tried first, then each other group on its own, each with `x >= 0` for its atoms
   (`NatNonneg`). `Void` goals try every group.
2. *Fourier–Motzkin*, one variable at a time: first any equality (a row whose exact negation
   is also a row, smallest coefficient first), eliminated by combining with both directions;
   otherwise the variable with bounds on one side only (dropped), else the fewest new rows,
   preferring coefficient ±1. Every new row is divided by the gcd of its coefficients with the
   constant rounded down (`Divide`); per stage, rows are kept one per coefficient list (the
   strongest), indexed, and a row meeting its exact negation with a negative sum closes at once.
3. *Model and splits.* If no contradiction appears, substituting back gives a rational point.
   If it's whole, the search fails with an integer model; if not, it splits on the first
   fractional atom `x = q` (`x <= floor q` or `x >= floor q + 1`, a `Split` row) and refutes
   both sides, up to 6 levels; at the limit it fails with the rational model.
4. *Budget.* 20,000 rows for the whole `omega`, deterministic (no hash map is iterated).

This is branch and bound rather than §6.8's "small-range split": it splits where the rational
point is fractional, so it needs no range analysis. It closes the §6.6 regression (one split)
and fails honestly on the shifted version in `omega-rational-model.sw`, which needs a split on
`x - z`, not on an atom.

**Emission.** Each branch's certificate writes only the rows its contradiction needs, in
dependency order, each once; split rows are numbered by depth, since nothing is written
before a split. Then only the facts the certificates use are kept, renumbered (`Input` counts
an `FEq` as two), and only the atoms of the goal, the kept facts, `NatNonneg` steps and split
rows. A Rust replay of the certificate (`omega_search::replay`) runs first, then the
**pre-check**: `Std.Omega.check` evaluates to `True`, each kept fact's
`Omega.Fact.holds env f` unifies with its proof's type, and the theorem's result type unifies
with the goal; a failure is `E-OMEGA-INTERNAL`, naming `omega` as the bug.

**Acceptance** (§8.1's table, through the `omega` keyword; all pass):

| Area | Case | Where |
|---|---|---|
| Atom dimensions | the checker refuses `[] ⊢ GLe (NV 0) (NLit 0)` with `Then NegGoal (Close 0)` | 1a's `Omega.sw` test; the search never emits such a certificate (each one is replayed in Rust first) |
| Nat domain | `x <= x + y`, no hypotheses (`NatNonneg`) | `omega-basics.sw` `leAddRight` |
| Multiplication shape | `x * 3 = x + x + x` and `x + x + x = x * 3`; `3 * x` both ways; `x * 0`, `0 * x`, `x * 1`, `1 * x` | `mulRight3`…`mul1b` |
| Boolean preprocessing | `Nat.leq a b = False`, `(a <= b && b <= c) = True`, day 5's `(lastFrom <= id && id <= lastTo) = True` (two bridges deep), `Not (a <= b)`, `Not (a < b)`, `And`, equations as facts | `leqFalseHyp`, `andHyp`, `absorbTrue`, `notLe`, `notLt`, `propAnd`, `eqHyp` |
| Equality | `a <= b`, `b <= a ⊢ a = b` by `proveEq` | `antisym` |
| Goal forms | `<`, `<=`, closed `2 < 3`, `Not (y <= x)`, `Nat.leq y x = False`, `And …`, `(… && …) = True` | `ltGoal` … `boolAndGoal` |
| Contradiction | closed (`3 < 2 ⊢ Void`), disconnected (`y < y ⊢ x < 0`), two facts ⊢ `Void` | `threeLtTwo`, `disconnected`, `void2` |
| Conversion | `(a + b) + c <= a + (b + c)` quoted as written; `getP n h1` vs `getP n h2` kept apart (rejected), the same proof one atom | `assoc`; `omega-proof-atoms.sw`; `sameProof` |
| Integer reasoning | `2 * x = 1 ⊢ Void` (`Divide`); §6.6's four constraints (one `Split`, `Divide`s) | `twoXEqOne`, `splitRegression` |
| Cost | `10 * x`, `1000 * x` (`MulLeft`, at the limit), `2000 * x` refused; `x * 10`, `x * 1000000` (`MulRight`); one atom `List.length (List.append xs ys)` in four facts | `big0`, `big1`, `omega-mul-left-limit.sw`, `bigR0`, `bigR`, `shared` |
| Proof consumption | an `omega` equation through `rewrite` both ways; a `J` transport along one, computed (`transport 7 42 = 42 := rfl`) | `viaRewrite`, `castBy`, `transportComputes` |
| Positions | `omega [h a]`; a `calc` step; a local theorem | `viaList`, `calcStep`, `localDef` |
| Failure reporting | integer model; opaque-atom model (with the `x * y` note); rational model; unsupported goal; budget; `a != b` note; no goal | `examples/reject/omega-*.sw` (9 files, snapshots) |
| Day 5 | `absorbLo`, `absorbStacked`, `topGe`, `coveredTop`, and `mergedContains`'s arithmetic | `omega-day05.sw` |

The other 1a acceptance rows (malformed certificates, rounding) are the checker's and are
unchanged.

**Messages** (verbatim, from the snapshots; the facts and atoms notes are omitted here):

```
[E-OMEGA] `omega` can't prove `x < y`
  label: an integer model of the arithmetic abstraction satisfies the facts and the goal's negation
  note:  an integer model of the arithmetic abstraction (it may not be a real counterexample): x = 0, y = 0

[E-OMEGA] `omega` can't prove `x <= x * y`
  label: an integer model of the arithmetic abstraction satisfies the facts and the goal's negation
  note:  an integer model of the arithmetic abstraction (it may not be a real counterexample): x = 1, x * y = 0
  note:  unsupported structure: `x * y` is an atom (a product of two unknowns isn't linear)

[E-OMEGA] `omega` can't prove `Void`
  label: a rational model of the relaxation satisfies the facts
  note:  a rational model of the relaxation (not a counterexample: whole numbers may still rule it out, but the search's case splits didn't): z = 4, x = 4, y = 13/3

[E-OMEGA] `omega` can't prove `xs = xs`
  label: unsupported structure: this goal isn't linear arithmetic on `Nat`

[E-OMEGA] `omega` can't prove `a + b + c + d + e + f + g + h <= 500`
  label: budget exhausted: the search stopped before finishing
  note:  budget exhausted: the search may make 20000 rows and 6 levels of case splits; nothing is claimed about the goal
```

**Day 5** (`omega-day05.sw` against `aoc/src/Aoc/Day05/Proofs/Part2.sw`, non-blank lines of
each theorem; `aoc/` itself is unchanged):

| lemma | lines before | after | arithmetic lemma calls before | after |
|---|---:|---:|---:|---:|
| `absorbLo` | 9 | 6 | 0 (a two-step `calc`) | 0 |
| `absorbStacked` | 19 | 12 | 4 | 0 |
| `coveredTop` | 10 | 6 | 2 | 1 (`Nat.leMaxRight`, listed) |
| `mergedContains` | 11 | 10 | 9 | 1 (`Nat.leMaxLeft`, listed) |
| the four | 49 | 34 | 15 | 2 |
| `topGe` | 6 | 3 | 2 | 2 (`Nat.leRefl`; `Nat.leMaxLeft`, listed) |

§7.1 predicted 31 after stage 2 and 28 after stage 3; what's left is `Nat.max` (stage 2's cheap
bounds would drop the listed `Nat.leMax…` facts) and `mergedContains`'s `Bool` equations
(stage 3).

**Costs** **[run]** (`STITCHWORT_TIMINGS=decls stitchwort check --no-cache`, one run;
elaboration includes the search and the pre-check, which runs the checker as the kernel
does):

| case | steps | ms (elab + kernel) |
|---|---:|---:|
| `closedGoal`, `threeLtTwo` | 1,904; 2,118 | <0.1 |
| `leAddRight`, `mulRight3`, `assoc` | 6,111; 7,283; 6,534 | 0.2 |
| day 5 `absorbTrue` (two bridges) | 17,079 | 0.5 |
| `antisym` (`proveEq`) | 16,583 | 0.5 |
| `eqHyp` (two equations, `proveEq`) | 33,639 | 1.0 |
| `twoXEqOne` (`Divide`) | 9,989 | 0.3 |
| `splitRegression` (`Split`) | 44,707 | 1.2 |
| `shared` (one atom in four facts) | 14,972 | 0.5 |
| `big1` (`1000 * x`, `MulLeft`) | 153,074 | 3.9 |
| `bigR` (`x * 1000000`, `MulRight`) | 8,072 | 0.2 |
| `viaRewrite`, `castBy` (through `J`) | 8,496; 7,862 | 0.3 |
| `transportComputes` (a computed `J` along an `omega` proof) | 1,893 | <0.1 |
| day 5 `absorbLo`, `absorbStacked`, `coveredTop`, `mergedContains` with `omega` | 18,547; 53,633; 38,106; 70,004 | 0.8; 2.2; 1.5; 2.7 |
| the same, hand-written in `aoc/` | 5,911; 27,890; 20,592; 32,231 | 0.3; 1.4; 1.0; 1.7 |
| `omega-budget.sw` (20,000 rows, then fails) | — | about 10 (search) |
| loading the library for a first `omega` | — | about 70 (`Omega`, `Sound`, `Int/Int.sw` and the `List/Toolkit.sw` it pulls in; once per program, and cached) |

What they say: a whole `omega` costs 0.1–3 ms on these goals, two to three times the steps of
the hand-written day 5 proofs (whose lemma chains are small), well inside §8's 0.5–5 ms
replay estimate; `1000 * x` is the most expensive case, which is why the limit is 1000. The
search itself is negligible except when it runs out of budget.

**What's left for stage 2** (§6.7, §8.2): operation atoms with proved relationships for `-`,
`Nat.max`/`min`, `if`, `/` and `%` by positive literals (with cheap bounds first, so
`coveredTop`, `topGe` and `mergedContains` lose their listed lemmas); `a != b` and `||` facts
(splits); `Int` atoms; a range check before splitting, or splitting on combinations of atoms
(the shifted example in `omega-rational-model.sw` needs a split on `x - z`); a smaller
search budget for the `auto` fallback (D547) and timing the failing search; converting the
AoC proofs. Smaller: `(p && q) = False` and `(p || q) = True` facts; `Bool`-equation goals
(stage 3); a `Not (x = True)` fact whose `x` is an `&&`.

## Stage 1 on AoC (SW-326)

SW-326 (D558) is the plan's gate before stage 2: convert every AoC proof step that stage 1
already closes, and measure. Everything below is **[run]** or **[checked]** against the
branch's `aoc/src/Aoc/*/Proofs/` (Common, days 1 to 8) and the release CLI built from the same
tree; the "before" tree is commit `df42c734`. Theorem statements, programs and answers are
unchanged (`stitchwort check --no-cache` is clean for the whole project; `stitchwort test
--no-cache` is recorded at the end of the section).

**How the conversions look.** Four kinds, in the order of how often they came up:

1. A chain of `Nat.leTrans`/`leCongRight`/`lessLe`/`leqFalse`/`addZero`/`addOne` calls that
   only reshapes an order fact becomes `omega` (or `omega [facts]`). Example, Day 4
   `stepKeeps`: the 3-line `many` + `Nat.lessIrrefl (… Nat.leTrans …)` is
   `Void.exfalso (omega [stable r c hk, neighboursMono grid k s ks r c])`.
   Day 4 `transpose9`, a 5-line `calc` of four `Nat.addSwap` steps, is `omega`.
2. A lemma argument whose type is fixed (`And.left ins r c (Nat.leqFalse (Succ r) grid.height
   e1)`) becomes a bare `omega` argument (these and the other bare uses are 146 of the 209
   `omega`s; 63 carry a fact list).
3. A calc that bridges two facts by arithmetic becomes one `omega [the two facts]`: Day 2
   `window`/`windowAbove` (five lines of `minLeRight`/`leSucc`/`leMaxLeft` steps become a
   single `omega [Nat.minLeRight …, Nat.leMaxLeft …]`), Day 5's five lemmas (the
   `examples/accept/omega-day05.sw` conversion, applied), Day 4's `Sweep.sw` window counting
   (`few2`, `few3`, `many`, `many2` and the final `Nat.addOne` step are one `omega [windowIsNeighbours …,
   Eq.cong Cell.count hs]`).
4. Unsupported atoms with a supplied lemma: stage 1 treats `a - b`, `a % b`, `max`, `min` as
   atoms, so `omega [Nat.addSubCancel from (to + 1) e]` closes `rangeEnd` and `rangeIn`
   (`Common.Proofs`) and the four `blockCount` sites in Day 2: the lemma still names the
   fact, `omega` does the rest.

One helper deleted (`lessTrans`, Day 8 Part 1: its one use is `omega [...]`). No other helper
lemma became unused (the local lemmas that remain are non-linear, `-`, `%` or `Int` facts).

**Per day.** Lines are non-blank non-comment lines of `Proofs/*.sw`; "lemma calls" counts
mentions of the linear-order lemma names (`Nat.leTrans`, `leRefl`, `leSucc`, `leCong*`,
`ltCong*`, `lessLe`, `lessIrrefl`, `lessTrans`, `leqFalse`, `leqFalseOfLess`, `addOne`,
`addZero`, `addSucc`, `addComm`, `addAssoc`, `addSwap`, `leAdd*`, `leAntisym`, `leOfAddLe`,
`addSuccLeSucc`, `succNotZero`, `zeroNotSucc`, `succInjective`, `zeroLe`, `leLessSucc`, the
`max`/`min` order lemmas, `predLeSucc`, `leMulPos`, `mulOne`, `mulZero`) outside comments, including the
ones now written as facts inside `omega [...]`. Check time is the `STITCHWORT_TIMINGS=1
stitchwort check --no-cache Aoc.DayNN.Proofs` row for the namespace, elaboration plus kernel,
median of five runs on one machine, so differences under about 5% are noise.

| Day | lines before → after | lemma calls before → after | `omega` | check ms before → after |
|---|---:|---:|---:|---:|
| Common | 69 → 55 | 39 → 8 | 16 | 5.6 → 10.7 |
| 1 | 139 → 139 | 19 → 10 | 6 | 39.7 → 41.7 |
| 2 | 1080 → 1044 | 133 → 48 | 68 | 266.5 → 285.4 |
| 3 | 167 → 158 | 35 → 5 | 20 | 23.5 → 29.3 |
| 4 | 894 → 880 | 66 → 4 | 46 | 409.8 → 427.4 |
| 5 | 162 → 143 | 21 → 3 | 12 | 17.9 → 21.5 |
| 6 | 147 → 145 | 1 → 1 | 1 | 22.7 → 23.1 |
| 7 | 391 → 389 | 27 → 5 | 16 | 69.4 → 73.5 |
| 8 | 545 → 541 | 36 → 0 | 24 | 767.6 → 730.0 |
| **all** | **3594 → 3494** (-2.8%) | **377 → 84** (-78%) | **209** | **1622.7 → 1642.6** (+1.2%) |

Source size, counting the characters of those lines, goes from 277,965 to 263,469 (-5.2%); the
proof lines that were removed were mostly long ones. Day 6 has a single arithmetic step
(`problemWide`, four lines of `Bool.andLeft`/`andRight` plumbing, now `omega`: the `||`
conjunct of `isProblem` is simply ignored, the `lo < hi` conjunct is found).

**What the numbers say.**

- *Lines* barely move (-2.8%): a call chain was usually one line already, wrapped in a call
  that has to stay (`rewrite … in`, `Eq.trans (Bool.decTrueToBool …)`, `Void.exfalso`). The
  change is in what the line says: 293 mentions of arithmetic lemmas by name are gone, and
  the replacements are either a bare `omega`, which leaves nothing to get wrong when the
  program changes, or `omega [facts]`, which names the *facts* the step needs, not the
  order in which to chain them. Day 5, the one day §7.1 estimated, goes 162 → 143 lines; its
  four lemmas are the 49 → 34 of `omega-day05.sw` (the rest is `topGe`, `solvePart2Correct`,
  `stackedCount` and `headCount`).
- *Check time* is a wash: +20 ms on 1.6 s of proof checking (+1.2%), inside run-to-run
  noise for the larger days. Eight of the nine namespaces are slower by a few ms each (68 ms
  together over 209 `omega`s, about 0.3 ms each, within §"As built (1b)"'s 0.1 to 3 ms), and the
  first `omega` of a program also loads `Std.Omega` and `Std.Omega.Sound`, about 10 ms **[run]**
  (the `std/Omega/*` rows of the timings table; they are separate rows, not in the figures
  above, and shift each namespace's `total` by that much). Day 8, the slowest namespace, got
  38 ms *faster* (767.6 → 730.0), which I haven't traced (**[unverified]**: its `occurrencesSplit`,
  `onlyOne` and `memPairs` lost long rewrite chains, my guess is that that is cheaper to check).
- *Failures to close were rare.* Of about 210 `omega` sites, two needed a second try: one
  where the goal was unknown (`Eq.cong (x => …) omega` in Day 1 `stepRight` is now
  `(omega: d = Succ a)`; stage 1's `needs to know the goal` message was clear), and the 20 sites
  of item 2 below, where the *goal* isn't arithmetic and the proof is a contradiction (written
  `Void.exfalso omega`).

**What stage 1 could not close** (every place I read and left, with the missing feature;
numbers are mentions of the lemma that remains, outside comments).

1. *Truncated subtraction `a - b`* (stage 2). The biggest group, 30 mentions:
   - closed only with a lemma supplied (8, stage 2 would drop the lemma): `Nat.addSubCancel`
     in `rangeEnd`, `rangeIn` and four Day 2 sites (`Repeated.sw` `twiceBlockCount`, two;
     `Part2.sw` `blockCountRep`, two; each `omega [Nat.addSubCancel …]`), `Nat.subEqZero`
     (`rangeEnd`), `Nat.predLeSucc` (Day 2 `idWeight`);
   - not closed (22): `subZeroLe` in Day 4 (`n - m = 0 -> n <= m`, the whole lemma is one `-`
     fact), `Nat.subSuccRight`/`subEqZero`/`addSub` rewrite steps in `countFrom`,
     `countBelow`, `countEmpty` (Common), `stepLeftFrom`/`stepLeftTop` (Day 1),
     `problemColumns` (Day 6), `betweenOne`/`betweenTwo`/`blocksWindow`/`weightBelow`/
     `divisorWeightsAll`/`periodSub`/`periodDvd`/`smallestIsPeriod` (Day 2),
     `bestLengthStep`/`bestOptimalStep` (Day 3: `Nat.addSubLe`, `Nat.leSubAdd`), and
     `Nat.addSub _ 1` in Day 8 `countedMoved`.
2. *Goal is not arithmetic but the facts contradict* (20 sites: `Void.exfalso omega` or
   `Void.exfalso (omega [facts])`). Not a missing *reasoning* feature: the goal is a `Bool`
   equation or a program-level statement (`copies x n = True`, `joltageOf … <= joltageOf …`,
   `Vec …`), and `omega` reports "unsupported structure". Days 2 (4), 3 (4), 4 (5), 5 (1),
   7 (1), 8 (5). If `omega` refuted the facts for *any* goal, all 20 would be a bare `omega`.
3. *`Nat.max`/`Nat.min`.* Eight sites list an order lemma as a fact (`omega [Nat.leMaxLeft …]`:
   Common `countFrom` ×2, Day 2 `windowAbove`/`window` ×3, Day 5 `topGe`/`coveredTop`/
   `mergedContains`; 11 lemma mentions), and twelve more sites rewrite with an equation about
   them (`Nat.maxLeft`, `maxRight`, `minLeft`, `minRight`: Common ×3, Day 2 `windowBelow`/
   `windowIn`/`window*` ×4, Day 3 `bestLengthStep`/`pickRestLength`/`pickBase`/
   `maxJoltageIsMaximum` ×5), where the equation is used as a `rewrite` rule or an `Eq.trans`
   link and `omega` would need to be stated with its type.
4. *Non-linear arithmetic* (products of two unknowns, 44 mentions of `leMulPos`, `leMulRight`,
   `mulComm`, `mulAssoc`, `mulSucc`, `mulSuccCancel`, `mulDistribLeft`, `mulCancelLeft`, all in
   Day 2): `blockLengthLeProduct`, `copiesLeProduct` (`x <= x * y` from `1 <= y`),
   `writeTimesMul` (an `Nat.mulAssoc`/`mulComm`/`mulDistribLeft` calc), `twiceAtLeast`,
   `tooLong`, `twiceInjective`/`repInjective` (`mulSuccCancel`), `writtenAsFillsDigits`
   (`2 * len <= copies * len` from `2 <= copies`), `blockCountPos`, `eK`/`ekn` in Day 2 Part 2.
   Eleven of these were bridged by listing the product fact (`omega [Nat.leMulPos …,
   Nat.mulComm k n]`). Two cheap pieces would remove some: atoms for products compared up to
   commutativity (the six `Nat.mulComm` facts, plus `Nat.mulComm … rewrite` steps in
   `writtenAsFillsDigits`, `writtenBlock`, `periodWritten`), and a "monotone product" hint;
   neither is linear arithmetic.
5. *`%` and `/` by a variable* (56 mentions, Day 1 and Day 2): `Nat.modSmall`, `modAddMod`,
   `addModSelf`, `addDivSelf`, `divModEq`, `modSelf`, `divSmall`, `modLess`, `dividesLe`: the
   dial of Day 1 is deliberately for a dial of any size (its header comment says the literal
   100 made every comparison take seconds), and Day 2's period argument divides by the
   smallest period. `%`/`/` by a **positive literal**, the §6.7 plan, is used by *no* AoC
   proof. Where a `%` fact came with its lemma, atoms were enough: `ek` and `countTimesPeriod`
   (`omega [Nat.divModEq …, smallestDivides …]`).
6. *`Not (a = b)`, `a != b` and `Nat.equal a b = False` facts* (the splits): 5 sites, all
   `Nat.leNeSucc` (`a <= b` and `a ≠ b` give `a < b`): Day 4 `mixStep`, `fewerRolls`; Day 8
   `lookupRange`, `memRange`, `memPairs`.
7. *Rewrite rules without a goal* (31 mentions): `Nat.addOne b`, `addZero x`, `addSucc a c`,
   `addComm`, `addAssoc` inside `rewrite …` lists and `Eq.cong (x => …) (Eq.sym (Nat.addOne j))`
   (Day 1, 2, 4 `Part1.sw` `taken`, 6, 7). `omega` needs its goal: `(omega: Succ j = j + 1)` works
   (Day 1 `stepRight`), but a named lemma reads as well and I left them. Not a stage 2
   capability; either keep them or give `rewrite` an `omega` form.
8. *`Int`* (45 mentions in Days 1 and 2): `Int.subNatNat`, `modNat`, `toIntSumBy`,
   `sumByMulLeft`, `toNat`, `mulZero`, `addSubCancel`, `zeroAdd`, `addZero`: only about four are
   linear `Int` steps an `Int` stage would close (`weightsOne`'s `d + (1 - d) = 1`,
   `divisorWeightsTop`, `divisorWeightsAll`, one `mulZero`); the rest are `Int.subNatNat`
   and `modNat` computation lemmas or sums.
9. *Case analysis on a numeral argument*: Day 4 `keepFloor` and `keepRollGe` (twelve clauses
   `0, 1, 2, 3, 4, Succ^5 n`) are about the program's `keep`, a `match` on `w`: not arithmetic.
   `||` and `if` as hypotheses: no AoC site needs them (`isProblem`'s `||` conjunct was
   ignored without harm; the one `if`, Day 3 `bestLengthStep`, is paired with `min`).

**Recommended order for stage 2**, by AoC sites unlocked (a site is a proof step that stays a
lemma call, or an `omega` with a listed fact that a feature would drop):

| # | Feature | AoC sites | Notes |
|---:|---|---:|---|
| 1 | `a - b` (with `x - y = 0` / `y + (x - y) = x` facts from case splits, §6.7) | about 30 | the one that matters; includes `subZeroLe`, the `rangeEnd`/`rangeIn`/`blockCount` lemma facts, Day 1's `highest - m` and Day 3's `rest.length - k` |
| 2 | Refute contradictory facts for a goal that isn't arithmetic | 20 | one rule, no new arithmetic; makes `Void.exfalso omega` a bare `omega` (whether that reads better is a taste call; the checker side is free) |
| 3 | `Nat.max`/`min` (cheap bounds first, §6.7) | 8 listed facts + 12 equations | the 8 drop `Nat.leMax…`; the equations need `omega` as a rewrite rule with a type |
| 4 | Products of atoms up to commutativity | about 10 | `Nat.mulComm` facts; not linear arithmetic, but the cheapest way to shrink Day 2's non-linear residue |
| 5 | `Not (a = b)` / `Nat.equal … = False` facts (splits) | 5 | the `Nat.leNeSucc` sites |
| 6 | `Int` atoms | about 4 | `weightsOne`, `divisorWeightsTop`, `divisorWeightsAll`, one `mulZero`; the rest of Days 1 and 2's `Int` proofs aren't omega-shaped |
| 7 | `%`, `/` by positive literals | 0 | AoC divides by variables; deferred unless another user needs it (§6.7's order should put it last) |
| 8 | `if`, `||` facts | 0 to 1 | Day 3 `bestLengthStep` once `min` is in; no `||`/`if` hypothesis needed arithmetic anywhere |

`stitchwort test --no-cache` in `aoc/` after the conversion: 135 tests, 135 passed, 0 failed
(**[run]**, one run).

Two readings of this against §8.2: `-` first matches the plan, but `%`/`/` by literals, listed
there next to `-`, would not have helped any AoC proof, and the cheap fallback (item 2) wasn't
in the plan at all. The failure-message work (D547 `auto` fallback) is unaffected.

## As built (stage 2)

SW-331 (D545's stage 2, approved as D574) built the features ranked in "Stage 1 on AoC" in
that order, except `Int` (below), then converted the AoC sites they unlock. Everything below is
**[checked]** against the files named and **[run]** with the release CLI built from this
branch. User-facing description: [docs/syntax.md](../syntax.md), "`omega`".

**The checker change** (`std/Omega/Omega.sw`), as §6.7 and the review's point 4 asked:
auxiliary atoms whose environment entry is the real source term, related to their arguments
by facts, with each case's rows following from a proved lemma. Four new `Omega.Fact`
constructors and one certificate step:

```
| FSub (t a b)    -- holds: eval t = eval a - eval b
| FMax (t a b)    -- holds: eval t = Nat.max (eval a) (eval b)
| FMin (t a b)    -- holds: eval t = Nat.min (eval a) (eval b)
| FNe (a b)       -- holds: Not (eval a = eval b)

| Cases (f: Nat) (left: Omega.Cert) (right: Omega.Cert)   -- in Omega.Cert
```

| Fact | Rows that always hold (`Omega.Fact.rows`) | `Fact.left` | `Fact.right` |
|---|---|---|---|
| `FSub t a b` | `t <= a`, `a <= t + b` | `b <= a`, `t + b = a` | `a < b`, `t = 0` |
| `FMax t a b` | `a <= t`, `b <= t` | `a <= b`, `t = b` | `b < a`, `t = a` |
| `FMin t a b` | `t <= a`, `t <= b` | `a <= b`, `t = a` | `b < a`, `t = b` |
| `FNe a b` | none | `a < b` | `b < a` |

The cases are lists of ordinary facts, so a branch's rows are `Facts.rows` of them, appended
to the rows before the split (`checkCert` now also takes the facts, for `Omega.getFact`).
`Cases f` is refused unless fact `f` exists and has cases (`Omega.Fact.splits`); a missing
fact reads as `0 <= 0`, which has none. The search never invents a fact: `t` is an atom whose
environment entry the compiler writes (`a - b` itself), and the `FSub` fact's proof is
`rfl`, which the kernel checks by conversion. `a <= t + b` is the bound the review didn't
list: it holds for truncated subtraction whichever side is larger, and with `t <= a` it closes
most subtraction goals without a split.

**The proof** (`std/Omega/Sound.sw`, 269 → 370 lines), still with no assumption or
extensionality: `Omega.leSubAdd` (`a <= (a - b) + b`, by induction), `subLeLeft`,
`subLeAdd`; one lemma per fact for the cases, each a `Bool.inspect` on the case condition
using existing `Nat` lemmas (`subCases`: `Nat.addSubCancel`, `subEqZero`; `maxCases`:
`maxRight`, `maxLeft`; `minCases`: `minLeft`, `minRight`; `neCases`: `leNeSucc`);
`factCases` dispatching them; `getFactHolds`; `casesHold` (the branch for the case that holds
gets its rows); and a `Cases` arm in `checkCertSound`, which now carries the facts' proofs.
`Omega.prove` and `proveEq` keep their statements. New checker tests: `Cases` accepted on a
subtraction, refused on a fact without cases, on a missing fact, and when a branch uses the
other case's row.

**The search** (`omega_search.rs`): `Problem` has the facts with cases (`Case`: the fact's
number and each case's rows). The unsplit attempt has the rows that always hold (§6.7's
"cheap bounds before splitting"). When it finds a model, the search splits on the first fact
with cases whose *both* cases the model violates (a split that leaves the model alive in one
branch can't help), before a fractional split, and never twice on one fact in a branch; the
six-level depth limit now counts both kinds. Case rows are numbered like split rows (nothing
is written before a split), and grouping joins every atom a case mentions. Unit tests:
`cheap_bound_needs_no_split`, `subtraction_splits_on_demand`,
`subtraction_without_its_cases_fails`, `subtraction_false_goal_fails`, `not_equal_splits`,
`replay_refuses_a_missing_case`.

**The elaborator** (`omega.rs`):

1. *Subtraction, `max`, `min`.* A stuck `Nat.sub a b`, `Nat.max a b` or `Nat.min a b` is an
   atom; its arguments are quoted too (nested operations get their own facts), and the
   atom's fact goes in the candidates with proof `rfl`. `max` and `min` are also recognised
   after they've computed: `Nat.max` unfolds to `Bool.ifThenElse (Nat.leq a b) (u => b)
   (u => a)` **[run]**, so an `if` on `Nat.leq a b` whose branches are `b`/`a` is `max a b`
   and `a`/`b` is `min a b`. Messages name the atom `Nat.max a b`, not the `if`.
2. *Any goal.* A goal that isn't arithmetic is proved by refuting the facts (`GVoid`), then
   `Void.exfalso [goal]` for a proposition or `Void.absurd [goal]` for a type of data in
   `Type` (read off the goal: an equation, or a data type's declared sort). When the facts
   don't contradict, the error is the old "unsupported structure" with a note saying so.
3. *Products up to commutativity.* Each `x * y` atom remembers its factors; when another is
   `y * x` (same terms), the candidates get the fact `x * y = y * x` with proof
   `Nat.mulComm x y`. Still two atoms, so no checker change; `(x * y) * z` and `x * (y * z)`
   stay different (`omega-product-order.sw`).
4. *`a != b`.* `Not (a = b)` facts (also `a != b`) are `FNe`; `Nat.equal a b = False` and
   `= True` are read through `Nat.equalFalse` and `Nat.equalSound`.

**Examples.** `examples/accept/omega-stage2.sw` (24 theorems: subtraction with and without
splits, `max`/`min`, the three ways of writing `a != b`, products both ways, a `List`
equation, a `Bool` equation and a `List Nat` value from contradictory facts);
`examples/reject/omega-sub-false.sw`, `omega-max-false.sw` (the models name the atoms),
`omega-no-contradiction.sw`, `omega-product-order.sw`. `omega-neq-fact.sw`, which recorded
the old limitation, now proves and is removed.

**Costs [run]** (`STITCHWORT_TIMINGS=decls`, elaboration + kernel, one run): the cheap-bound
goals (`a - b <= a`, `a <= Nat.max a b`) 0.3 ms and about 10,000 steps, like stage 1's
simplest; one case split (`(a - b) + b = a` from `b <= a`) 1.0 ms, 34,000 steps; the most
expensive, `a - b - c = a - (b + c)` (two equations, three subtraction atoms, nested
splits), 3.2 ms and 121,000 steps. `Omega/Sound.sw` now checks in about 16 ms (elaboration + kernel; loaded once per program).

**On AoC.** Theorem statements, programs and tests unchanged; one helper deleted (Day 4
`subZeroLe`, whose callers now pass its premise straight to `omega`). The kinds of change:

1. *`Void.exfalso omega` → `omega`* (and `Void.exfalso (omega [facts])` → `omega [facts]`):
   all 20 sites, Days 2, 3, 4, 5, 7, 8.
2. *Listed facts dropped*: `Nat.leMaxLeft/Right`, `minLeLeft` (Day 5 `topGe`, `coveredTop`,
   `mergedContains`; Day 2 windows), `Nat.addSubCancel` (Day 2 `twiceBlockCount`,
   `blockCountRep`), `Nat.predLeSucc` (Day 2), `Nat.mulComm` (Day 2, six sites).
3. *Lemma-call steps → `omega`*: Common's whole `Range.sw` counting (`countFrom`'s three-step
   calcs are two steps), Day 4 `fewerRolls`/`mixAbove` and Day 8 `lookupRange`/`memRange`/
   `memPairs` (`Nat.leNeSucc … (Nat.equalFalse …)` → `omega`), Day 3's `Nat.minLeft`/
   `addSubLe`/`leSubAdd` arguments, Day 2's `writtenAsFillsDigits` five-line calc.
4. *A named rewrite rule → a stated one*: where the step is used by `rewrite` or `Eq.cong`,
   the lemma became `(omega: hi - lo = Succ (hi - Succ lo))`, `(omega: Nat.max s bLo = bLo)`,
   `(omega: n + 1 - 1 = n)` (Days 1, 2, 3, 6). These say the equation instead of naming it;
   whether that reads better than `Nat.subSuccRight lo hi h` is a taste call worth Matt's look.
   One Day 3 site (`bestLengthStep`) now repeats a long `Nat.min k (List.length …) = k` type
   in the annotation.

Per day, as in "Stage 1 on AoC" (non-blank non-comment lines of `Proofs/`; check time is the
`Aoc.DayNN.Proofs` row of `STITCHWORT_TIMINGS=1 stitchwort check --no-cache`, elaboration +
kernel, median of five runs, both columns with this branch's compiler). "Lemma calls" now
counts the stage-1 list **plus** the lemmas stage 2 covers (`addSubCancel`, `subEqZero`,
`subSuccRight`, `addSub`, `subLe`, `leSubAdd`, `addSubLe`, `maxLeft/Right`, `minLeft/Right`,
`leMin`, `leNeSucc`, `mulComm`), so the "before" column is larger than stage 1's "after".

| Day | lines before → after | lemma calls before → after | `omega` | check ms before → after |
|---|---:|---:|---:|---:|
| Common | 55 → 49 | 16 → 1 | 16 → 12 | 10.3 → 22.2 |
| 1 | 139 → 139 | 13 → 10 | 6 → 8 | 40.4 → 43.2 |
| 2 | 1044 → 1035 | 75 → 34 | 68 → 83 | 279.8 → 300.7 |
| 3 | 158 → 158 | 9 → 0 | 20 → 28 | 27.9 → 36.5 |
| 4 | 880 → 878 | 6 → 3 | 46 → 47 | 426.0 → 433.7 |
| 5 | 143 → 143 | 3 → 0 | 12 → 12 | 21.4 → 21.9 |
| 6 | 145 → 145 | 2 → 1 | 1 → 2 | 22.6 → 24.5 |
| 7 | 389 → 389 | 5 → 5 | 16 → 16 | 72.7 → 73.5 |
| 8 | 541 → 541 | 4 → 0 | 24 → 28 | 712.6 → 727.5 |
| **all** | **3494 → 3477** | **133 → 54** (-59%) | **209 → 236** | **1613.7 → 1683.7** (+4.3%) |

What the numbers say:

- *Lines* barely move again (-17): the removed lemma calls were arguments inside lines that
  stay. The 79 lemma mentions that went are the point: what's left in those places is a bare
  `omega`, a fact about the program, or the equation itself.
- *Check time* is +70 ms (+4.3%), more than stage 1's +1.2%: case splits cost. The largest
  relative change is Common, 10.3 → 22.2 ms, almost all `countFrom` (4.4 → 14.0 ms: its
  `omega`s hold `Succ r.to - Nat.max r.from s`, a subtraction over a `max`; that the cost
  is the nested case splits is **[inferred]**, not traced). Days 2 and 3 rise by 21 and 9 ms
  over many sites.
- *What's left* in the "lemma calls" column outside Day 2 is "Stage 1 on AoC"'s item 7, rewrite
  rules without a goal: `Nat.addOne`, `addZero`, `addSucc`, `addAssoc` in `rewrite` lists
  (Days 1, 4, 6, 7; 17 mentions), and two `Nat.leqFalseOfLess` that build a `Bool` equation
  for a program's `&&`. Day 2's 34 are mostly inside its non-linear products and `%`/`/` by
  variables. **[checked]** by grep.

**Not built.**

- *`Int` atoms* (item 6 of the ranking, about 4 AoC sites, all in Day 2: `weightsOne`'s
  `d + (1 - d) = 1`, `divisorWeightsTop`, `divisorWeightsAll`, one `Int.mulZero`). It needs
  `Int` syntax, `Int` facts and goals over the environment's `Int` list (no non-negativity),
  their linear forms and a second `linEval`: a second soundness layer for four one-line
  lemma calls. Left for a later lane; the environment and rows already have the `Int` side.
- *`/` and `%` by literals* and *`if`/`||` facts*: no AoC site (as the ranking said).
- *Splits on combinations of atoms* (`omega-rational-model.sw`'s `x - z`) and a smaller
  budget for the D547 `auto` fallback: unchanged from 1b.

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
searched (option C, §5). (Milestone 1a has since built and proved the checker, with `Divide`
and `Split`, and measured it with real proofs: [As built](#as-built-milestone-1a), "Costs".)

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
