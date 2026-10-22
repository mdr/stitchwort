# Proposal: rewriting a hypothesis (`rewrite p at h`)

**Status:** draft 1, 22 October 2026. Ticket SW-209, decision D461 (write this note).
Decisions D463 to D465 ([§7](#7-decisions)) were decided by Matt on 22 October 2026 as
recommended; built in SW-209 (see [As built](#as-built-sw-209)). Related:
[calc-rewrite.md](calc-rewrite.md) §6.4, §6.5 and its Stage 3 ("rewrite in the body's own
type when no goal is known"); [docs/aoc-2025.md](../aoc-2025.md), day 2 and day 3 pain points.

**The short answer.** `rewrite p in t` can only change the *goal* (what is being proved). To
change the type of a fact you already have, you write `J` with a hand-written motive, or you
rearrange the proof so that the fact sits where the goal says what it must become. I recommend
one new form, borrowed from Lean's `rw [p] at h`:

```
rewrite p at h in t      -- in t, h has its type with p's left side replaced by its right side
rewrite p at h           -- the rewritten h itself, as a term (also where no goal is known)
```

It reuses the existing search and motive check unchanged, pointed at `h`'s type instead of the
goal, and builds the same kind of `J` term. Roughly a day and a half to build, then half a day to
replace about two dozen `J`s in `aoc/` and the standard library. I also recommend **dropping**
calc-rewrite.md's Stage 3 item (`rewrite p in t` silently rewriting `t`'s type when no goal is
known): `at` says the same thing explicitly.

Two findings change the ticket's premise **[run]**:

- The day 3 workaround is no longer needed. `pickSub`'s `J` and its helper `pickSubStep` can both
  go today: `pickStep` became `rfl` (SW-246), and `match e:` now refines hypotheses as well as the
  goal (SW-193; `docs/syntax.md`, "Hypotheses" under generalised `match`). So the `match e:` half
  of the ticket is already done; what is left is a doc correction and a cleanup ([§1.4](#14-day-3-picksub-already-fixable-today)).
- Some of the day 2 `J`s can already be replaced by today's `rewrite`, by moving it to a position
  where the goal is known. But there is a family of proofs where nothing can replace `J` today,
  because the goal has computed to `False = True` and no longer mentions anything to rewrite
  ([§1.1](#11-a-fact-whose-target-computes-away)).

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given, or in a source
  listed at the end;
- **[run]**: a Stitchwort program run on 22 October 2026 with the release CLI at `dcb087f8`
  (scratch files and temporary edits, not committed; each is quoted where it is used);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [0. Background in two paragraphs](#0-background-in-two-paragraphs)
- [1. The problem, with real examples](#1-the-problem-with-real-examples)
- [2. How other languages do it](#2-how-other-languages-do-it)
- [3. Options for Stitchwort](#3-options-for-stitchwort)
- [4. The recommended form in detail](#4-the-recommended-form-in-detail)
- [5. Recommendation, effort and stages](#5-recommendation-effort-and-stages)
- [6. What is not included](#6-what-is-not-included)
- [7. Decisions](#7-decisions)
- [As built (SW-209)](#as-built-sw-209)
- [Sources](#sources)

## 0. Background in two paragraphs

A proof of `a = b` can be used to move any fact about `a` to the same fact about `b`. The
primitive that does it is `J`: `J (y q => P y) base e`, where `e: a = b` and `base: P a`, proves
`P b`. The function `y q => P y` is the **motive**: it says which places in the fact are being
changed (every `y`). Writing the motive by hand is tedious and repeats the whole fact
(`docs/syntax.md`, the `J` row of the table of built-ins **[checked]**).

`rewrite p in t` (built in SW-153) works the motive out itself, but only for the **goal**: it
looks for `p`'s left side in the type the expression is checked against, replaces it, and
checks `t` against the result (`docs/syntax.md`, "`rewrite`" **[checked]**). It needs a goal
(`E-REWRITE-NO-GOAL` otherwise), and the goal it searches is the goal *as it computes*. Nothing
rewrites the type of a fact you already hold. The design note said so: "Rewriting a hypothesis
in the context (Lean's `rw … at h`)" is listed under "Not included" (calc-rewrite.md §6.5
**[checked]**).

## 1. The problem, with real examples

There are 76 `J (` in `aoc/src` and the standard library (`crates/elab/src/std`) **[run:
grep]**. About two dozen of them carry a fact along an equation (a base that isn't `rfl`); the
rest build an equation with an `rfl` base, or deliberately change only one occurrence, which
this proposal doesn't help with ([§6](#6-what-is-not-included)) **[inferred, from reading the
grep output]**.

### 1.1 A fact whose target computes away

`Nat.nonzeroOfPos` (`crates/elab/src/std/Nat/Arith.sw:129` **[checked]**):

```
theorem Nat.nonzeroOfPos (d: Nat) (h: 1 <= d): d != 0 := e => Bool.falseNotTrue (J (y q => 1 <= y) h e)
```

Given `e: d = 0`, `h: 1 <= d` becomes `1 <= 0`, which computes to `False = True`, and
`Bool.falseNotTrue` turns that into `Void`. Every way of writing it with today's `rewrite` fails
**[run]**:

```
e => Bool.falseNotTrue (rewrite <- e in h)              -- goal known
e => Bool.falseNotTrue (rewrite <- e in h: 1 <= 0)      -- with an ascription
e => let h0: 1 <= 0 := rewrite <- e in h                -- with a typed let
     Bool.falseNotTrue h0
```

All three give the same error:

```
[E-REWRITE-NOTHING] Error: `rewrite` found no `0` in the goal
    looking for `0`
  Note 1: goal: `False = True`
```

The goal is searched as it computes, and `1 <= 0` has already become `False = True`: there is
no `0` left to turn back into `d`. Rewriting `h`'s type instead works, because `h: 1 <= d` still
mentions `d`. With this proposal:

```
theorem Nat.nonzeroOfPos (d: Nat) (h: 1 <= d): d != 0 := e => Bool.falseNotTrue (rewrite e at h)
```

The same shape, "a hypothesis about `y`, an equation `y = 0`, so `False = True`", appears at
`Nat/Arith.sw:381`, `Nat/Divides.sw:44`, `aoc/src/Aoc/Day02/Proofs/Part2.sw:484` and `:510`
**[checked]**. The last one, in `writtenOfDivides`, transports an unnamed fact:

```
| Zero, e => Void.exfalso (Bool.falseNotTrue (J (y q => 1 <= y) (blockCountPos x) e))
-- would be
| Zero, e => Void.exfalso (Bool.falseNotTrue (rewrite e at blockCountPos x))
```

### 1.2 Day 2, `sumIdsEq`: a hypothesis in a contradiction

`aoc/src/Aoc/Day02/Proofs/Repeated.sw:224` **[checked]**, inside a `match t: Nat.leq from y`
branch where `t: Nat.leq from y = False`, and the lambda gets `hx1: from <= x` and `e: y = x`:

```
(x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym (J (z q => Nat.leq from z = True) hx1 (Eq.sym e))) t))
```

The `J` moves `hx1` from `x` to `y`. It sits under `Eq.sym`, where the goal isn't fully known,
which is why the AoC notes say `rewrite` can't be used here (docs/aoc-2025.md, day 2 pain point
2 **[checked]**). There *is* a way today **[run]**: rewrite `t` instead of `hx1`, in the second
argument of `Eq.trans`, whose expected type `Nat.leq from x = ?c` is known enough:

```
(x hx1 hx2 e => Bool.trueNotFalse (Eq.trans (Eq.sym hx1) (rewrite <- e in t)))
```

It checks, but you have to see that `Eq.trans`'s middle term is fixed by the first argument, and
turn the rewrite round (`<-`, and the other fact). With this proposal you say what you mean,
"`hx1`, but about `y`":

```
(x hx1 hx2 e => rewrite <- e at hx1 in Bool.trueNotFalse (Eq.trans (Eq.sym hx1) t))
```

### 1.3 Day 2, `twiceBlockCount`: an unnamed fact

`Repeated.sw:333-340` **[checked]**, with `e: writeTimes (Succ j) b 2 = x` and
`hq: writtenAs (Nat.digits x) (Succ j) 2 = False`:

```
(e => Bool.trueNotFalse (Eq.trans
  (Eq.sym (J (y q => writtenAs (Nat.digits y) (Succ j) 2 = True)
    (twiceDigits j b h1 (calc …))
    e))
  hq))
```

Today's workaround **[run]** swaps the contradiction round (`falseNotTrue`, `Eq.sym hq` first)
so that the transported fact lands where the goal is known:

```
(e => Bool.falseNotTrue (Eq.trans (Eq.sym hq)
  (rewrite <- e in twiceDigits j b h1 (calc …))))
```

With this proposal, the fact is rewritten where it is, in the order the argument goes
**[inferred]**:

```
(e => Bool.trueNotFalse (Eq.trans (Eq.sym (rewrite e at twiceDigits j b h1 (calc …))) hq))
```

The same pattern is at `Part2.sw:162`, `:389`, `:468` and `:506` **[checked]**.

### 1.4 Day 3, `pickSub`: already fixable today

`aoc/src/Aoc/Day03/Proofs/Best.sw:73-94` **[checked]**. The notes say `pickSub` "needed `J` to
move [a hypothesis] across `pickStep` and a helper that cases on the `Decidable` itself
(`pickSubStep`), since `match e:` too only generalises the goal" (docs/aoc-2025.md, day 3
**[checked]**). Two things have changed since:

- `pickStep` is now `rfl` (SW-246, D414, recorded in the same section **[checked]**), so `h`
  already has the rewritten type up to computation. Replacing the `J (p q => …) h (pickStep …)`
  by plain `h` checks **[run]**.
- `match e:` now copies hypotheses whose types mention the scrutinee (`docs/syntax.md`,
  "Hypotheses" **[checked]**). So the helper isn't needed either. This checks **[run]**:

```
  | Succ w, Cons x more, c, after, hx, hc, s, h =>
    rewrite pickStep w x more c after in
      match d: Bool.decTrue (Nat.leq (Succ (Fin.toNat c)) (Fin.toNat x)) with
        | Yes lt => pickSub t w more x more (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) (s2 g2 => hx (Cons x s2) (Inl (Both rfl g2))) s h
        | No ge  => pickSub t w more c after (s2 g2 => hx s2 (List.subsequenceCons x s2 more g2)) hc s h
```

So **`match e:` needs no new design**: it already changes the types of hypotheses. What remains
is to apply this simplification and correct the day 3 note (stage 2 below).

### 1.5 What the examples have in common

- The fact to change is a hypothesis or a term, not the goal.
- Its type still mentions the thing to replace, even when the goal it is heading for has
  computed past it (§1.1). That is the case today's tools cannot do without `J`.
- Where a workaround exists (§1.2, §1.3), it means restructuring the proof around where
  Stitchwort happens to know the goal, and often flipping `<-`.

## 2. How other languages do it

| | Rewrite a hypothesis | Rewrite a term's type | Replace a variable everywhere | Library function |
|---|---|---|---|---|
| **Lean 4** | `rw [p] at h` (`at h₁ h₂ ⊢`, `at *`) | `p ▸ e` | `subst h` | `Eq.subst`, `Eq.mpr` |
| **Rocq** | `rewrite H in H'` | (tactic world; no term form) | `subst x` | `eq_rect`, `eq_ind` |
| **Agda** | `rewrite p` also rewrites the clause's argument types | no | (pattern matching on `refl`) | `subst P p x` |
| **Idris 2** | no: `rewrite p in e` rewrites the goal | no | (pattern matching on `Refl`) | `replace` |

**Lean 4.** The reference: "`rewrite [e] at l` rewrites `e` at location(s) `l`, where `l` is
either `*` or a list of hypotheses in the local context. In the latter case, a turnstile `⊢` or
`|-` can also be used, to signify the target of the goal." `rw` is `rewrite` followed by an
attempt at `rfl` **[checked: [L1]]**. A typical use (this snippet and the Rocq one below are
illustrations, not run **[unverified]**):

```lean
example (d : Nat) (h : 1 ≤ d) (e : d = 0) : False := by
  rw [e] at h        -- h : 1 ≤ 0
  exact absurd h (by decide)
```

What happens to the old `h` is stated for `simp at`: "If the target or another hypothesis
depends on `hᵢ`, a new simplified hypothesis `hᵢ` is introduced, but the old one remains in the
local context" **[checked: [L1]]**; `rw … at` behaves the same way **[unverified]**. In terms,
`h ▸ e` "has type `p b`" given `e : p a`, and "If the context provides an expected type, it
rewrites the expected type, else it rewrites the type of e" **[checked: [L2], quoted in
calc-rewrite.md §4.2]**. `subst h` "substitutes each hypothesis `x` with a definition found in the
local context, then eliminates the hypothesis", for `h : a = b` where one side is a variable
**[checked: [L1]]**.

**Rocq.** `rewrite H in H'` uses the same `in` clause as other tactics; the error for a missing
match names the hypothesis: "Found no subterm matching `term` in `ident`" **[checked: [R1]]**.
`subst x`, for a hypothesis `x = t` or `t = x`, "replaces `x` with `t` everywhere in the
hypotheses and the conclusion and clears `x` and the hypothesis from the context" **[checked:
[R1]]**. `replace a with b` swaps a term for another and leaves `b = a` as a new goal
**[checked: [R1]]**.

```coq
Lemma t (d : nat) (h : 1 <= d) (e : d = 0) : False.
Proof. rewrite e in h. inversion h. Qed.
```

**Agda.** There is no separate "at h": `rewrite` is with-abstraction, and with-abstraction
generalises "the goal type and the type of the original arguments" over the term, so a clause's
arguments are rewritten along with the goal. The manual's example "used the commutativity proof
to rewrite `a + b` to `b + a` in the type of `t`" (an argument) **[checked: [A1]]**. For anything
else there is the library function `subst : Substitutive _≡_ ℓ`, where
`Substitutive _∼_ p = (P : A → Set p) → P Respects _∼_`: given `x ≡ y`, it turns `P x` into
`P y`, with the motive `P` given by hand **[checked: [A2], `PropositionalEquality/Core.agda:85`
and `Relation/Binary/Definitions.agda:243`]**.

**Idris 2.** `rewrite p in e` only rewrites the goal. The documentation's own example of
"rewriting an argument" works the way §1.2's workaround does: it rewrites the goal so that the
argument fits it, and notes "here we need to supply reverse equality, i.e. `y=x` instead of
`x=y`" **[checked: [I1]]**. `replace : (0 rule : x = y) -> prop x -> prop y` is the library
transport; `rewrite` "calculates the property and applies `replace`" **[checked: [I1]]**.
Without `rewrite`'s help, `replace` usually needs its `prop` given explicitly
(`replace {p = \y => …}`) **[unverified]**.

**What to take from this.**

- The two systems built around tactics (Lean, Rocq) have exactly this feature, spelled "at h"
  (Lean) or "in H" (Rocq). Stitchwort's `in` already means "the rest of the proof", so the Lean
  spelling fits.
- Lean's term-level `▸` guesses: goal first, then the term's type. That is calc-rewrite.md's Stage
  3 item. It is convenient and also a known source of confusing errors, since which one happened
  depends on whether the elaborator knew the expected type at that moment **[inferred]**.
- Agda's "rewrite the arguments too" is what Stitchwort's `match e:` already does for
  hypotheses (§1.4); `rewrite` in Stitchwort is a term, not a clause, so it has no "arguments" to
  generalise.
- A library function (`subst`, `replace`) is `J` with the arguments reordered: the motive still
  has to be written or inferred from a known goal.

## 3. Options for Stitchwort

House style: Stitchwort reads like Scala/TypeScript where it can (`(x: Nat)`, `x => …`,
`let x: T := …`), and its proof keywords are words, not symbols (`rewrite`, `calc`, `in`, `<-`)
(`docs/syntax.md` **[checked]**).

### Option A: `rewrite p at h in t` and `rewrite p at h` (recommended)

- **Reads:** "rewrite with `p` at `h`, in `t`". In `t`, `h` has the new type; the whole proves
  whatever `t` proves. Without `in`, the value is the rewritten `h`.
- **Elaborates:** take `h`'s type `H`, run the existing search for `p`'s left side in `H`
  (instead of in the goal), get the motive `M` with `H = M a`, and build `J M h p : M b`. With
  `in t`, that is bound as a new `h` for `t`. Details in [§4](#4-the-recommended-form-in-detail).
- **Errors:** the existing ones, with "in the type of `h`" for "in the goal".
- **Covers:** §1.1 to §1.3, with or without a known goal.

### Option B: Stage 3's "no goal, so rewrite the body's type"

`let h2 := rewrite p in h`, with no type, would rewrite `h`'s type (Arend's and Lean's `▸`
fallback, calc-rewrite.md §6.4).

- **Reads:** the same words mean two opposite things. With a goal, `rewrite p in t` changes the
  goal and `t` must fit the changed goal. Without one, it changes `t`'s type. Whether there is a
  goal is invisible in the source: `Bool.falseNotTrue (rewrite e in h)` has one (`False = True`),
  so §1.1 still fails, while the same text in an untyped `let` would work.
- **Elaborates:** like A, without the rebinding.
- **Errors:** an error in one mode is reported in terms of that mode, and the user may have
  expected the other.
- **Covers:** §1.1 only through an extra `let`; §1.2 and §1.3 only after restructuring.

### Option C: a library function

`Eq.subst (y => P y) e h` or Idris's `replace`: `J` with its arguments in a friendlier order.

- **Reads:** fine, but the motive is still written by hand.
- **Elaborates:** with Lean's `elab_as_elim` trick, the motive could be inferred from a known
  goal. That brings back the "needs a goal" limit, and §1.1 has no usable goal.
- **Covers:** nothing that `J` doesn't already cover.

### Option D: `subst e` (Lean, Rocq)

For `e: x = t` with `x` a variable, replace `x` everywhere, in the goal and every hypothesis.

- **Reads:** short, and powerful. In §1.3, `subst e` would turn `hq` into a fact about
  `writeTimes (Succ j) b 2`, and `twiceDigits …` would contradict it directly.
- **Elaborates:** like a `match` on the equation: re-bind the goal and every hypothesis
  mentioning `x`. That is close to the generalisation machinery `match e:` has, but it is a new
  construct with a larger surface; only helps when one side is a variable (not in §1.1's
  `Divides.sw:44`, where the equation is between two expressions).
- **Covers:** some cases, more neatly; not all.

Not considered further: Rocq's `rewrite H in H'` spelling, because `in` already introduces the
body; a symbol like Lean's `▸`, against the house preference for words.

## 4. The recommended form in detail

### 4.1 Forms

| form | meaning |
|---|---|
| `rewrite p at h in t` | in `t`, `h` has its type with `p`'s left side replaced by its right side |
| `rewrite p at h` | the rewritten `h` (as `rewrite p at h in h`) |
| `rewrite p, q at h in t` | `p`, then `q` on what is left, in `h`'s type |
| `rewrite <- p at h in t` | right to left |
| `rewrite p at f x y` | the term `f x y` with its type rewritten; no `in` (there is no name to rebind) |

The target is any expression; `in` needs it to be a single local name (D464). To rewrite the
goal as well, nest: `rewrite p at h in rewrite p in t`. Several targets at once (Lean's
`at h₁ h₂ ⊢`) are left out: nesting covers them, and no AoC proof needs it **[inferred]**.

### 4.2 Elaboration

1. Elaborate the target and infer its type `H` (with solved metavariables read back, as the
   goal is today).
2. For each rule in turn, run today's `rewrite_once` (`crates/elab/src/rewrite.rs:185`
   **[checked]**) with `H` in the place of the goal. It finds the occurrences by the same rules
   (keyed, outermost first, never under a binder the type introduces, one budget for the whole
   `rewrite`), and checks the motive `M` the same way (`E-REWRITE-MOTIVE`, then the round trip
   `M a ≡ H`). `H` becomes `M b`.
3. Build the term. The direction is the opposite of the goal case, and simpler: for the goal,
   `t: M b` has to become `M a`, so today's term is `J M t (Eq.sym p)`; for a hypothesis,
   `h: M a` becomes `M b`, so the term is `J M h p` (`J M h (Eq.sym p)` for `<-`). For several
   rules, the `J`s nest the other way round from the goal case.
4. With `in t`: bind the result under the name `h` (a `let`, so it shadows the old `h`) and
   elaborate `t` with the expected type, if any. Without `in`: the result is the term, its type
   is `M b`, and if there is an expected type it is compared by conversion as for any other
   term.

The kernel is unchanged: it re-checks the `J` term as it does every `rewrite` today.

Because it never needs a goal, `rewrite p at h` works in inferring positions too: an untyped
`let`, the head of an application, the argument of `Eq.sym`.

### 4.3 The old `h`

The new `h` shadows the old one; nothing else changes. A hypothesis whose type mentions the
old `h` (rare: a proof about a proof) still mentions the old one, which is what Lean's `simp at`
does in the same situation (§2). This is unlike `match e:`, which copies dependent hypotheses;
copying them here would mean rewriting their types too, which `J` can't do in one step
**[inferred]**.

### 4.4 Errors

Same codes, with the target in place of "the goal". For example, with `e: d = 0` and a
hypothesis `h: 1 <= n` that doesn't mention `d` (a sketch, not output):

```
[E-REWRITE-NOTHING] Error: `rewrite` found no `d` in the type of `h`
    ╭─[ a.sw:2:…]
  2 │ … rewrite e at h …
    │           ┬
    │           ╰── looking for `d`
  Note 1: `h`: `Nat.leq 1 n = True`
  Note 2: occurrences are looked for by their outer function and compared by computing, …
```

- `E-REWRITE-NOTHING`, `E-REWRITE-MOTIVE`, `E-REWRITE-RULE`, `E-REWRITE-BUDGET`: as today.
- New, `E-REWRITE-TARGET`: `in` after a target that isn't a local name ("only a name can be given
  a new type for the rest of the proof; drop `in …` to use the rewritten term directly").
- After the rewrite, a mismatch between the rewritten `h` and what was expected is the usual
  `E-TYPE-MISMATCH`, with a note "after `rewrite … at h`, `h` is `…`".
- `E-REWRITE-NO-GOAL`'s second hint changes to mention `at`: "to rewrite the type of `t` instead
  of a goal, write `rewrite p at t`".

### 4.5 With the rest of the language

- **`rewrite p, q in t`.** `at` sits between the rules and `in`, and the rule list is the same:
  `rewrite p, q at h in t`. Rules are applied left to right to `h`'s type, as they are to the
  goal.
- **`calc`.** `_ = c := rewrite p at h` is a step proved by the rewritten `h`, checked by
  conversion like any other step proof. It is different from `rewrite p` in a step, which
  rewrites the step's own proposition; both stay valid.
- **Stage 3, "rewrite in the body's own type when no goal is known."** `rewrite p at t` is
  that, made explicit. I recommend removing the item (D465) rather than adding a second,
  implicit way.
- **`match e:`.** Unaffected. It already refines hypotheses (§1.4).
- **Parsing.** `at`, like `in`, becomes special only where a rule can end. It is used as a name
  today: `aoc/src/Aoc/Day07/Proofs/Part1.sw:253` defines `let at: …` and `:299` writes
  `rewrite at b hb2 in …` **[checked]**. That still parses (there `at` begins the rule, which
  isn't a place a rule can end). Passing a variable called `at` as an argument inside a rule
  needs brackets, `rewrite f (at) at h`, as `in` does today.

## 5. Recommendation, effort and stages

**Recommendation.** Option A, with any term as the target (D463, D464); drop Stage 3's implicit
form (D465). Leave `subst` (option D) for later, if proofs ask for it.

**Stage 1: build `at` (about 1 to 1.5 days; one lane).**

- Parser: an optional `at <expr>` after the rule list, ending at `in` or at the end of the
  expression; `at` contextual as above. AST: a `target` field on `Expr::Rewrite`.
- Elaborator: one function beside `check_rewrite` that runs `rewrite_once` over the target's
  type and builds `J M h p`; `infer_rewrite` handles the `at` case instead of erroring. The
  messages in `nothing_found` and friends take "the goal" or "the type of `h`" as a parameter.
- Tests: `examples/accept/rewrite-at.sw` (every form in §4.1, the §1.1 case, `<-`, several rules,
  in a `calc` step, inferring position), `examples/reject/rewrite-at-*.sw` for each error,
  parser tests for `at` as a name. Docs: the `rewrite` section of `docs/syntax.md`, and an "As
  built" note here.

**Stage 2: use it (about half a day; mechanical, exact list).**

- Replace the transport `J`s listed in §1 (Arith.sw:129, :381, Divides.sw:44, Part2.sw:162, 389,
  468, 484, 506, 510, Repeated.sw:221, 224, 334) and those in `Nat/Digits.sw` and `List/Sort.sw`
  where the result reads better; leave the single-occurrence `J`s alone.
- Day 3: drop `pickSub`'s `J` and the `pickSubStep` helper (the `match` in §1.4), and correct the
  day 3 note in `docs/aoc-2025.md`, whose "`match e:` too only generalises the goal" is out of
  date. This part doesn't depend on stage 1 and can go first.
- Correct calc-rewrite.md §6.5 ("Not included") and Stage 3 to point here.

**Risks.** Small. The search and motive check are reused as built; only the direction of the
`J` and the binding are new. The one thing to watch is the form of `h`'s type that is searched:
a parameter's type is stored as elaborated, so `x % d` in it has unfolded as it has in goals,
and the same "searched as it computes" surprises apply (`docs/syntax.md`, "What will surprise
you" **[checked]**).

## 6. What is not included

- **Choosing occurrences.** `twiceAbove` (`Repeated.sw:271`) and `repAbove` (`Part2.sw:96`) need
  a motive that changes one `k` and not another (docs/aoc-2025.md, day 2 pain point 1). That is a
  separate Stage 3 item of calc-rewrite.md, and `at` doesn't change it.
- **Several targets at once, and `at *`.** Nest instead.
- **`subst`.** See option D.
- **Rewriting dependent hypotheses along with `h`.** See §4.3.

## 7. Decisions

| ID | Decision | Recommendation |
|---|---|---|
| D463 | How to rewrite a hypothesis (§3) | [Option A: `rewrite p at h in t`, and `rewrite p at h` for the rewritten term. Not the implicit "no goal" mode, not a library function, `subst` maybe later.] |
| D464 | What may follow `at` (§4.1) | [Any expression, so `rewrite e at blockCountPos x` works without a `let`; `in` only after a single local name.] |
| D465 | calc-rewrite.md Stage 3's "rewrite in the body's own type when no goal is known" (§4.5) | [Drop it: `at` is the explicit form, and one spelling meaning two opposite things depending on an invisible expected type is a trap. `E-REWRITE-NO-GOAL` points at `at`.] |

## As built (SW-209)

Built as §4 describes, with these details.

**Syntax.** `rewrite p, <- q at h in t`, `rewrite p at h`, `rewrite p at <any expression>`.
`at` ends a rule only outside brackets, after the rule's first token, and not after a `.`
(a field `r.at`); `in` ends the target the same way. So `rewrite at b hb2 in …` in
`aoc/src/Aoc/Day07/Proofs/Part1.sw` (a lemma called `at`) still parses, as does
`rewrite p (at) at h` (`crates/syntax/src/parser.rs`, `ends_rewrite_rule`; parser test
`rewrite_at_takes_a_target_before_the_body`). The AST has a `target` field on
`Expr::Rewrite`.

**Elaboration** (`crates/elab/src/rewrite.rs`, `rewrite_at`). The target is inferred (implicit
arguments inserted); its type is searched by the same `rewrite_once` as the goal, which now takes
where it is looking (`Place::Goal` or `Place::Target`). For a target the `J` goes the other way:
the proof is `p` itself (`Eq.sym p` for `<-`), the motive's proof binder is over `a = x`, and
the round trip applies the motive to `a` and `rfl`. Several rules nest as
`J M2 (J M1 h p1) p2`. With `in t`, `h` is bound by a `let` (`Ctx::define`) of the `J` term
for `t`, which is checked against the expected type if there is one and inferred otherwise.
Without `in` and with an expected type, the rewritten type is compared by conversion as for
any term. The kernel is unchanged.

**Errors.** As planned: the existing codes, with "the type of `h`" (or "the type of the term
after `at`") in place of "the goal", and the note `` `h`: `…` `` showing the type searched.
`E-REWRITE-TARGET` for `in` after something that isn't a local name. A mismatch after the
rewrite is `E-TYPE-MISMATCH` with the note "after `rewrite … at`, `h` is `…`".
`E-REWRITE-NO-GOAL` has a third note, "to rewrite the type of a fact `t` instead of a goal,
write `rewrite p at t`". Examples: `examples/accept/rewrite-at.sw`,
`examples/reject/rewrite-at-{nothing,motive,target,mismatch}.sw`.

**Searched as it computes.** As with goals, the target's type is searched in its computed
form, so a rule must mention what the type computes to. Where an inferred type has a
different shape from the one wanted (`Nat.digitsNonEmpty x` is about
`List.length (Nat.digits x)`, not `digitCount x`), an ascription gives the shape:
`rewrite countTimesPeriod x, e at (Nat.digitsNonEmpty x: 1 <= digitCount x)`.

**Stage 2: 30 `J`s replaced**, all still checking:

| file | `J`s | how |
|---|---|---|
| `crates/elab/src/std/Nat/Arith.sw` | 6 | `leCongLeft`, `leCongRight`, `ltCongLeft`, `ltCongRight` are `rewrite p at h`; `nonzeroOfPos` and `posOfDouble` as §1.1 |
| `crates/elab/src/std/Nat/Divides.sw` | 1 | `rewrite <- Nat.modSmall n (Succ d) h2, e at h1` (two rules for the old `Eq.trans`) |
| `crates/elab/src/std/List/Sort.sw` | 5 | `at` on the fact (`t`, `f`, a lemma call); the one at `firstFromAtLeast`'s `t` branch is left, as it changes one `s` of `s <= s` |
| `crates/elab/src/std/Nat/Digits.sw` | 6 | the `digitsFuel*` lemmas: goal `rewrite … in` (the facts' inferred types don't show the rewritten list) |
| `crates/elab/src/std/List/Toolkit.sw` | 1 | `nonSepCons`: `rewrite h in hc` |
| `aoc/src/Aoc/Day02/Proofs/Repeated.sw` | 4 | §1.2 and §1.3 (`rewrite <- e at hx1` inline, under `Eq.sym`), and `twiceBlockLength` |
| `aoc/src/Aoc/Day02/Proofs/Part2.sw` | 6 | §1.1 and §1.3, `rewrite e at rest`, `rewrite <- Nat.mulComm n t, <- eK at Nat.dividesMul n t`, and `smallestIsPeriod` as a goal rewrite |
| `aoc/src/Aoc/Day03/Proofs/Best.sw` | 1 | `pickSub` matches like `pickGe` (§1.4); `pickSubStep` is gone |

Left alone, as §6 says: the `J`s that change one occurrence (`Repeated.sw` `twiceAbove`,
`Part2.sw` `repAbove`), those that build an equation from `rfl`, and the ones in `core.sw`
(the definitions of `Eq.sym` and friends, and the decidable-equality lemmas).

Corrected: `docs/aoc-2025.md`'s day 3 friction note, and `calc-rewrite.md` §6.5 and Stage 3
(the "no goal" item is dropped, D465).

## Sources

- [L1] Lean 4 reference, tactic reference (`rewrite`, `rw`, `simp`, `subst`):
  <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- [L2] Lean 4 source, `Lean/Parser/Term.lean` (`subst`, the `▸` docstring):
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean>
- [R1] Rocq reference manual, "Reasoning with equalities" (`rewrite … in`, `replace`, `subst`):
  <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html>; source
  <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/writing-proofs/equality.rst>
- [A1] Agda manual, "With-Abstraction" (generalisation, `rewrite`):
  <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [A2] Agda standard library, `Relation.Binary.PropositionalEquality.Core` (`subst`):
  <https://agda.github.io/agda-stdlib/master/Relation.Binary.PropositionalEquality.Core.html>
- [I1] Idris 2 documentation, "Proving Propositional Equality" (`replace`, `rewrite … in`):
  <https://idris2.readthedocs.io/en/latest/proofs/propositional.html>
- Stitchwort: `docs/syntax.md` ("`rewrite`", generalised `match`); `docs/proposals/calc-rewrite.md`
  §4, §6.4, §6.5, Stage 3, "As built"; `crates/elab/src/rewrite.rs`; `docs/aoc-2025.md` days 2
  and 3.
