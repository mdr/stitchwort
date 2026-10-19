# Proposal: treating two proofs of the same fact as equal (proof irrelevance)

**Status:** Draft 3, 19 October 2026. Design only: nothing is built. Drafts 1
and 2 each had an independent review; the responses are in
[Appendix A](#appendix-a-response-to-the-draft-1-review) and
[Appendix B](#appendix-b-response-to-the-draft-2-review). The draft 2 review's
verdict was "adopt D1′ with changes"; draft 3 makes them. **Stage 1 is ready
to implement once Matt answers §10 question 1.** No third review is planned
(§11 says why).

This note can be read without knowing type theory. §1 explains the words it
needs, with Stitchwort examples. Claims about Stitchwort were checked against
the source at commit `80c87a8` (draft 1), `69dd68a` (draft 2) and `bc89481`
(draft 3). `crates/core/src` and `crates/elab/src` are unchanged across the
three apart from `pretty.rs` and the prelude, which lost four lines after
line 231 (prelude line numbers below are as of `bc89481`); other line numbers
hold for all three. Programs marked **[run]** were run with a release build
of the CLI on 19 October 2026 (draft 3's at `bc89481`, files kept outside the
repository). New Stitchwort code in draft 3 uses the new house style
(`(x: Nat)`); older blocks are left as they were. Labels:

- **[checked: S]**: read in source S (listed in [Sources](#sources)), or in
  the Stitchwort source at the `file:line` given;
- **[run]**: a Stitchwort program run as described;
- **[inferred]**: my reasoning from checked facts, not stated in a source;
- **[unverified]**: believed, but not confirmed.

## Changes since draft 2

1. **Reworded what D1′ implies** (§0, §1, §5.1, §5.7, §6): not "its rules
   imply full irrelevance", but "D1′ is enough to *derive* propositional
   proof irrelevance and a computing K, although its comparison sees
   irrelevance only at marked positions". And "it never says two different
   things are equal" becomes "it never equates two values that differ in the
   proof-irrelevant model" (it does equate `MkBox p` and `MkBox q`).
2. **Softened "rejections only"** to: assuming §5.6's model argument, the
   subject-reduction gap can make elaboration or checking fail, or run into
   the budget, but doesn't by itself let a false term through (§0, §1, §5.7,
   §6).
3. **Normalisation kept explicitly open** (§4.5, §5.7, §6): "evaluator
   unchanged; no non-normalising term known; normalisation unproved", in
   place of "termination as today". The Abel–Coquand loop is now checked
   against the paper's reduction rule, and the reason hand-written K doesn't
   rebuild it is stated (§5.2, §5.7; still an inference, not a proof).
4. **New must-reject test 14: `Loop.expose`/`bad`**, the reviewer's direct
   test that a computing `Prop.irrel` doesn't turn into fake structural
   descent. Run today: `E-TERMINATION` **[run]** (§5.7, §8).
5. **§7.4 split into `conv` and `unify`.** The sentence "a pair visited in a
   comparison that fails doesn't matter" was false for `unify`, which keeps
   the solutions it made before failing. The elaborator already treats the
   unifier as non-atomic and runs every alternative inside a transaction
   (`undo.rs`); D1′'s one new kind of solution (a whole proof metavariable)
   goes through the same trail, so the existing rollback covers it. Stated as
   a stage 1 requirement, with tests 11b and 16 (§7.4, §7.5, §8). The audit
   tables now list every `unify` caller (draft 2 missed eleven, all safe).
6. **Mask only the definition's own arguments** (§7.2, §7.3): in a `Def`
   spine, masks apply to the leading `App` entries up to the telescope's
   length, never to anything after a `J` entry. Test 15 pins it **[run]**.
7. **`Prop.irrel` is no longer recommended for the prelude** (§7.9, §9,
   §10 question 2): it adds no power, but makes the surprising computation of
   §5.7 one call away. Deferred until a program needs it, and documented as
   computing if added.
8. **Lean citation found** (§4.1, Sources L6): the Lean reference states that
   K and its computation rule follow from definitional proof irrelevance.
9. Prelude line numbers updated; §10 cut to what's still open; §11 and §12
   revised; new Appendix B.

## Changes in draft 2 (since draft 1)

1. **Dropped the special `rfl` rule** (draft 1 §7.4: "`rfl : p = q` checks for
   any two proofs"). It made the checker accept an equation that its own
   comparison didn't believe, which is two notions of "equal" in one
   checker. The recommendation is now **D1′: proof-position masks only**
   (§6, §7). `rfl` is again checked by comparison alone.
2. **Corrected a claim the reviewer's fix relied on.** Dropping the `rfl` rule
   does *not* remove the reviewer's computational-K / subject-reduction
   example: masks alone let `rfl` prove `MkBox p = MkBox q`, and transporting
   along that and taking the box apart rebuilds the same example. New §5.7
   explains it, with a program that checks today **[run]**. The conclusion is
   that D1′ is a sound but *incomplete* approximation of full proof
   irrelevance, like Lean's checker, and that its failures are always
   rejections (§5.7, §7.9).
3. **Added the "same type" (homogeneous input) obligation** for comparing
   constructor values, which don't record their data type's parameters, and
   **audited every comparison call site** (§7.4, new). The invariant holds
   today; the design keeps comparison untyped and writes the invariant down,
   rather than adding parameters to constructor values or types to `conv`.
4. **Narrowed the unifier rule** (§7.5): only a metavariable that *is* the
   whole proof argument may be solved; never look inside a skipped proof.
   Also corrected the account of Agda #8699 (its fix was in the termination
   checker, not the unifier).
5. **Reworded the transitivity claim** (§6) to apply only to the masked
   relation on well-typed values of one type.
6. **Fixed two paired tests that depended on the dropped rule**, and added
   the reviewer's tests (a `Prop` *parameter* stays relevant; a metavariable
   seen only inside a proof stays unsolved) plus tests for §5.7 and §7.4
   (§8).
7. Labelled Agda's decidability/normalisation entries as properties of the
   published calculus, not of every Agda release (§4.3, §4.5).
8. Checked that both motivating cases are still fixed by masks alone,
   including every arm of `examples/accept/char-pattern-proofs.sw` (§2.4).
9. New words in §1: *Axiom K*, *subject reduction*, *homogeneous comparison*.
   Questions for Matt (§10) and the reviewer (§11) revised.

## Contents

0. [Summary](#0-summary)
1. [The words, in plain terms](#1-the-words-in-plain-terms)
2. [The problem: three programs](#2-the-problem-three-programs)
3. [How Stitchwort handles proofs today](#3-how-stitchwort-handles-proofs-today)
4. [How other systems do it](#4-how-other-systems-do-it)
5. [What can go wrong: the known pitfalls](#5-what-can-go-wrong-the-known-pitfalls)
6. [Options](#6-options)
7. [The recommended design in detail](#7-the-recommended-design-in-detail)
8. [Tests](#8-tests)
9. [Stages](#9-stages)
10. [Questions for Matt](#10-questions-for-matt)
11. [Questions for the reviewer](#11-questions-for-the-reviewer)
12. [What I couldn't verify](#12-what-i-couldnt-verify)
13. [Sources](#sources)
- [Appendix A: response to the draft 1 review](#appendix-a-response-to-the-draft-1-review)
- [Appendix B: response to the draft 2 review](#appendix-b-response-to-the-draft-2-review)

## 0. Summary

Today the kernel compares two proofs the same way it compares data: they're
equal only if they compute to the same thing. So `x % 100` with a
hand-written proof that `100 != 0` and `x % 100` with `auto`'s proof have
different types that print the same, and a hand-built character
`MkChar 97 p` isn't the literal `'a'` (whose proof is `rfl`). Stitchwort has
worked around both: `[auto]` arguments in the `Int` lemmas, and an
elaborator pass (`canonical`, commit `55c48eb`) for character patterns.

**Recommendation: option D1′, "skip proof positions when comparing".** When
the kernel compares two values with the same head and reaches an argument or
constructor field that the declaration says is a proof (its declared type is
in `Prop`), it skips it. That is the whole rule. Nothing new is *computed*:
the evaluator is untouched, `J` still only computes on `rfl`, a `case` on a
proof still needs a constructor, and `rfl` is still checked only by
comparison. It uses the "relevance marks" idea from Rocq's `SProp` (read the
binder's declared sort, don't infer types during comparison). It fixes all
three programs in §2, needs no change to JS extraction, erasure or hashing,
and comparison only does less work than before.

What it is, honestly: a *sound but incomplete* version of the proof
irrelevance Lean has. D1′ is enough to *derive* that every two proofs of a
proposition are equal (as a theorem) and to write a computing K by hand
(§5.7), although its comparison recognises irrelevance only at proof
positions of definitions, constructors and data types, not for two bare
proof variables `p` and `q`. Because of the gap, a well-typed term can
compute to one the checker would reject at the same type (§5.7). Assuming
the model argument of §5.6, that can make elaboration or checking fail (or
run into the budget), but doesn't by itself let a false term through; Lean
has a gap of the same kind for other reasons (§5.1).

Three prerequisites: comparison is only ever asked about two values of the
same type (audited call by call, §7.4: holds today); the unifier never looks
inside a skipped proof (§7.5: stage 1 builds it); and any elaborator code
that tries another way after a failed unification first undoes the failed
attempt's solutions (§7.4: holds today through `undo.rs`, and stage 1's new
solutions use the same mechanism).

Normalisation is not proved, today or with D1′. The evaluator is unchanged
and no non-terminating term is known, but D1′ accepts more programs, so it
stays an open question (§5.7).

It deliberately doesn't add Lean's "K-like" rule (`J` computes along *any*
proof of `a = a`), because with an impredicative `Prop` that rule is known to
give terms whose checking never finishes (Abel and Coquand 2020, §5.2). And
it doesn't try to be complete: Lean's full rule is known to make type
checking undecidable (Carneiro 2019, §5.1), and Stitchwort's `Prop` admits
the same counterexample (§5.1, a program accepted today).

Stage 1 is a small kernel change plus the matching change in the
elaborator's unifier and the reference evaluator; stage 2 removes the
elaborator workarounds. **The design is ready for stage 1** once Matt agrees
to D1′ (§10 question 1); the other questions only affect stage 2 or later.

## 1. The words, in plain terms

**Proposition, proof, `Prop`.** In Stitchwort a statement such as
`xs ++ [] = xs` or `d != 0` is a *type*, and a value of that type is a
*proof* of it. Types of statements live in the universe `Prop`; ordinary data
types (`Nat`, `List Nat`, `Char`) live in `Type`. A proof is erased when the
program runs, because nothing at runtime may depend on it (DESIGN §6).

```
theorem two : 1 + 1 = 2 := rfl          -- `1 + 1 = 2 : Prop`, `rfl` is a proof
def Not (p : Prop) : Prop := p -> Void   -- a proof of `Not p` is a function
```

**Definitional versus propositional equality.** There are two kinds of
"equal":

- *Definitional* (also "judgemental", or "conversion"): the checker can see
  it by itself, by computing. `2 + 2` and `4` are definitionally equal. This
  is what lets `rfl` prove `2 + 2 = 4`, and what decides whether an argument
  of type `Vec Nat (2 + 2)` fits a parameter of type `Vec Nat 4`.
- *Propositional*: there's a proof of `a = b`, which you must use explicitly
  (with `J`, `Eq.cong`, `rewrite`) to move between `a` and `b`. `n + 0 = n`
  for a variable `n` is propositional in Stitchwort: it needs an induction
  proof (`+` recurses on its first argument).

**Proof irrelevance.** "Any two proofs of the same proposition are equal."
*Propositional* proof irrelevance is a theorem or axiom you can use
explicitly: `(p q : P) -> p = q`. Stitchwort proves it for a few
propositions, e.g. `Bool.uniqueEq : (p q : x = y) -> p = q` for `Bool`
(prelude, line 300). *Definitional* proof irrelevance means the checker
itself treats `p` and `q` as the same, so nothing has to be transported.
That's what this note is about.

**Elimination, large elimination.** *Eliminating* a value means taking it
apart: a `match`, or `J` for an equation. *Large elimination* of a proof
means taking a proof apart to produce data or a type, not just another
proof. It's dangerous because runtime results could depend on which proof
was given, and proofs are erased. Stitchwort allows it only for propositions
with at most one constructor whose fields are all proofs (Lean's
"subsingleton elimination", `E-PROP-ELIM`, DESIGN §6):

```
type And (p : Prop) (q : Prop) : Prop = | Both (left : p) (right : q)   -- prelude

def pick [p q : Prop] (h : And p q) : Nat :=     -- allowed: one constructor,
  match h with | Both a b => 5                   -- only proof fields

def which [p q : Prop] (h : Or p q) : Nat :=     -- refused (E-PROP-ELIM): the
  match h with | Inl a => 0 | Inr b => 1         -- answer depends on the proof
```

Equality has one constructor and no fields, so `J` may produce data
("transport": turning a `Vec Nat (n + 0)` into a `Vec Nat n` along a proof of
`n + 0 = n`).

**Decidability of type checking, and why it matters.** Type checking is
*decidable* if there's an algorithm that always finishes and always gives the
right yes/no answer. If definitional equality is undecidable, then either
the checker sometimes runs forever, or it gives up and says "not equal" for
some things the rules say are equal. The second is what Lean does: its
checker is a sound but incomplete approximation of its own rules. For
Stitchwort this matters because the checker computes (so DESIGN §2's
principle 1, no divergence, has to hold for what it computes) and for
predictability: a user should be able to tell whether `rfl` will work.
Stitchwort's checker already has a budget, so "runs forever" would show as
`E-RESOURCE` (inconclusive), never as a wrong answer; but a rule that makes
the budget the *normal* way to fail is a bad rule.

**Sound versus complete.** A checker is *sound* if everything it accepts is
really true (no proof of `Void`). It is *complete* for a rule if it accepts
everything the rule allows. D1′ is sound and deliberately incomplete: it
never equates two values that are different in the proof-irrelevant model
(§5.6; it does equate syntactically different values such as `MkBox p` and
`MkBox q`, which that model can't tell apart), but sometimes says "not
equal" for two proofs the model considers equal.

**Normalisation.** Every term computes to a final form (a *normal form*) in
finitely many steps. Stitchwort's checker compares types by computing both
to normal form and comparing the results (DESIGN §6 "Running vs comparing"),
so if some terms have no normal form, comparison can loop.

**Transitivity.** If `a ≡ b` and `b ≡ c` then `a ≡ c`. A checker whose
equality isn't transitive surprises users: two steps that each check can
fail when combined.

**Subject reduction.** "Computing doesn't change a term's type": if the
checker accepts `t : T` and `t` computes to `t'`, the checker also accepts
`t' : T`. Example: it accepts `(\x => x) 3 : Nat`, and also `3 : Nat`. When
it fails, replacing an expression by its value (inlining, or the elaborator
writing in a computed solution) can turn an accepted program into a
rejected one. In a checker that is sound, failure of subject reduction shows
up as rejections (or an elaborator error, or running out of budget), not as
false proofs **[inferred]**.

**Homogeneous comparison.** Comparing two values *of the same type*. The
kernel's comparison (`conv`) is untyped: it's handed two values and never
told their types. D1′ skips a constructor's proof field by looking only at
the constructor, which is safe only if both values have the same type:
`MkBox p : Box P` and `MkBox q : Box Q` have the same constructor, but `p`
and `q` prove different things, and skipping them would be wrong. So
D1′ requires every caller to compare values of one type (§7.4).

**Erasure versus irrelevance.** These are different questions:

| | Erasure | Irrelevance |
|---|---|---|
| Question | Does it exist when the program *runs*? | Does the *checker* look at it when comparing? |
| Stitchwort today | Proofs and types are erased (DESIGN §6) | Nothing is irrelevant |
| Idris 2 | Quantity `0` arguments are erased, but still compared by the checker **[checked: I1, for erasure; unverified for comparison]** | |
| Agda | `@0` erases; `.x` makes an argument irrelevant **[checked: A2]** | |

Types are erased in Stitchwort but must stay *relevant*: `Vec Nat 3` and
`Vec Bool 3` differ only in a type argument. So whatever is built here must
key on "is a proof", never on "is erased". Note that a *proposition* is not
a proof either: in `type R (p : Prop) : Type`, the parameter `p` has type
`Prop`, and `Prop : Type 0`, so `p` is relevant and `R Unit` and `R Void`
must stay different (test 9, §8).

**Axiom K, UIP.** *UIP* ("uniqueness of identity proofs") is propositional
proof irrelevance for equations: any two proofs of `a = b` are equal. *Axiom
K* says the same thing as an eliminator: to prove something about every
`h : a = a`, it's enough to prove it for `rfl`. Its *computation rule* says
that using K on any `h` computes as if `h` were `rfl`. Example: with K
computing, transporting `x : F rfl` to `F h` for a variable `h : a = a`
gives back `x`. Both K and UIP are incompatible with homotopy type theory's
univalence, which is why Agda and Rocq care about avoiding them. Stitchwort
has no univalence and no plans for it, and definitional proof irrelevance for
`Prop` implies UIP, so UIP itself is no cost here **[inferred]**. What *is*
a cost is K's computation rule as a built-in reduction, because of §5.2.

## 2. The problem: three programs

All three were run at `80c87a8` **[run]**.

**2.1 The divisor proof** (TODO.md, Int stage 6, docs/proposals/integers.md
§"As built (stage 6)").

```
theorem sameMod (x : Int) : Int.modNat x 100 [ok := Nat.succNotZero 99] = Int.modNat x 100 := rfl
```
```
[E-REFL] `Int.modNat x 100` and `Int.modNat x 100` aren't equal
```

`Int.modNat x 100 ok` is stuck (it needs to know `x`), so the proof `ok` is
part of its normal form, and the two `ok`s are different terms
(`Nat.succNotZero 99` versus whatever `auto`'s decision procedure produced).
Int stage 6 worked around it by making every lemma take the proof as
`[auto ok : d != 0]`, so the lemma and the user's statement get the same
proof from the same search.

**2.2 A hand-built character.**

```
theorem handBuilt (p : Char.isScalar 97 = True) : MkChar 97 p = 'a' := rfl
```
```
[E-REFL] `'a'` and `'a'` aren't equal
```

`'a'` is `MkChar 97 rfl` (`crates/core/src/chars.rs`, header comment), so
the two differ only in the proof field `valid`. The printer hides proofs,
hence the baffling message.

**2.3 Character patterns** (fixed in the elaborator). A pattern `'a'`
compiles to `MkChar 97 _`, so in its arm the matched character was
`MkChar 97 p` for a fresh proof `p`, not the literal. Commit `55c48eb`
fixed `| 'a', h => rfl` with an elaborator pass, `canonical`
(`crates/elab/src/lib.rs:2370`), which checks the arm with `rfl` in place of
`p` and transports back along `Bool.uniqueEq`. That commit added about 190
lines to the elaborator, and it only works because `Bool`'s equality proofs
are provably unique. Examples: `examples/accept/char-pattern-proofs.sw`.

### 2.4 Are these fixed by masks alone? (new in draft 2)

Yes, by this reasoning **[inferred from the code cited]**:

- **2.1.** A stuck definition stays *folded*: its value is
  `Neutral(Def(Int.modNat), [x, 100, ok])`, the original spine
  (`value.rs:920-924`, `stuck_tree`; `value.rs:5-7`). `Int.modNat`'s type is
  `Int -> (d : Nat) -> [auto ok : d != 0] -> Nat` (prelude:1640), and
  `d != 0` is a function into `Void : Prop` (prelude:16, 22), so it's in
  `Prop` and position 2 is a proof position. Comparing the two sides reaches
  the `Neutral`/`Neutral` arm with the same `Def` head (`value.rs:1291`), and
  the mask skips position 2. The `E-REFL` may come from the elaborator first
  (`elab/src/check.rs:1229` unifies the two sides of an `rfl` goal), which is
  why §7.5 gives the unifier the same masks.
- **2.2.** Both sides are `Ctor(Char, 0, [97, …])` (a single character is a
  constructor value, not a compact `Chars` range); field 1, `valid`, has
  sort `Prop`, so it's skipped (`value.rs:1275`).
- **2.3.** Each arm of `examples/accept/char-pattern-proofs.sw`, with the
  matched character `MkChar n p` and no `canonical`:
  `firstIsA`, `isItself`, `hypothesisRefined` and `pairOfChars` need
  `MkChar n p ≡ MkChar n rfl` (directly, or inside `Pair`/`Or`): the mask.
  `nextOfA`, `bitIsBit` and `bitRoundTrip` compute `next`, `isBit`,
  `bitValue` and `bitChar` on `MkChar n p`. Those functions match
  `MkChar n _` and never look at the proof field, so they compute today; the
  remaining comparisons (`bitChar (bitValue c) = c`) are again the mask.
  `firstIsAComputes` and `nextOfAComputes` get simpler: without `canonical`
  there's no `J` in the arm to compute away.

  **Does the char case need anything beyond masks?** `canonical` does one
  more thing: by putting `rfl` in for `p`, it lets a `J` or a `match` *on
  the proof `p`* compute inside the arm. Masks don't (that would be new
  computation). No program in the repository needs it: the only prelude
  functions that take `MkChar n v` apart either ignore `v` (`Char.code`,
  prelude:322) or are theorems (`Char.mkExt`, prelude:327-334)
  **[checked: grep of the prelude, `aoc/`, `examples/`]**. So stage 2 can
  remove `canonical`, gated on the example file and the AoC solutions still
  checking. If a later program does compute on a char's proof, it can
  transport along `Bool.uniqueEq` by hand, as `canonical` does.

## 3. How Stitchwort handles proofs today

The relevant parts of the kernel (`crates/core/src`), checked by reading:

- **Comparison is untyped.** `value::conv` (`value.rs:1164`) compares two
  values by their shapes, without knowing their types: constructors by
  index and fields (`value.rs:1275`), data types by parameters (`:1268`),
  stuck computations (`Neutral`) by head and arguments (`:1291`, with
  `spine_pairs` at `:1331`). A value doesn't record its type: a lambda has
  no domain, a constructor value no parameters (`value.rs:20-40`:
  `Ctor(DataId, usize, Values)`).
- **Universes are exact.** `Prop : Type 0`, with no cumulativity: sorts
  compare with `==` (`value.rs`, `(Value::Sort(s), Value::Sort(t)) => s ==
  t`), and `check` uses `conv` with no subsumption. A function type whose
  result is a proposition is a proposition (`Sort::pi`, `term.rs:45`): this
  is *impredicativity*. There's no universe polymorphism (DESIGN §6). So
  every type has exactly one sort, and a variable `x : a` with `a : Type`
  can never be a proof **[inferred from the code]**.
- **The kernel already records which fields are proofs.** Each constructor
  stores `field_sorts` (`globals.rs:117`), and separately `field_erased`
  (proofs *and* types, `globals.rs:119`). Only the former is right for
  irrelevance.
- **`J` computes only on `rfl`**: `J P d rfl ⟶ d`, stuck on anything else
  (docs/core.md, "Equality").
- **A `case` on a proof computes only on a constructor.** Matching on an
  erased placeholder takes the single branch only *while running*
  (`value.rs:911`, `erase.rs` rules 4 and 5), never in the checker.
- **Effects aren't in the kernel**: an effectful function's type is a
  function into the prelude's `Effect.Comp` (docs/core.md, line 14), which is
  data. So "effectful arrows are never `Prop`" (DESIGN §6) holds with
  nothing extra.
- **Data types have parameters but no indices**, and a data type may only
  use itself with its own parameters in its fields (`E-POSITIVITY` "used with
  different parameters" **[run]**). So Lean's `Acc` can't be written as is.
- **Termination checking never calls `conv` or `unify`**
  (`grep` of `sct.rs`, `termination.rs`): descent is read from the terms.
- **The elaborator's unifier** (`crates/elab/src/unify.rs:23`) mirrors
  `conv`'s structure, and solves metavariables.
- **A reference evaluator** (`reference.rs`, test only) has its own `conv`
  (`reference.rs:373`), kept in step for differential tests.

## 4. How other systems do it

### 4.1 Lean 4: all of `Prop`, checked by type

- Definitional equality has proof irrelevance for every `Prop` ("any two
  proofs of the same proposition are definitionally equal"), and "is
  reflexive and symmetric, but not transitive" **[checked: L3, re-read 19
  October 2026]**.
- The kernel's check (`is_def_eq_proof_irrel`): infer the type of `t`; if it
  is a proposition, infer the type of `s` and compare the two types
  **[checked: L1, type_checker.cpp:895-903]**. So Lean's comparison is
  typed at exactly this point: it never equates proofs of different
  propositions, which is the issue §7.4 handles differently. It runs after
  cheap checks and *before* unfolding definitions (`:1159`, before
  `lazy_delta_reduction`), so proofs are never unfolded to compare them
  **[checked: L1]**.
- **K-like reduction.** For an inductive proposition with one constructor
  and no fields beyond its parameters (equality is the main example), the
  recursor computes even when the proof isn't a constructor:
  `to_cnstr_when_K` infers the major premise's type and, if its indices match
  the constructor's, replaces the proof by the constructor (for `e : a = a`,
  by `Eq.refl a`) **[checked: L2, inductive.h:27-50; L5]**. So in Lean,
  transport along any proof of `a = a` computes. With definitional proof
  irrelevance this is not really separate machinery: any `e : a = a` *is*
  definitionally `Eq.refl a`, so K's computation rule is a consequence; the
  rule just makes the checker see it. The Lean reference says so directly:
  equality proofs are unique "because of definitional proof irrelevance", and
  Streicher's axiom K "is also a consequence of definitional proof
  irrelevance, as is its computation rule" **[checked: L6, §20.4.1
  "Uniqueness of Equality Proofs", 19 October 2026]**.
- **Structure eta in the recursor**, which turns a stuck `p` into
  `mk p.1 … p.n` so a match can compute, is explicitly *not* done for
  propositions: `if (is_prop(e_type)) return e;` **[checked: L2,
  inductive.h:61-73]**. So in Lean a match on a stuck proof of `And p q` into
  data stays stuck, though by proof irrelevance it "should" compute.
- Subsingleton elimination as in Stitchwort, plus recursive propositions
  such as `Acc` (well-founded recursion) **[checked: L4 §2.6]**.
- Theory: consistent relative to ZFC plus inaccessible cardinals, by a
  set-theoretic model in which every proposition has at most one element
  **[checked: L4, abstract]**. But "type checking is undecidable, and the
  type checking as implemented by the Lean theorem prover is a decidable
  non-transitive underapproximation of the typing judgment"
  **[checked: L4, abstract]** (§5.1 below).

### 4.2 Rocq: `SProp`, a separate sort

- `SProp` is a separate sort of "strict propositions"; "all elements are
  convertible". It's on by default; its status is "experimental"
  **[checked: R1]**. Rocq's ordinary `Prop` stays proof-*relevant* for
  conversion.
- **Restriction:** inductive types in `SProp` "can only be eliminated to
  construct proofs of other strict propositions", except empty types
  **[checked: R1]**. So no transport along an `SProp` equality, no `Acc`
  recursion.
- An opt-in flag, *Definitional UIP*, allows eliminating `SProp` equality
  into anything, through a special reduction that doesn't look at the proof;
  combined with impredicative `Prop` it "breaks termination of reduction"
  **[checked: R1]**.
- **No cumulativity** from `SProp` into `Type`, "to keep conversion
  tractable" **[checked: R1; G §6.1]**.
- **Relevance marks.** Rocq's conversion is untyped, like Stitchwort's.
  Rather than infer types during conversion, every binder (lambda, product,
  context variable, constant) carries a mark saying whether its type is in
  `SProp`, and conversion inserts "a check for irrelevance before the
  reduction step" **[checked: G §4.5, §6.1.1]**. The marks are computed by
  the kernel; marks from outside it may be wrong, which only makes
  conversion incomplete **[checked: R1; G §6.1.1]**. Relevance of an
  application is the relevance of its head; this is correct because typing
  is unique, so relevance is stable under substitution **[checked: G §4.5,
  Prop. 4.4]**. This is the trick option D1′ borrows, for definition,
  constructor and data-type binders only (stage 3, §9, would add context
  variables).
- Theory: the paper proves consistency and decidability of type checking
  for its calculus, and shows why the old "singleton elimination" criterion
  is wrong in the presence of definitional irrelevance: `Acc` makes
  conversion undecidable, and singleton types would collapse propositional
  into definitional equality **[checked: G abstract, §2.2, §2.3]**.

### 4.3 Agda: `Prop` (opt-in) and irrelevant arguments

- `Prop` is "an experimental extension of Agda guarded by option `--prop`";
  it is predicative (`Prop₀`, `Prop₁`, …); a function from a `Prop` data
  type into `Set` may only use the absurd pattern `()`; equality in `Prop`
  can't be eliminated, so it's only useful for refuting impossible
  equations **[checked: A1]**.
- Agda's conversion is type-directed, so adding "any two elements of a type
  in `Prop` are equal" was straightforward; impredicativity was avoided
  because Agda's termination checker assumes predicativity **[checked: G
  §6.5]**.
- Older, separate: *irrelevant arguments* `.x`: "only be typechecked but
  never evaluated or compared for equality"; an irrelevant variable may only
  be used in irrelevant positions; you can't pattern match on one, except
  with `()` **[checked: A2]**. Irrelevance here is attached to the *binder*,
  not inferred from a type, which is close to option D1′.
- Known soundness bugs *in the implementation*: irrelevant record fields
  gave a proof of `⊥` in Agda 2.5.3 (issue #2170), by matching on an
  irrelevant field **[checked: G §1, appendix B]**; and #8699, a `--safe`
  proof of `⊥` through `Prop` and irrelevant arguments, fixed 29 August 2026
  (§5.4) **[checked: A3]**. So the "decidable / normalising" entries for
  Agda below describe the published calculus, not every Agda release.

### 4.4 Idris 2

Quantity `0` means "erased at run time", and such variables can still be
"reasoned about in types" **[checked: I1]**. Whether the checker skips them
when comparing: not stated there **[unverified]**; I believe it doesn't,
i.e. Idris 2 has erasure without irrelevance.

### 4.5 Summary

| | Which proofs are equal | Large elimination | Transport on non-`rfl` proofs | Checking decidable | Normalising |
|---|---|---|---|---|---|
| Lean 4 | All of `Prop` | Subsingletons, incl. `Acc` | Yes (K-like rule) | No (in theory); kernel is a decidable approximation | No (§5.2) |
| Rocq `SProp` | All of `SProp` | Only empty types | No (unless Definitional UIP) | Yes (proved) | Yes, without Definitional UIP |
| Agda `--prop` (calculus of G) | All of `Prop` | Only `()` | No | Yes **[inferred from G]** | Yes **[inferred]** |
| Agda `.x` | Arguments marked `.` | No matching | n/a | Yes | Yes |
| Stitchwort today | None | Subsingletons (Lean's rule) | No | Budgeted | Assumed |
| **Option D1′** | **Derivable as a theorem: all of `Prop`. Seen by the checker: proof positions of definitions, constructors, data types** | **Unchanged** | **No rule; a user can write K by hand (§5.7)** | **Budgeted, as today** | **Evaluator unchanged; no non-normalising term known; unproved (§5.7)** |

## 5. What can go wrong: the known pitfalls

### 5.1 Undecidability through recursive propositions (Carneiro)

Lean's `Acc` (accessibility) has one constructor whose field is a proof, so
it may be eliminated into data. Any `a : Acc x` is, by proof irrelevance,
equal to `intro x (inv a)`, where `inv` takes `a` apart; so a function
defined by recursion on `Acc` can be unfolded one more step at any time.
Carneiro uses a decidable predicate `P` (e.g. "machine M runs at least n
steps") to build `f 0 a` that is definitionally equal to `()` exactly when
`∀n. P n`: so definitional equality is undecidable **[checked: L4 §3.1]**.
Lean's checker never makes that "creative" step, so it fails to see some
equalities its rules give, and is not transitive: `f 0 a ⇔ f 0 (intro 0
(inv a))` and that `⇔ f 1 (…)`, but `f 0 a ⇎ f 1 (…)` **[checked: L4
§3.1.1]**. That in turn breaks subject reduction for the algorithmic typing
**[checked: L4 §3.1.2; G appendix A shows a Lean 3 instance]**.

**Stitchwort has the same shape.** `Acc` itself is refused (non-uniform
parameter), but this is accepted today **[run]**:

```
type Loop : Prop = | MkLoop (next : Loop)       -- empty, but allowed
def Loop.inv : Loop -> Loop | MkLoop n => n
def steps : Loop -> Nat -> Bool                  -- large elimination of a proof
  | MkLoop n, k => if k == 3 then True else steps n (k + 1)
```

Under a *full* proof-irrelevance rule, `steps l 0 ≡ steps (MkLoop
(Loop.inv l)) 0 ≡ steps (Loop.inv l) 1 ≡ …`, and Carneiro's argument goes
through: any rule that says "all proofs of `Loop` are equal, everywhere"
makes Stitchwort's definitional equality undecidable **[inferred]**. The
design must therefore not *promise* full irrelevance; it must specify the
decidable part it implements. (D1′ is enough to *derive* propositional
proof irrelevance, §5.7; what its checker promises is only the masked
comparison of §7.1.)

### 5.2 Non-termination through impredicativity and K-like transport (Abel and Coquand)

With an impredicative `Prop` and a transport `cast : A = B -> A -> B` that
computes whenever `A` and `B` are definitionally equal, without looking at
the proof, normalisation fails: under a hypothesis `h : ∀ A B : Prop, A = B`
there's a term `Ω h` that reduces to itself; with Lean's `propext` the term
is closed and `#reduce` loops in Lean 3.4.2 **[checked: AC]**. It refutes
Werner's normalisation conjecture for proof-irrelevant type theory
**[checked: AC]**. Agda's and Rocq's strict `Prop` avoid it because their
equality can't be eliminated into types **[checked: AC, last section]**.

Stitchwort has every ingredient except the transport rule: an impredicative
`Prop`, `Eq` at type `Prop`, and `J` into `Prop`. The term is accepted and
checks quickly today, because `J` is stuck on `h Top a` **[run]**:

```
def Bot : Prop := (a : Prop) -> a
def Top : Prop := Bot -> Bot
def delta : Top := \z => z Top z
def omega : ((a : Prop) -> (b : Prop) -> a = b) -> Bot :=
  \h a => J (\y e => y) delta (h Top a)
def bigOmega : ((a : Prop) -> (b : Prop) -> a = b) -> Bot := \h => delta (omega h)
theorem omegaUnfolds (h : (a : Prop) -> (b : Prop) -> a = b) :
    bigOmega h = omega h Top (omega h) := rfl
```

With Lean's K-like rule, `J … (h Top Top)` would compute, and the
comparison would loop under the binder (ending in `E-RESOURCE`)
**[inferred]**. **So: no K-like rule.** This is a must-keep test (§8).

The narrow claim is: ordinary `J`, which computes only on a literal `rfl`,
doesn't perform the reduction this counterexample uses; the paper stresses
that the bad cast computes *without inspecting the proof* **[checked: AC]**.
Draft 1 overstated what follows from it. Not changing `J` is not by itself
enough: anything that lets users *manufacture* a literal `rfl` between
different proofs gives them K-like computation by hand. Draft 1's `rfl`
rule did that, and so, less directly, do masks (§5.7).

The exact step that loops (draft 3, re-read): the paper's rule is
`cast A A e x ⟶ x`, which "does not inspect the equality proof e … but only
checks whether the endpoints are (definitionally) equal", and the loop is
`Ω h = δ (ω h) ⟶ cast ⊤ ⊤ (h ⊤ ⊤) δ (ω h) ⟶ δ (ω h)`, where `ω h A = cast ⊤ A
(h ⊤ A) δ` is written for a *variable* `A` and the step fires only after `A`
becomes `⊤` **[checked: AC §1]**. So what's needed is a cast that notices,
after substitution, that its endpoints have become equal, while its proof
`h ⊤ ⊤` is still a stuck hypothesis. §5.7 explains why hand-written K doesn't
supply that.

### 5.3 Singleton types and extensionality (Gilbert et al.)

If a proposition that carries data (like `{ b : A | a = b }`) could be
eliminated into data, irrelevance would turn every propositional equality
into a definitional one, which is undecidable **[checked: G §2.2]**.
Stitchwort's `E-PROP-ELIM` already refuses this (`∃` can't produce data,
DESIGN §6), and option D1′ doesn't touch it. But it's the reason the
elimination rule and the irrelevance rule must be designed together: **every
proposition that can be eliminated into data must really have at most one
proof in the model** **[inferred]**.

### 5.4 Termination through irrelevant parts (Agda #8699)

The mechanism, as the issue records it **[checked: A3, re-read 19 October
2026]**: a family `T : Sq -> Set` is indexed by a record `Sq` whose only
field is irrelevant. Matching on `T s` makes the unifier instantiate `s`
with a *dot pattern* `.(sq (suc m))` (a pattern the checker fills in
itself). The termination checker turned that dot pattern into a constructor
pattern and descended into the irrelevant field, taking `sq m` in the
recursive call as smaller than `sq (suc m)`. But nothing ever inspects that
field, so `f` reduced to itself and proved `⊥` under `--safe`; a `Prop`
variant failed the same way. In the discussion Abel suggested stopping the
unifier from refining irrelevant subterms; Cockx argued the unifier should
stay as it was, and the fix (PR #8707, 29 August 2026) was in the
termination checker: don't count descent under irrelevant or `Prop`
arguments of dot patterns.

The lesson recorded in docs/proposals/mutual-recursion.md §6.7: descent
must only use parts that really exist in the values the evaluator computes
with.

For Stitchwort with D1′: descent evidence is still read from real matches on
variables (no dot patterns, no indices, no forced patterns); the evaluator
still computes with proof terms, and only *comparison* skips them; the
termination checker never calls `conv` or `unify` (§3). So the #8699
mechanism has nothing to act on **[inferred]**. The elaborator's unifier is
narrowed anyway (§7.5), because a solution taken from inside a skipped proof
is information the kernel's comparison doesn't vouch for. §8 has tests for
both.

### 5.5 Irrelevant data (Agda #2170)

Agda's bug came from making a *data* field irrelevant and then matching on
it **[checked: G appendix B]**. D1′ only ignores proofs, never data, and
matching on proofs is still governed by `E-PROP-ELIM`. Must keep: never use
`field_erased` (which includes types) where `field_sorts == Prop` is meant.

### 5.6 What "sound" requires here

Three things **[inferred]**:

1. **A model where proofs are all equal.** Interpret each proposition as a
   set with at most one element (as in Carneiro's model of Lean). Every
   equation D1′ adds then holds in the model, so D1′ can't prove anything
   false *provided* Stitchwort's existing rules hold in such a model. They
   are a subset of Lean's (impredicative `Prop`, subsingleton elimination,
   `J`), plus things checked against their definitions (natives, compact
   text) and things justified separately (size-change termination, handler
   termination: DESIGN §13 "Known gaps"). Nothing in Stitchwort today
   distinguishes two proofs of one proposition except computation, which is
   exactly what the model forgets. (The draft 1 reviewer saw no model-breaker
   among `NumCase`, `Comp`, `Partial`, compact text or natives.)
2. **Each skip compares two proofs of the same proposition.** This needs
   both values to have the same type (§7.4). Then: for a definition or data
   type, the two values have the same head, the relevant earlier arguments
   are in the spine, and if the comparison as a whole succeeds those are
   equal, so the skipped position's declared type is the same proposition on
   both sides. For a constructor, the field types also depend on the data
   type's *parameters*, which the value doesn't carry; they are equal only
   because the two values have the same type, which is what §7.4 audits.
   "Equal" here means equal in the model: a later position's type may
   mention an earlier, skipped proof.
3. **Every type has exactly one sort** (no cumulativity, no universe
   polymorphism, §3), so "the declared type is in `Prop`" means the argument
   really is a proof whatever the instantiation. If Stitchwort ever adds
   cumulativity or universe polymorphism, this must be revisited (Rocq
   forbids `SProp` cumulativity for the same reason, §4.2).

Soundness does *not* need subject reduction or completeness (§5.7): the
checker only has to never call two things equal that differ in the model.

### 5.7 What masks are enough to derive: proof irrelevance, hand-written K, and a subject-reduction gap

Masks let `rfl` prove `MkBox p = MkBox q` for any two proofs `p q : a`
(the field is skipped). From that, propositional proof irrelevance and K's
computation follow by ordinary means. This file checks today **[run]**:

```
type Box (p : Prop) : Type =
  | MkBox (h : p)

def Box.unbox [p : Prop] : Box p -> p
  | MkBox h => h

def castViaBox (a : Prop) (p : a) (q : a) (f : a -> Type) (x : f p)
    (e : MkBox p = MkBox q) : f q :=
  J (\y e2 => f (Box.unbox y)) x e

theorem piViaBox (a : Prop) (p : a) (q : a) (e : MkBox p = MkBox q) : p = q :=
  J (\y e2 => p = Box.unbox y) rfl e
```

Today `rfl : MkBox p = MkBox q` is rejected (`E-REFL` **[run]**), so `e`
must be a hypothesis. Under D1′, `rfl` is accepted there, so:

- **Propositional proof irrelevance is a theorem**: `piViaBox a p q rfl :
  p = q`. Option A's trusted `proofIrrel` constant isn't needed; a prelude
  theorem would do.
- **K's computation rule can be written by hand.** With `a` an equation
  `t = t` and `p := rfl`, `castViaBox (t = t) rfl h f x rfl : f h`, and it
  computes to `x`, for any `h : t = t`. The kernel's `J` is unchanged: it
  computes because its proof argument is a literal `rfl`.
- **Algorithmic subject reduction fails.** `castViaBox a p q f x rfl` is
  accepted at type `f q` and computes to `x`, but the checker rejects
  `x : f q`, because `f` is a local variable (no masks) and `p`, `q` are two
  different proof variables. This is the reviewer's `castProofIndex`
  example; it doesn't need draft 1's `rfl` rule, only masks.

So D1′ is enough to derive propositional proof irrelevance and a computing
K operator, even though its comparison recognises irrelevance only at
masked positions (the draft 2 reviewer agrees the construction is right).
That is the same kind of gap as Lean's (§5.1), from a different cause:
Lean's comparison is typed and sees `p ≡ q` here, but misses Carneiro's
creative unfoldings.

**What the gap costs.**

- *Soundness*: nothing, assuming §5.6's model argument. The checker still
  only equates values equal in the model (§5.6), and the evaluator's rules
  (β, `case` on a constructor, `J` on `rfl`) all hold in the model. The reduct
  `x` of `castViaBox a p q f x rfl` may not be *algorithmically* typable at
  `f q`, but it has that type in the model, where `p` and `q` are the same
  proof and `f` can't tell them apart **[inferred; the draft 2 reviewer
  agrees]**.
- *Failures*: a term accepted at one type can compute to a term rejected at
  that type. Users meet this only if they inline such a value by hand. The
  elaborator meets it if it writes a computed normal form back into a term
  (metavariable solutions are quoted values, `unify.rs:342`, `rename`; and `let`
  values can be folded back, `lift.rs:605-620`): the kernel then rejects the
  elaborated term. That's an elaborator error, not a false acceptance, and
  needs a program that transports along a hand-made `rfl` between proofs.
  Other possible symptoms are an internal elaborator error or running into
  the budget; none of them accepts a false term.
- *Termination*: comparison does strictly less work, and evaluation has the
  same rules as today, so checking any *given* term does no more work than
  before. But the set of accepted terms grows, and Stitchwort has no
  normalisation proof today ("Assumed", §4.5). **Normalisation stays an open
  question.** What's known:
  - Abel and Coquand's `Ω` doesn't carry over, as far as I can see
    **[inferred; the draft 2 reviewer reaches the same conclusion]**. Their
    loop (§5.2) needs `ω h A`, with `A` a variable, to compute once `A`
    becomes `⊤`, though its proof `h ⊤ A` is a stuck hypothesis. Hand-written
    K computes only on a literal `rfl`, and to use it on `h ⊤ A : ⊤ = A` the
    user would need `rfl : ⊤ = A`, which doesn't check for a variable `A`. And
    nothing in the evaluator later notices that `A` has become `⊤` and
    replaces `h ⊤ ⊤` by `rfl`.
  - Hand-written K does let a function manufacture a constructor from a stuck
    proof, which is the shape of Carneiro's `Acc` trick (§5.1). With
    `Prop.irrel` derived as above (`Loop` and `Loop.inv` as in §5.1, `Box`
    as above), this is accepted under D1′, and `Loop.expose l` computes to
    `MkLoop (Loop.inv l)` for a variable `l`, because `boxEq` and then
    `Prop.irrel` compute to `rfl` **[inferred]**:

    ```
    theorem boxEq (a: Prop) (p: a) (q: a): MkBox p = MkBox q := rfl   -- needs D1′

    theorem Prop.irrel (a: Prop) (p: a) (q: a): p = q :=
      J (\y e2 => p = Box.unbox y) rfl (boxEq a p q)

    def Loop.expose (l: Loop): Loop :=
      J (\y e => Loop) (MkLoop (Loop.inv l)) (Prop.irrel Loop (MkLoop (Loop.inv l)) l)

    def bad (l: Loop): Void :=
      match Loop.expose l with
        | MkLoop n => bad n
    ```

    If `bad` were accepted it would prove `Void`, and unfolding it on an open
    `l` would never stop. It's rejected by the termination checker, which
    reads descent from the terms and doesn't use comparison or evaluation:
    `n` is a part of `Loop.expose l`, not of `l`. Run today, with `Prop.irrel`
    built from `boxEq: MkBox p = MkBox q := rfl` (the only part that needs
    D1′): `boxEq` is `E-REFL` today, and `bad` is `E-TERMINATION` ("no
    argument is known to be smaller"), and nothing else is reported. With
    `Prop.irrel` passed in as a hypothesis instead, `Loop.expose` checks
    today and `bad` is again `E-TERMINATION` **[run]**. This is test 14.
  - If some other term does loop, the budget turns it into `E-RESOURCE`, as
    today.

**Could the gap be closed?** Partly, by stage 3 (§9): give `conv` Rocq-style
marks for the *context's* variables, so two neutral values whose heads are
proof variables (or theorems), with only applications in their spines, are
equal. That makes `p ≡ q` and `f p ≡ f q` above, and
`theorem pi (p q : a) : p = q := rfl`, check. Variables bound *during* a
comparison (under a lambda) have no mark, so it stays incomplete
**[inferred]**. Not proposed for stage 1; question 4, §10.

## 6. Options

### Option A: no definitional irrelevance; keep and extend workarounds

Keep `[auto]` lemma arguments and the `canonical` pass, and add a built-in
*propositional* irrelevance theorem, `proofIrrel : (P : Prop) -> (p q : P)
-> p = q`, justified by the same model (Lean proves it by `rfl`; Rocq offers
it as an axiom) **[inferred; Rocq's axiom unverified here]**.

- *Gains:* §2.1 can be fixed by hand with a transport along `proofIrrel`;
  nothing in the kernel changes.
- *Kernel:* one new built-in theorem, trusted. It blocks computation (`J` on
  it is stuck), so it's harmless to normalisation.
- *Costs:* users still see "`'a'` and `'a'` aren't equal" and must write the
  transport; each new kind of proof-carrying value (records with proof
  fields, `Char`-like types) needs its own elaborator trick.
- *Soundness / decidability / hashing / JS:* unchanged (one trusted constant).

### Option B: irrelevance only for a narrow class (equations at `Bool`)

Make proofs of `a = b` at type `Bool` (or at a fixed list of types with
decidable equality) definitionally equal: what `canonical` does today, moved
into the kernel. Every such equality is already a theorem (`Bool.uniqueEq`,
by Hedberg's argument), so the rule adds nothing new to the logic
**[inferred]**.

- *Gains:* §2.2 and §2.3. **Not §2.1**: a proof of `d != 0` is a *function*
  `d = 0 -> Void`, and two such functions are provably equal only with
  function extensionality, which Stitchwort doesn't have.
- *Kernel:* the same position machinery as D1′, plus a check of the
  proposition's shape. So it's no simpler than D1′.
- *Verdict:* the safety is real but D1′'s argument (§5.6) is not much
  weaker, and B leaves the motivating example unsolved.

### Option C: a separate sort of strict propositions (Rocq `SProp` style)

Add `SProp` beside `Prop`; all proofs of an `SProp` are equal; an `SProp`
can only be eliminated into another `SProp`, except empty types.

- *Gains:* a design with a published decidability proof **[checked: G]**.
- *Users:* must choose between two logics. `Char`'s field would become
  `valid : IsTrue (Char.isScalar code)` with `IsTrue : Bool -> SProp`
  computing to a strict unit or empty type (Rocq's `is_true` encoding
  **[checked: R1 mentions `is_true` in its encodings]**); `d != 0` would need
  a strict negation. Existing `Prop` lemmas don't apply to `SProp`
  statements without boxing. Transport along an `SProp` equality is
  impossible, so `rewrite` can't use them.
- *Kernel:* a new sort; elimination rules for it; erasure must treat it like
  `Prop`; positions still need marks (as D1′).
- *Verdict:* the most principled, and the only option here without §5.7's
  gap (an `SProp` box can't be taken apart into data). But it splits the
  logic, which goes against "propositions are types" being one simple story
  (DESIGN §6), and the effort lands on users.

### Option D: Lean-style, for all of `Prop`

Three levels:

**D1′ (recommended): skip proof positions when comparing; nothing else.**
When `conv` compares two values with the same head, it skips the arguments
whose declared type is in `Prop`: a definition's parameters, a
constructor's fields, a data type's parameters. `rfl`, `J`, `case` and
evaluation are unchanged.

- *Gains:* §2.1, §2.2 and §2.3 all become `rfl` (§2.4); `canonical` and the
  second `[auto]` proofs in the `Int` lemmas become unnecessary; equal
  records with different proof fields are equal (`MkSortedList xs p ≡
  MkSortedList xs q`, docs/proposals/records.md R7); propositional proof
  irrelevance becomes a provable theorem (§5.7).
- *Not gained:* two bare proofs (`rfl : p = q` for variables `p q : a`, or
  `f p ≡ f q` with `f` a hypothesis: `conv` doesn't know their types), and
  anything needing computation on a non-canonical proof (`J … h` with
  `h : a = a` a variable still stuck; `steps l 0` still stuck). Stage 3 (§9)
  can add the first.
- *Known gap:* algorithmic subject reduction (§5.7): failures to check, not
  false acceptances (given §5.6).
- *Kernel:* §7.
- *Soundness:* §5.6, given the same-type invariant (§7.4).
  *Decidability:* the evaluator is unchanged, and `conv` only compares less,
  so checking a given term terminates whenever it does today; more terms are
  accepted, and normalisation is unproved (§5.7).
  *Predictability:* on well-typed values of a common type, the masked
  relation is structural equality of normal forms with the masked parts
  ignored, plus the existing eta rules, and is intended to remain an
  equivalence relation (reflexive, symmetric, transitive)
  **[inferred; to be tested, §8]**. It doesn't fail transitivity the way
  §5.1 describes, because it never equates an unreduced term with a reduced
  one (the price is the same incompleteness: `steps l 0` and
  `steps (MkLoop (Loop.inv l)) 0` stay different). It is *not* a congruence
  for computation: `MkBox p ≡ MkBox q`, yet `Box.unbox (MkBox p)` computes
  to `p`, `Box.unbox (MkBox q)` to `q`, and those differ (§5.7). The claim is
  not made for values of different types: that's what §7.4 excludes.
- *Hashing, JS, erasure:* unchanged (§7.7).

**D1 (draft 1, withdrawn): D1′ plus "`rfl : p = q` whenever the equation is
between proofs".** The extra rule adds nothing to what the rules imply
(§5.7 derives `p = q` anyway), but makes the checker accept `rfl : p = q`
while its comparison still says `p ≢ q` everywhere else, for example in
`f p` against `f q`. Two notions of "equal" in one checker; dropped.

**D2 (not recommended): full Lean.** Typed comparison (infer the type of any
two values being compared, and if it's a proposition, stop), plus K-like
computation for `J`.

- *Gains over D1′:* local-variable positions, top-level proofs anywhere,
  subject reduction for §5.7's example, and transport along any proof of
  `a = a` computes.
- *Kernel:* `conv` would need the type of every value it compares, but
  values don't carry types (lambdas have no domain, constructors no
  parameters), so this is a rewrite of `conv` and the unifier, or a parallel
  type-inference for values.
- *Soundness:* as D1′ (Lean's model). *Decidability:* the Abel–Coquand term
  (§5.2) loops; Carneiro's argument (§5.1) applies.
- *Verdict:* the gains are rare in Stitchwort's programs so far, and the
  costs are exactly the known pitfalls.

### Comparison

| | A | B | C | **D1′** | D2 |
|---|---|---|---|---|---|
| §2.1 divisor | by hand | no | with new types | **yes** | yes |
| §2.2, §2.3 chars | elaborator | yes | with new types | **yes** | yes |
| New kernel code | 1 constant | ~D1′ | new sort + rules | **masks + skips** | typed `conv` + K |
| Termination of checking | as today | as today | as today | **evaluator unchanged; no non-normalising term known; unproved (§5.7)** | lost (§5.2) |
| Subject reduction gap | no | no | no | **yes; failures, not false acceptances (§5.7)** | Carneiro's only |
| Users' mental model | "use `proofIrrel`" | "Bool equations only" | two logics | **"proofs in arguments and fields never matter for equality, but still compute"** | "proofs never matter" (mostly) |
| JS / erasure | unchanged | unchanged | `SProp` erased too | **unchanged** | unchanged |

## 7. The recommended design in detail

### 7.1 The rule

> **Proof positions.** A *proof position* is: parameter `i` of a definition
> whose type's `i`-th domain is in `Prop`; field `i` of a constructor whose
> `field_sorts[i]` is `Prop`; parameter `i` of a data type whose declared
> type is in `Prop`. When comparing two values of the same type with the
> same head, arguments at proof positions are equal without being compared.
>
> Nothing else: evaluation, `rfl`, `J` and `case` are unchanged.

In docs/core.md, "There's no definitional proof irrelevance" (line 121)
becomes this rule, with the sentences: "Proofs in arguments and fields are
ignored when comparing, but still used when computing: `J` needs `rfl`, and
a `case` on a proof needs a constructor. Two proof *variables* are still
compared, so `rfl : p = q` needs `p` and `q` to be the same." And the
precondition of §7.4 goes in `conv`'s doc comment.

### 7.2 Where `conv` changes (`crates/core/src/value.rs`)

- **`Data` against `Data`** (`:1268`): skip `a1[i]`/`a2[i]` where the data
  type's parameter `i` is a proof position.
- **`Ctor` against `Ctor`** (`:1275`): skip field `i` where
  `g.data(d).ctors[c].field_sorts[i] == Sort::Prop`. **Not**
  `field_erased`.
- **`Neutral` against `Neutral`, same `Def` head** (`:1291`, `spine_pairs`
  at `:1331`): skip `Elim::App` arguments at the definition's proof
  positions. Only the spine's *leading* `App` entries are the definition's
  arguments: entry `i` is skipped only if entries `0..=i` are all `App` and
  `proof_params[i]` is set (so `i` is within the telescope). Once a `J`
  entry appears, everything after it eliminates the result (`(J P d (f x
  h)) y` is the spine `[x, h, J, y]`) and stays relevant. `Elim::J` entries
  are compared as now (motive and base are relevant; the proof is the head,
  which is compared already). Both branches of that arm (fully applied, and
  the partially applied/eta one) use the same pairs, so both get the skip.
  Test 15 pins the `J` boundary.
- **`Var` and `Meta` heads**: unchanged in stage 1 (no type information).
- **Compact text** (`Chars`): nothing to do. A range against a constructor
  is expanded one cell to `MkChar c rfl`, whose `valid` field is then
  skipped; the comment at `:1220` ("equal only if `h` and `rfl` are")
  changes.
- **`Eq` against `Eq`, `Refl`**: unchanged.
- **`reference.rs` `conv`** (`:373`): the same change, independently
  written, so the differential tests still mean something.

### 7.3 Deciding "is this a proof position?" cheaply

Like Rocq's relevance marks (§4.2), but read from what the kernel already
computes when it checks declarations, so no new syntax and nothing the
elaborator can get wrong. Positions count from the start of a `Def` spine
and stop at its first `J` entry (§7.2):

- **Constructors**: `field_sorts` exists (`globals.rs:117`).
- **Definitions**: a new `proof_params: Box<[bool]>` on `Def`, computed once
  from the checked signature with `check::telescope` (`check.rs:1744`) and
  `sort_of(dom) == Sort::Prop`, at `declare_def` (`check.rs:943`), so it's
  available while the definition's own group is being checked (pending
  definitions appear as stuck heads). Not `erase::of_def`, which (a) only
  works for final definitions and (b) also marks types. Positions beyond the
  telescope (a definition whose result is a function computed by its case
  tree) count as relevant.
- **Data types**: `proof_params` from the checked parameter telescope, at
  `declare_data`. A parameter `p : Prop` is *not* a proof position
  (`sort_of(Prop)` is `Type 0`); test 9 pins this.

Cost: one pass over each signature at declaration; then a bit lookup per
argument compared. Comparison does strictly less work than today
**[inferred]**; worth confirming with `bench` (§9).

### 7.4 The same-type invariant, the audit of every caller, and undoing failed unifications

**The invariant.** Every call `conv(v, w)` and `unify(v, w)` that can reach a
masked comparison is made on two values of the same type (equal in the
model). Inside the comparison it then holds for every pair reached, by
construction: parts at the same position under a common head have the same
declared type, instantiated with the earlier parts, which either compared
equal or were skipped proofs (equal in the model); `Eq` against `Eq`
compares the type first, and the result is "equal" only if the types are;
lambda bodies are compared under the same fresh variable. The only places
where a value's type isn't fixed by its surroundings are the top-level call
and a constructor's missing parameters, so the audit is of the top-level
calls **[inferred]**. This relies on both `conv` and `unify` taking parts
left to right, element type before endpoints, domain before codomain
(`unify.rs:19-22` says so for `unify` **[checked]**); a future change to
either must keep that order.

**What happens to a comparison that fails part-way differs:**

- *`conv`* has no side effects, so pairs visited before it answers "not
  equal" don't matter.
- *`unify`* is not atomic: it solves metavariables as it goes
  (`solve` calls `g.solve_meta` at once, `unify.rs:333`), and a later part
  that fails leaves the earlier solutions in place. With D1′ that includes a
  whole proof metavariable solved at a proof position (§7.5): unifying
  `MkT ?p 1` with `MkT q 2` (field 0 a proof) solves `?p := q`, then fails.
  The kernel re-checks everything, so this can't make a false proof check,
  but code that then tries *another way* would start from a polluted state,
  making elaboration depend on the order things were tried **[inferred; the
  draft 2 reviewer's point]**.

  The elaborator already handles this. `undo.rs:1-5`: "The unifier isn't
  atomic: a comparison that fails part-way keeps the solutions it made
  before failing. So anything that tries one way and, if it doesn't work,
  another, runs the first inside a transaction." Every solution is recorded
  on `Globals::meta_trail` (`globals.rs:233-236`) and `Snapshot::restore`
  undoes them (`undo.rs:60-84`); `undo::unify` (`undo.rs:122-124`) is the
  all-or-nothing version; `auto`'s alternatives each run in a transaction
  (`auto.rs:86`, `:140`, `:149`, through `attempt`, `:196-198`); and a unit
  test pins the behaviour (`a_comparison_that_fails_part_way_solves_nothing`,
  `undo.rs:167`) **[checked]**. Other callers that try alternatives take
  snapshots too (`check.rs:835`, `:1498`, `:1548`, `logic.rs:98`, `:109`,
  `:239`, `numbers.rs:612`, `pipe.rs:105`, `bind.rs:68`, `:188`)
  **[checked that they exist; not each traced]**.

  So D1′ adds no new kind of state, provided **stage 1's proof-metavariable
  solutions go through `solve`/`solve_meta`** like every other solution, not
  through a new path that bypasses the trail. Test 16 adds the D1′ shape to
  `undo.rs`'s tests. Any new code that retries after a `false` from `unify`
  must use `undo::transaction` (already the rule; restate it in `unify`'s doc
  comment next to the same-type precondition).

Types at the top level are easy: a type's own type is a sort, so it's never
a constructor value (constructors build values of data types); skips below it
happen under a common head, which fixes the types. Two types of *different*
sorts can be compared (`Nat` against `Prop`); that's harmless for the same
reason.

**Audit of `conv` callers** (all of them outside tests; `grep` for `conv(`
in `crates/core/src` and `crates/elab/src`; other crates call it only from
tests; `reference.rs`'s calls are its own recursion; re-checked at
`bc89481`) **[checked]**:

| Call site | Compares | Same type? |
|---|---|---|
| `core/check.rs:412` | the two sides `a`, `b` of an expected `Eq(ty, a, b)`, for `rfl` | yes: both `: ty` |
| `core/check.rs:446` | a term's inferred type against the expected type | types |
| `core/native.rs:253-255` | `Decidable`'s parameter type against `Prop`; its constructors' field types against `p`, `Not p` | types |
| `core/native.rs:340`, `:393` | a native's declared type against the expected shape | types |
| `core/partial.rs:350` | a primitive's declared type against the expected shape | types |
| `core/value.rs:1313` | recursive, inside `conv` (partially applied definitions) | inherited |
| `elab/lib.rs:1021` | parameter types of mutually defined data types | types |
| `elab/lib.rs:2391` (`canonical`) | the two sides of `p : a = b` at `Bool` | yes: both `: Bool` |
| `elab/partial.rs:700` | parameter types of partial-recursive members | types |
| `elab/partial.rs:750-751` | the members' rows: `ops` and `res`, arguments 0 and 1 of the same `Comp`/`Delay` type (`partial.rs:629-630`) | yes: same telescope positions **[inferred]** |

**Audit of `unify` callers** (the unifier has the same structure,
`unify.rs:23`; every `unify(` in `crates/elab/src` outside tests, re-checked
at `bc89481`): most compare types (`elab/check.rs:871, 942, 1132, 1156,
1272, 1492, 1504, 1553, 1845, 1860, 1943`, `numbers.rs:120, 472, 498, 641`,
`pipe.rs:110`, `dot.rs:675`, `lib.rs:2575`, `patlet.rs:153`,
`auto.rs:86, 383`, `effects.rs:1214, 1465, 1539, 1656, 2114, 2330, 2346`;
draft 2 missed `check.rs:871, 1492` and the `effects.rs` ones). The ones that
compare non-type values **[checked]**:

| Call site | Compares | Same type? |
|---|---|---|
| `elab/check.rs:1229` | the two sides of an `rfl` goal | yes |
| `elab/check.rs:889` | a postponed argument, checked against `dom`, against its placeholder metavariable of type `dom` | yes |
| `elab/dot.rs:724` | a written argument checked against `dom`, against its placeholder of type `dom` | yes |
| `elab/auto.rs:69` | an obligation's placeholder against a proof found for its goal | yes |
| `elab/auto.rs:411` | an argument metavariable of type `dom` against a value found for `dom` | yes |
| `elab/effects.rs:377`, `:676` | a row tail against `MkSig ops res` (a constructor value; `:676` was missed in draft 2) | yes: `Sig` has no parameters (prelude:2104-2105), and the tail has type `Sig` **[inferred]** |
| `elab/effects.rs:382`, `:442`, `:691` | the arguments of two labels for the same ability; two row tails (`:691` missed in draft 2) | yes: same telescope positions / both `Sig` |
| `unify.rs:75, 201, 277` | recursive | inherited |

**Result: the invariant holds today.** No caller compares two values whose
types could differ.

**Choice: write the invariant down, rather than pass types or keep
parameters.** The alternatives the reviewer named:

- *Keep parameters in constructor values* (`Ctor(d, c, params, fields)`):
  every list cell and character would carry its type arguments, costing
  memory and time in the evaluator for everything, not just the checker, and
  changing quotation, erasure and the unifier.
- *Pass the common type into `conv`*: a typed comparison, which is D2's
  rewrite (§6).

Both buy safety against a future caller breaking a rule that every current
caller keeps for free (the elaborator always checks both sides against one
type before comparing). So: state the precondition prominently ("**Precondition:
homogeneous values**: `a` and `b` have the same type; breaking this can be a
soundness bug, not just a wrong `false`") in the doc comments of
`value::conv`, `reference::conv` and `unify::unify`, and in docs/core.md;
add test 10 (`MkBox p = MkBox q` at different propositions is rejected, by
`E-TYPE-MISMATCH`, before any comparison of the boxes); and make "every new
`conv`/`unify` caller compares values of one type" a review item for kernel
changes. If a heterogeneous caller is ever needed, it must compare the types
first and only then the values.

### 7.5 The unifier (`crates/elab/src/unify.rs`)

The elaborator must agree, or it rejects §2.1 before the kernel sees it
(`elab/check.rs:1229`). At a proof position (the same masks, from
`Globals`), in the `Data`, `Ctor` and `Def`-headed `Neutral` arms
(`unify.rs:111`, `:118`, spines at `:219`):

- **If the complete argument on one side is an unsolved metavariable** (a
  `Neutral(Meta, spine)` with the spine allowed by the existing pattern
  rules), solve it with the other side, as now: the existing occurs and
  scope checks apply, and its type is already known (that's what keeps
  implicit proof arguments, `[auto]` placeholders and `_` proofs working).
  The two arguments have the same type by §7.4 and the left-to-right order
  (earlier arguments are unified first), so the solution is well-typed.
- **Otherwise the position is opaque**: succeed without looking inside
  either side. Don't recurse into it, and don't solve any metavariable,
  nested or enclosing, from what's inside it.

So a metavariable that occurs *only* inside a proof argument, and not in any
type, stays unsolved and is reported as unsolved, as it is today when nothing
determines it (test 11). Nor does anything flow out of the proof into later
relevant parts: in `MkT (f ?m) ?m` against `MkT (f 3) ?k` (field 0 a proof),
`?m` is solved from field 1 only, as `?k` (or `?k := ?m`), never as `3`
(test 11b).

A proof metavariable is solved with the ordinary `solve`, so the solution is
on the undo trail and a failed attempt's transaction removes it (§7.4,
test 16). In practice proofs' metavariables are usually
pinned by types (the proposition is a relevant parameter, e.g. `Box`'s `p`),
which still works.

Why not "unify as usual and ignore failure"? Because then a solution can come
from inside a proof that the kernel's comparison never looks at. The kernel
re-checks everything, so that can't make a false proof check, but it is the
pattern behind #8699 (information read out of an irrelevant part, §5.4), and
it would make elaboration depend on which proof was written.

Unsolved proof metavariables are still reported as they are today, and the
kernel re-checks the result anyway.

### 7.6 What doesn't change

- **Evaluation**: no new reduction, so programs, tests and natives behave
  exactly as before. The erasure rules (`erase.rs`) and JS extraction
  already ignore proofs at runtime; irrelevance is about checking only.
- **`rfl`** (`check.rs:411`): still checks only by `conv`.
- **Termination checking**: untouched (§5.4).
- **`E-PROP-ELIM`**: untouched. It's what keeps §5.3 away.
- **Caches**: the kernel only accepts more than before; every cache key
  includes the compiler version or source fingerprint (DESIGN §11), so no
  old rejection is reused.

### 7.7 Hashing and JS

**Hashes**: no elaborated term changes in stage 1, so no hash changes. In
stage 2, removing `canonical` changes the elaborated terms (and hashes) of
definitions with char-pattern arms that mention the character; that's
allowed (hashes aren't a constraint yet, TODO.md).

**Should a proof's body affect a hash? Yes, still** (no change proposed). A
theorem's hash covers its body (DESIGN §11), and so do the hashes of
everything that uses it. One could argue that with irrelevance a dependent
can't observe the body, so its hash needn't change when a proof is
rewritten. That's false under D1′: a proof can still *compute* inside a
dependent's check (`J` on `myLemma x` computes if `myLemma x` evaluates to
`rfl`; a `case` on a `Loop`-like proof computes on its constructor), so
changing a proof's body can change whether a dependent checks
**[inferred]**. What *is* true: a proof's body can never change a test's
result, because proofs are erased when running (`erase.rs`). So a later
optimisation could leave theorem bodies out of the *test-result* cache key.
Not proposed here.

Separately, two definitionally equal terms can have different hashes (they
already can: `2 + 2` and `4`). Hashes identify terms, not meanings, so that's
fine.

### 7.8 `auto` and `Decidable` (multi-file note §4.9.4)

Multi-file §4.9.4 says the decision procedure `auto` picks is visible to
proofs, citing `aoc/day02.sw:337-344` (`decIsTrue` exists so that `if IsTrue
c` uses the same procedure as `if lo <= hi`). **D1′ doesn't change that
case**: a `Decidable p` is data (it lives in `Type`, DESIGN §6), so
`Bool.decTrue c` and `Bool.decEq c True` stay different, and an `if` that
computes with one doesn't match the other **[inferred]**.

It does change the other half: for an `[auto ok : p]` *proof* argument,
which candidate found the proof becomes invisible to comparison (that's
§2.1). So §4.9.4's point 1 shrinks to "the *procedure* is visible where it's
run as data (`if`, `==`)", and the order rules there stay as they are.

### 7.9 What users will still hit

"Proofs in arguments and fields are ignored when comparing, but still used
when computing." So these remain:

- `rfl : p = q` for two different proof variables: rejected. Prove it
  through a box as in §5.7 (`piViaBox a p q rfl`), or wait for stage 3. A
  prelude `Prop.irrel` is deferred (§10 question 2). If it's ever added, its
  documentation must say that it computes: `J … (Prop.irrel p q)` reduces
  when `p` and `q` are any proofs, which is surprising.
- `J P d h` with `h : a = a` a variable or a lemma call: stuck (no K-like
  rule, deliberately: §5.2).
- A function that matches a proof to produce data (`steps`, or `pick` on
  `And`) is stuck on a non-constructor proof.
- Proof arguments of local function variables are compared (until stage 3).
- Rarely, a value that computed from a transport along a hand-made `rfl` is
  rejected at the type of the expression it came from (§5.7).

The `E-REFL`/`E-TYPE-MISMATCH` message could add a note when the two sides
print the same, saying they differ in a part the printer hides; that's a
small independent improvement.

## 8. Tests

Per the soundness policy (DESIGN §13), each must-reject test has a nearby
accepted one, and declares its error code. Tests 9-13 and the changed
pairings of 4 and 6 are new in draft 2; 11b and 14-16 in draft 3.

| # | Must be rejected | Code | Why it matters | Paired accepted example |
|---|---|---|---|---|
| 1 | `rfl : MkTBox Nat = MkTBox Bool` for `type TBox : Type 1 = MkTBox (t : Type)` | `E-REFL` | A type field is erased but relevant: catches `field_erased` used for `field_sorts` | `rfl : MkChar 97 p = 'a'` (§2.2) |
| 2 | `rfl : choose Nat n = choose Bool n`, for `choose : Type -> Nat -> Nat` stuck on `n` | `E-REFL` | The same for definition parameters (`erase::of_def` marks types) | `sameMod` (§2.1) |
| 3 | `rfl : Sorted [1, 2] = Sorted [2, 1]`, for a test-defined `type Sorted (xs : List Nat) : Prop` | `E-REFL` | Data parameters that are data stay relevant | A data type with a proof parameter, two different proofs, `rfl` |
| 4 | With a test-defined `type Exists (p : Nat -> Prop) : Prop = MkEx (x : Nat) (h : p x)`: `def leak (e : Exists (\n => n = n)) : Nat` matching out the witness; and `rfl : MkEx 1 rfl = MkEx 2 rfl` | `E-PROP-ELIM`; `E-REFL` | Irrelevance must not leak a proof's data (§5.3); a data field inside a proof is still compared | `rfl : MkEx 1 h1 = MkEx 1 h2` for two proofs `h1 h2 : 1 = 1` (the witness agrees, the proof field is skipped) |
| 5 | `J (\y e => P y) d h = d` for a variable `h : n = n` | `E-REFL` | No K-like rule (§5.2) | `J (\y e => P y) d rfl = d`; and `omegaUnfolds` (§5.2) checks within the default budget |
| 6 | `rfl : f = g` for two different `f g : Unit -> {IO} Unit` | `E-REFL` | Effectful functions are data, never proofs | `rfl : MkBox p = MkBox q` for `p q : Unit` (the `Prop`) |
| 7 | Agda #8699's shape adapted: a recursive call whose argument is smaller only inside a proof field that comparison ignores | `E-TERMINATION` | §5.4 | Structural recursion on a real proof field (`Loop -> Void`, `f (MkLoop n) = f n`) |
| 8 | `rfl : x = y` for two different variables `x y : Nat` inside a record with a proof field | `E-REFL` | Skipping the proof must not skip its neighbours | `rfl : MkSortedList xs p = MkSortedList xs q` for a test-defined record with a proof field |
| 9 | `rfl : R Unit = R Void` for `type R (p : Prop) : Type = MkR` | `E-REFL` | A *proposition* parameter is relevant: guards `sort_of(dom) == Prop` against classifying `p : Prop` as a proof | `rfl : R Unit = R Unit`; and test 3's paired proof parameter |
| 10 | `rfl : MkBox p = MkBox q` for `p : a`, `q : b`, `a b : Prop` | `E-TYPE-MISMATCH` | The same-type invariant (§7.4): the boxes have different types, so comparison is never asked | `rfl : MkBox p = MkBox q` for `p q : a` |
| 11 | Unifier unit test (`unify.rs` tests): `unify(MkBox (f ?m), MkBox (f 3))` with `f`'s argument data but `MkBox`'s field a proof: `?m` stays unsolved | unit test; at the language level, the unsolved-metavariable error | §7.5: never solve from inside a skipped proof | `unify(MkBox ?p, MkBox q)` solves `?p := q` (whole proof argument) |
| 11b | Unifier unit test: `unify(MkT (f ?m) ?m, MkT (f 3) ?k)`, field 0 a proof, field 1 data | unit test | §7.5: nothing read from inside a skipped proof reaches a later relevant field: afterwards `?m` is not `3` | the same with field 0 relevant (a test-only data type) solves `?m := 3`, then `?k := 3` |
| 12 | `theorem pi (p q : a) : p = q := rfl` for variables `p q : a` | `E-REFL` | Documents the incompleteness: bare proof variables are compared (until stage 3) | `piViaBox a p q rfl : p = q` (§5.7) |
| 13 | `def bad (a : Prop) (p q : a) (f : a -> Type) (x : f p) : f q := x` | `E-TYPE-MISMATCH` | Documents the subject-reduction gap (§5.7): `castViaBox a p q f x rfl` computes to `x`, but `x` itself is rejected at `f q` | `def ok … : f q := castViaBox a p q f x rfl` |
| 14 | `bad (l: Loop): Void` matching on `Loop.expose l` and recursing on the field (§5.7), with `Prop.irrel` built from `boxEq: MkBox p = MkBox q := rfl` | `E-TERMINATION` | A computing `Prop.irrel` manufactures a constructor from a stuck proof; that must never count as descent. Today: `E-TERMINATION` **[run]** (and `boxEq` is `E-REFL`, which D1′ fixes) | `Loop.expose` itself is accepted, and `theorem (l: Loop): Loop.expose l = MkLoop (Loop.inv l) := rfl` checks (today `E-REFL`, needs `boxEq` **[run]**); plus test 7's structural `Loop -> Void` |
| 15 | With `def fnEq (n: Nat) (h: Unit): (Nat -> Nat) = (Nat -> Nat)` stuck on `n` and `def apply (f: Nat -> Nat) (x: Nat): Nat := f x`: `rfl : apply (J (\y e => y) (\x => x) (fnEq n u)) 3 = apply (J … (fnEq n u)) 4` | `E-REFL` | Masks cover only a definition's leading arguments, never an argument after a `J` entry (§7.2). A `J` entry can only come after at least the whole telescope (the proof must be an equation), so a mask indexed by spine position already gets this right; the test pins the rule against a looser implementation **[inferred]**. (`J` with a fourth argument is `E-ARITY`, hence `apply`.) Today: `E-REFL` **[run]** | the same with `fnEq n u1` and `fnEq n u2` and both applied to `3` (position 1 of `fnEq` is a proof position). Today `E-REFL` **[run]**; D1′ must accept |
| 16 | `undo.rs` unit test: inside `undo::unify`, `MkT ?p 1` against `MkT q 2` (field 0 a proof) | unit test | §7.4: a whole-proof solution made before a failure is undone by the transaction (`?p` unsolved afterwards); bare `cx.unify` leaves `?p := q`, documenting why the transaction is needed | `MkT ?p 1` against `MkT q 1` solves `?p := q` |

Must not hang: `steps l 0 = steps (MkLoop (Loop.inv l)) 0` is rejected
promptly (`E-REFL`), documenting the incompleteness of §5.1.

Also:

- **Mutation tests**: skipping nothing must fail the accepted tests;
  skipping erased positions (types too) must fail tests 1, 2 and 9; skipping
  every argument must fail tests 3, 4 (second part), 6 and 8; unifying
  inside skipped proofs must fail tests 11 and 11b; skipping every `App`
  after a head that has any proof position must fail test 15; solving proof metavariables without the undo
  trail must fail test 16.
- **Differential**: `value::conv` against `reference::conv` on the kernel
  test programs, as for the evaluator.
- **Equivalence (property test)**: on generated well-typed values of one
  type, the masked `conv` is reflexive, symmetric and transitive, including
  pairs that need the existing eta rules (`push_eta`, lambda against
  neutral, partially applied definitions).
- **Unifier**: an implicit proof argument solved only by unification still
  gets solved.
- **Regression**: `examples/accept/char-pattern-proofs.sw` checks with and
  without `canonical` (stage 2 removes it); `aoc/` still checks.

## 9. Stages

1. **Kernel and unifier** (Sonnet, from this note): the masks (§7.3), the
   `conv` skips with the `J` boundary (§7.2), the reference `conv`, the
   unifier rule with proof solutions through `solve` (§7.5), the
   precondition comments ("homogeneous values"; retry only inside
   `undo::transaction`, §7.4), the tests in §8 (including 11b and 14-16),
   docs/core.md and DESIGN §6 line 459 ("isn't needed for the POC" becomes
   the rule), the pointer in mutual-recursion.md §6.7. Bench comparison
   before and after. Needs only §10 question 1.
2. **Remove workarounds** (Sonnet or DeepSeek): delete `canonical`
   (`elab/src/lib.rs:2370` and its callers at `:2479`, `:2528`) and check
   char-pattern proofs and `aoc/` still pass; optionally simplify
   `Char.mkExt` and the second `[auto]` proofs of `Int.modNatToInt`,
   `Int.toIntDiv`, `Int.toIntMod`; update hash snapshots. No `Prop.irrel`
   in the prelude unless a program needs it (question 2).
3. **Later, if a program needs it**: proofs that are *context variables*.
   `conv` would take one mark per context variable ("its type is a
   proposition"; the checker has the types), so two neutral values whose
   heads are marked variables or theorem definitions, with only
   applications in their spines, are equal; and a local function variable's
   type read as a telescope gives its proof positions. Variables bound inside
   the comparison (under a lambda) have no mark and stay relevant. Narrows,
   doesn't close, the §5.7 gap.
4. **Not planned**: K-like `J`, eta for proofs of single-constructor
   propositions in `case` (Lean doesn't do it either, §4.1), `SProp`, the
   draft 1 `rfl` rule.

## 10. Questions for Matt

Only question 1 blocks stage 1. The rest affect stage 2 or later.

1. **Adopt D1′?** In plain terms: when the checker compares two values, it
   stops caring *which* proof was given in a function argument or a
   constructor field, but proofs still matter when the program computes.
   The cost is a rare oddity: a value can be accepted while the thing it
   computes to is rejected at the same type (§5.7). That shows up as an
   error, never as a false proof being accepted. Whether every program still
   finishes checking is no more proved than it is today, and no
   counterexample is known (§5.7). *Recommendation: yes.* It fixes the real
   problems (§2) with a small change, both reviews support it, and the
   alternatives either don't fix the `Int` case or split the logic in two.
2. **Leave `Prop.irrel : (p q: a) -> p = q` out of the prelude for now?**
   Draft 2 proposed adding it. It adds no power (anyone can write it, §5.7),
   but it would make the surprising behaviour of §5.7 one call away.
   *Recommendation: yes, leave it out* until a program needs it; if it's
   added, its documentation says it computes.
3. **Remove the `canonical` workaround** in stage 2, changing the hashes of
   definitions with character-pattern arms? *Recommendation: yes.* No
   program in the repository relies on what only `canonical` does (§2.4).
4. **Wait for a real need before stage 3** (letting two bare proof variables
   compare equal)? *Recommendation: yes, wait.* Nothing in `aoc/` or the
   examples needs it.

(Settled and no longer asked: no K-like rule; hashes keep proof bodies;
comparison stays untyped with the same-type rule written down, which both
reviewers accept.)

## 11. Questions for the reviewer

None. The draft 2 review's changes are wording, tests and one requirement
already met by existing code (§7.4); none changes the design, and nothing it
raised is still disputed (Appendix B). A third review isn't needed before
stage 1. The implementation itself will be reviewed as usual, and the open
theoretical question (normalisation, §5.7) isn't one that another review of
this note can settle.

## 12. What I couldn't verify

- Whether Idris 2's checker skips quantity-0 arguments when comparing (§4.4).
- Lean 4's current treatment of `Acc` in the kernel; Carneiro's thesis
  describes Lean 3 (2019), and the Lean 4 kernel source I read
  (`inductive.h`, `type_checker.cpp`, master, 19 October 2026) was only the
  parts quoted.
- Whether Rocq's documented Definitional-UIP non-termination example is the
  Abel–Coquand term (R1 shows "a non-terminating example"; I didn't compare).
- That Rocq offers propositional proof irrelevance as an axiom (option A).
- Werner (2008), cited by Abel and Coquand, was not read.
- No proof of §5.6: it's an argument by analogy with Lean's model.
- Normalisation with D1′ (§5.7). That Abel and Coquand's `Ω` doesn't carry
  over is an inference (shared by the draft 2 reviewer), not a proof, and
  another looping term may exist.
- The rows of §7.4 marked **[inferred]** (`partial.rs:750-751`,
  `effects.rs:377`, `:676`) were read for what the values are, not traced to
  every way they're built. The snapshot-taking callers listed in §7.4 were
  found by `grep`, not each traced.
- §2.4 is reasoning about code, not a run: masks aren't built. The §5.7
  programs, tests 10, 14 and 15 and the box `E-REFL` were run on today's
  build; what they do under D1′ is inferred.
- Experiments in §2 and §5.1–5.2 used the release build of `80c87a8`; the
  `E-REFL` in §2.1 wasn't traced to the elaborator or the kernel.

## Sources

- **[L1]** Lean 4 kernel, `src/kernel/type_checker.cpp`, master, fetched 19
  October 2026: `is_def_eq_proof_irrel` (lines 895-903) and its use before
  `lazy_delta_reduction` (line 1159).
  <https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp>
- **[L2]** Lean 4 kernel, `src/kernel/inductive.h`, same date:
  `to_cnstr_when_K` (lines 27-50), `to_cnstr_when_structure` (lines 61-73,
  "if (is_prop(e_type)) return e;").
  <https://github.com/leanprover/lean4/blob/master/src/kernel/inductive.h>
- **[L3]** The Lean Language Reference, "The Type System".
  <https://lean-lang.org/doc/reference/latest/The-Type-System>
- **[L4]** Mario Carneiro, *The Type Theory of Lean*, MS thesis, CMU, 2019:
  abstract; §2.6 (subsingleton elimination, K-like reduction); §3.1
  (undecidability); §3.1.1 (non-transitivity); §3.1.2 (subject reduction).
  <https://github.com/digama0/lean-type-theory>
- **[L6]** The Lean Language Reference, "Propositional Equality", §20.4.1
  "Uniqueness of Equality Proofs" (latest, read 19 October 2026).
  <https://lean-lang.org/doc/reference/latest/Basic-Propositions/Propositional-Equality/>
- **[L5]** *Type Checking in Lean 4*, "Definitional equality" and
  "Reduction".
  <https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html>
- **[AC]** Andreas Abel and Thierry Coquand, "Failure of Normalization in
  Impredicative Type Theory with Proof-Irrelevant Propositional Equality",
  LMCS 16(2), 2020. <https://arxiv.org/abs/1911.08174>. §1's `cast` rule
  and the looping step re-read from the PDF for draft 3
- **[G]** Gaëtan Gilbert, Jesper Cockx, Matthieu Sozeau, Nicolas Tabareau,
  "Definitional Proof-Irrelevance without K", POPL 2019: §1, §2.2, §2.3,
  §4.5, §6.1, §6.5, appendices A and B.
  <https://inria.hal.science/hal-01859964v2>
- **[R1]** Rocq reference manual, "SProp (proof irrelevant propositions)".
  <https://rocq-prover.org/doc/master/refman/addendum/sprop.html>
- **[A1]** Agda documentation, "Prop".
  <https://agda.readthedocs.io/en/latest/language/prop.html>
- **[A2]** Agda documentation, "Irrelevance".
  <https://agda.readthedocs.io/en/latest/language/irrelevance.html>
- **[A3]** Agda issue #8699, "Termination checker descends into irrelevant
  constructor arguments of dot patterns", closed 29 August 2026 by PR #8707;
  discussion re-read 19 October 2026.
  <https://github.com/agda/agda/issues/8699>
- **[I1]** Idris 2 documentation, "Multiplicities".
  <https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html>

## Appendix A: response to the draft 1 review

| # | Finding (severity) | Verdict | What changed |
|---|---|---|---|
| 1 | §7.4's `rfl` rule gives computational K and breaks algorithmic subject reduction (`castProofIndex`); fix: drop §7.4 (Critical) | **Accept in part.** The diagnosis is right and §7.4 is dropped. But the fix doesn't remove the problem: masks alone accept `rfl : MkBox p = MkBox q`, and transport plus `Box.unbox` rebuilds the example (`castViaBox`, checked today with `e` as a hypothesis **[run]**). What dropping §7.4 does fix is the "two notions of equal" mismatch: `rfl` is again decided by `conv` alone. The remaining gap is documented as an incompleteness that only rejects. | Changes 1-2; §0, §1 (K, subject reduction), §5.2 last paragraph, new §5.7, §6 (D1 withdrawn, D1′ recommended), §7.1, §7.6, §7.9, tests 12-13, §10 Q1-2 |
| 1a | Optional later opaque `proofIrrel` constant | **Reject (as unnecessary).** Under D1′ it's a provable theorem (`piViaBox`, §5.7); opacity wouldn't stop users writing the computing version. | §5.7, §10 Q2 |
| 2 | "Same head" isn't enough for constructor values, which lack parameters; establish a homogeneous-input invariant or carry types/parameters (Major) | **Accept.** Audited every `conv` and `unify` caller in `crates/core` and `crates/elab`: the invariant holds today. Chose to document it as a precondition (plus test 10 and a review rule) rather than pass types (D2's rewrite) or store parameters (cost to every value). | Change 3; §1 (homogeneous comparison), §5.6 point 2, new §7.4, test 10, §10 Q5 |
| 3 | Unifier rule must be narrowed per Agda #8699: only a whole proof metavariable may be solved; never recurse into ignored proofs; add a test (Major) | **Accept**, with a correction to the background: #8699's fix (PR #8707) was in the termination checker (descent under irrelevant arguments of dot patterns); Abel floated restricting the unifier, Cockx argued against, and the unifier was left alone **[checked: A3]**. The narrowed rule is still right for Stitchwort, as defence in depth. | Change 4; §5.4, §7.5, test 11 |
| 4 | Transitivity/equivalence claim should apply only to the mask-only relation on well-typed values of one type (Major) | **Accept.** Reworded; added a property test; also noted it isn't a congruence for computation (§5.7). | Change 5; §6 D1′, §8 "Equivalence" |
| 5 | Abel–Coquand reading OK, but §7.4 undermines "we didn't alter `J`" (Minor) | **Accept.** Narrow claim kept; added that manufacturing `rfl` between proofs gives hand-written K, by §7.4 or by masks. | §5.2, §5.7 |
| 6 | Lean's docs present K as a consequence of definitional proof irrelevance (Minor) | **Accept the point, unverified source.** The logical point is right and now in §4.1 and §5.7; I couldn't find the cited sentence in the Lean reference. | §4.1, §12 |
| 7 | Label Agda's properties as of the calculus, not the implementation; #8699 fixed Aug 2026 (Minor) | **Accept.** | Change 7; §4.3, §4.5 |
| 8 | Add a must-reject test that `P : Prop` parameters stay relevant (`R True ≢ R False`) (Minor) | **Accept.** Written with `Unit` and `Void`, Stitchwort's true and false propositions (`True` is a `Bool`). | §1, §7.3, test 9, mutation tests |
| 9 | Masks alone fix the motivating programs (in passing) | **Accept, checked.** Including every arm of the char-pattern example; `canonical`'s extra power (computing on the proof) isn't used anywhere. | §2.4 |
| 10 | D1′ fixes Int/Char without "granting general computational proof equality" (verdict) | **Reject that part.** It still grants it, by hand (§5.7); the recommendation stands on rejections-only, not on avoiding it. | §5.7, §6 |
| — | Kept, as the reviewer suggested: `field_sorts` not `field_erased`; evaluation, `J`, `case`, erasure, JS unchanged; proof bodies in hashes; B, C, D2 rejected | No change | — |

Also fixed, found while revising: draft 1's test 4 paired example
`rfl : MkEx 1 rfl = MkEx 2 rfl` and test 6's `rfl : p = q` depended on the
dropped rule (the first is now a must-reject: the witness is data).

## Appendix B: response to the draft 2 review

The reviewer's verdict: adopt D1′ with changes. Each point, checked where it
could be:

| # | Point | Verdict | Where changed |
|---|---|---|---|
| 1 | §5.7's box construction is right; the draft 1 review's opaque `proofIrrel` wasn't a fix; avoid saying the rules "imply full irrelevance" | **Accept.** Reworded to "enough to derive propositional proof irrelevance and a computing K, though the comparison sees irrelevance only at marked positions". | Change 1; §0, §4.5, §5.1, §5.7 |
| 2 | "Rejections only" holds for soundness, via a model where `p` and `q` are one proof; soften to "can fail, get stuck or hit resource limits, but doesn't by itself justify a false term" | **Accept.** The model argument is §5.6's; the wording now names elaborator errors and the budget too. **[inferred]**, as before. | Change 2; §0, §1, §5.7, §6 |
| 3 | The Box K doesn't rebuild Abel–Coquand's `Ω`: their loop needs a cast that fires on definitionally equal endpoints without looking at a neutral proof; still don't claim normalisation | **Accept.** Checked the rule and the loop step against the paper (**[checked: AC §1]**, quoted in §5.2). The conclusion stays an inference; the tables now say "no non-normalising term known; unproved". | Change 3; §0, §4.5, §5.2, §5.7, §6, §12 |
| 4 | Add a direct `Loop.expose`/`bad` termination test using the Box-derived `Prop.irrel` | **Accept, and run.** Today `bad` is `E-TERMINATION`, both with `Prop.irrel` built from `boxEq` (whose `rfl` is `E-REFL` until D1′) and with `Prop.irrel` as a hypothesis **[run]**. The termination checker reads descent from patterns, so D1′ can't change this **[inferred]**. | Change 4; §5.7, test 14 |
| 5 | §7.4's "a pair visited in a failing comparison doesn't matter" is false for `unify`, which solves eagerly; callers that backtrack must restore metavariable state, including whole-proof solutions; audit `auto` and others | **Accept the correction; the requirement is already met.** `undo.rs:1-5` documents exactly this, solutions are trailed (`globals.rs:233-236`) and undone (`undo.rs:60-84`), and `auto`'s alternatives run in transactions (`auto.rs:86, 140, 149, 196`) **[checked]**. D1′'s new solutions must use the same `solve` path. While re-auditing I found eleven `unify` callers draft 2's list missed; all compare types or `Sig` rows **[checked]**. | Change 5; §0, §7.4, §7.5, tests 16, mutation tests |
| 6 | Documenting the same-type precondition is adequate; name it aggressively | **Accept.** Doc comments say "Precondition: homogeneous values" and that breaking it can be a soundness bug. | §7.4 |
| 7 | In a `Def` spine, only the definition's own leading arguments use the masks; anything after a `J` belongs to the result | **Accept.** Specified in §7.2/§7.3. Test 15 written and run (`E-REFL` today for both halves, as expected) **[run]**. Since a `J` can only come after the whole telescope, a mask indexed by spine position already behaves correctly; the test pins the rule **[inferred]**. | Change 6; §7.2, §7.3, test 15 |
| 8 | The unifier rule (whole proof meta, otherwise opaque) is right; add a test where a hidden nested meta would otherwise affect a later relevant field | **Accept.** | §7.5, test 11b |
| 9 | Agda #8699 correction is fair | No change. | — |
| 10 | Don't add `Prop.irrel` to the prelude yet; if added, document that it computes | **Accept.** It adds no power and puts §5.7's surprise one call away. | Change 7; §7.9, §9, §10 question 2 |
| 11 | §1's "never says two different things are equal" is misleading | **Accept.** Now "never equates two values that differ in the proof-irrelevant model". | Change 1; §1 |
| 12 | The Lean sentence exists: "Uniqueness of Equality Proofs" | **Accept, checked.** Quoted in §4.1 **[checked: L6]**. | Change 8; §4.1, §12, Sources |
| 13 | Option C (`SProp`) not worth it for current goals; it would be if a published decidability/normalisation argument became the priority | **Agree.** No change. | — |
