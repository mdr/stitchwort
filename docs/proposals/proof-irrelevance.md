# Proposal: treating two proofs of the same fact as equal (proof irrelevance)

**Status:** Draft 1, 19 October 2026. Design only: nothing is built. Awaiting
Matt's answers (§10) and an independent review (§11).

This note can be read without knowing type theory. §1 explains the words it
needs, with Stitchwort examples. Claims about Stitchwort were checked against
the source at commit `80c87a8`; the programs in §2 were run with a release
build of that commit. Claims about other systems are labelled:

- **[checked: S]**: read in source S (listed in [Sources](#sources));
- **[run]**: a Stitchwort program run at `80c87a8`;
- **[inferred]**: my reasoning from checked facts, not stated in a source;
- **[unverified]**: believed, but not confirmed.

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

## 0. Summary

Today the kernel compares two proofs the same way it compares data: they're
equal only if they compute to the same thing. So `x % 100` with a
hand-written proof that `100 != 0` and `x % 100` with `auto`'s proof have
different types that print the same, and a hand-built character
`MkChar 97 p` isn't the literal `'a'` (whose proof is `rfl`). Stitchwort has
worked around both: `[auto]` arguments in the `Int` lemmas, and an
elaborator pass (`canonical`, commit `55c48eb`) for character patterns.

**Recommendation: option D1, "ignore proofs when comparing".** When the
kernel compares two values and reaches an argument or constructor field that
the declaration says is a proof (its type is in `Prop`), it skips it. Nothing
new is *computed*: the evaluator is untouched, `J` still only computes on
`rfl`, and a `case` on a proof still needs a constructor. This is a narrow
form of what Lean does for all of `Prop`, using the "relevance marks" idea
from Rocq's `SProp` (read the binder's sort, don't infer types during
comparison). It fixes all three programs in §2, needs no change to JS
extraction, erasure or hashing, and keeps type checking terminating, because
comparison only does less work than before.

It deliberately doesn't add Lean's "K-like" rule (transport computes along
*any* proof of `a = a`), because with an impredicative `Prop` that rule is
known to give terms whose checking never finishes (Abel and Coquand 2020,
§5.2). It also doesn't try to be complete: Lean's full rule is known to make
type checking undecidable (Carneiro 2019, §5.1), and Stitchwort's `Prop`
admits the same counterexample (§5.1, a program accepted today).

Stage 1 is a small kernel change plus the matching change in
the elaborator's unifier and the reference evaluator; stage 2 removes the
elaborator workarounds.

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
(prelude, line 304). *Definitional* proof irrelevance means the checker
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

**Normalisation.** Every term computes to a final form (a *normal form*) in
finitely many steps. Stitchwort's checker compares types by computing both
to normal form and comparing the results (DESIGN §6 "Running vs comparing"),
so if some terms have no normal form, comparison can loop.

**Transitivity.** If `a ≡ b` and `b ≡ c` then `a ≡ c`. A checker whose
equality isn't transitive surprises users: two steps that each check can
fail when combined.

**Erasure versus irrelevance.** These are different questions:

| | Erasure | Irrelevance |
|---|---|---|
| Question | Does it exist when the program *runs*? | Does the *checker* look at it when comparing? |
| Stitchwort today | Proofs and types are erased (DESIGN §6) | Nothing is irrelevant |
| Idris 2 | Quantity `0` arguments are erased, but still compared by the checker **[checked: I1, for erasure; unverified for comparison]** | |
| Agda | `@0` erases; `.x` makes an argument irrelevant **[checked: A2]** | |

Types are erased in Stitchwort but must stay *relevant*: `Vec Nat 3` and
`Vec Bool 3` differ only in a type argument. So whatever is built here must
key on "is a proof", never on "is erased".

**Axiom K, UIP.** *UIP* ("uniqueness of identity proofs") is propositional
proof irrelevance for equations: any two proofs of `a = b` are equal. *Axiom
K* is an equivalent eliminator. Both are incompatible with homotopy type
theory's univalence, which is why Agda and Rocq care about avoiding them.
Stitchwort has no univalence and no plans for it, and definitional proof
irrelevance for `Prop` implies UIP, so this is no cost here **[inferred]**.

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
`p` and transports back along `Bool.uniqueEq`. That commit added about 190 lines to the
elaborator, and it only works because `Bool`'s equality proofs are
provably unique. Examples: `examples/accept/char-pattern-proofs.sw`.

With proof irrelevance, all three are `rfl` and `canonical` can go.

## 3. How Stitchwort handles proofs today

The relevant parts of the kernel (`crates/core/src`), checked by reading:

- **Comparison is untyped.** `value::conv` (`value.rs:1164`) compares two
  values by their shapes, without knowing their types: constructors by
  index and fields (`value.rs:1275`), data types by parameters (`:1268`),
  stuck computations (`Neutral`) by head and arguments (`:1291`, with
  `spine_pairs` at `:1331`). A value doesn't record its type: a lambda has
  no domain, a constructor value no parameters (`value.rs:20-40`).
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
- **The elaborator's unifier** (`crates/elab/src/unify.rs`) mirrors `conv`'s
  structure, and solves metavariables.
- **A reference evaluator** (`reference.rs`, test only) has its own `conv`,
  kept in step for differential tests.

## 4. How other systems do it

### 4.1 Lean 4: all of `Prop`, checked by type

- Definitional equality has proof irrelevance for every `Prop`, and "is
  reflexive and symmetric, but not transitive" **[checked: L3]**.
- The kernel's check (`is_def_eq_proof_irrel`): infer the type of `t`; if it
  is a proposition, infer the type of `s` and compare the two types
  **[checked: L1, type_checker.cpp:895-903]**. It runs after cheap checks
  and *before* unfolding definitions (`:1159`, before
  `lazy_delta_reduction`), so proofs are never unfolded to compare them
  **[checked: L1]**.
- **K-like reduction.** For an inductive proposition with one constructor
  and no fields beyond its parameters (equality is the main example), the
  recursor computes even when the proof isn't a constructor:
  `to_cnstr_when_K` infers the major premise's type and, if its indices match
  the constructor's, replaces the proof by the constructor (for `e : a = a`,
  by `Eq.refl a`) **[checked: L2, inductive.h:27-50; L5]**. So in Lean,
  transport along any proof of `a = a` computes.
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
  into anything; combined with impredicative `Prop` it "breaks termination
  of reduction" **[checked: R1]**.
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
  Prop. 4.4]**. This is the trick option D1 borrows.
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
  not inferred from a type, which is close to option D1.
- Known soundness bugs: irrelevant record fields gave a proof of `⊥` in
  Agda 2.5.3 (issue #2170), by matching on an irrelevant field
  **[checked: G §1, appendix B]**; and #8699 (§5.4).

### 4.4 Idris 2

Quantity `0` means "erased at run time", and such variables can still be
"reasoned about in types" **[checked: I1]**. Whether the checker skips them
when comparing: not stated there **[unverified]**; I believe it doesn't,
i.e. Idris 2 has erasure without irrelevance.

### 4.5 Summary

| | Which proofs are equal | Large elimination | Transport on non-`rfl` proofs | Checking decidable | Normalising |
|---|---|---|---|---|---|
| Lean 4 | All of `Prop` | Subsingletons, incl. `Acc` | Yes (K-like) | No (in theory); kernel is a decidable approximation | No (§5.2) |
| Rocq `SProp` | All of `SProp` | Only empty types | No (unless Definitional UIP) | Yes (proved) | Yes, without Definitional UIP |
| Agda `--prop` | All of `Prop` | Only `()` | No | Yes **[inferred from G]** | Yes **[inferred]** |
| Agda `.x` | Arguments marked `.` | No matching | n/a | Yes | Yes |
| Stitchwort today | None | Subsingletons (Lean's rule) | No | Budgeted | Assumed |
| **Option D1** | **Proof positions of definitions, constructors, data types** | **Unchanged** | **No** | **As today** | **As today** |

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
decidable part it implements.

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

### 5.3 Singleton types and extensionality (Gilbert et al.)

If a proposition that carries data (like `{ b : A | a = b }`) could be
eliminated into data, irrelevance would turn every propositional equality
into a definitional one, which is undecidable **[checked: G §2.2]**.
Stitchwort's `E-PROP-ELIM` already refuses this (`∃` can't produce data,
DESIGN §6), and option D1 doesn't touch it. But it's the reason the
elimination rule and the irrelevance rule must be designed together: **every
proposition that can be eliminated into data must really have at most one
proof in the model** **[inferred]**.

### 5.4 Termination through irrelevant parts (Agda #8699)

Agda's termination checker treated a dot pattern's irrelevant argument as
structurally smaller, while conversion never looked at it, so `f` reduced to
itself and proved `⊥` under `--safe`; the `Prop` variant failed the same way;
fixed in PR #8707, 29 August 2026 **[checked: A3]**. The lesson recorded in
docs/proposals/mutual-recursion.md §6.7: descent must only use parts that
really exist in the values the evaluator computes with.

For Stitchwort with D1: descent evidence is still read from real matches on
variables (no dot patterns, no indices, no forced patterns); the evaluator
still computes with proof terms, and only *comparison* skips them; the
termination checker never calls `conv` (§3). So the #8699 mechanism has
nothing to act on **[inferred]**. That's an argument, not a proof, so §8 has
tests for it, and the note in mutual-recursion.md §6.7 should be updated to
point here.

### 5.5 Irrelevant data (Agda #2170)

Agda's bug came from making a *data* field irrelevant and then matching on
it **[checked: G appendix B]**. D1 only ignores proofs, never data, and
matching on proofs is still governed by `E-PROP-ELIM`. Must keep: never use
`field_erased` (which includes types) where `field_sorts == Prop` is meant.

### 5.6 What "sound" requires here

Two things **[inferred]**:

1. **A model where proofs are all equal.** Interpret each proposition as a
   set with at most one element (as in Carneiro's model of Lean). Every
   equation D1 adds then holds in the model, so D1 can't prove anything
   false *provided* Stitchwort's existing rules hold in such a model. They
   are a subset of Lean's (impredicative `Prop`, subsingleton elimination,
   `J`), plus things checked against their definitions (natives, compact
   text) and things justified separately (size-change termination, handler
   termination: DESIGN §13 "Known gaps"). Nothing in Stitchwort today
   distinguishes two proofs of one proposition except computation, which is
   exactly what the model forgets.
2. **Each skip compares two proofs of the same proposition.** The two
   values being compared have the same head (definition, constructor or data
   type), so the position's declared type is the same telescope entry,
   instantiated with the earlier arguments. If the comparison as a whole
   succeeds, those earlier arguments are equal (or are themselves proofs),
   so the two propositions are equal in the model. And because every type
   has exactly one sort (no cumulativity, no universe polymorphism, §3), "the
   declared type is in `Prop`" means the argument really is a proof whatever
   the instantiation. If Stitchwort ever adds cumulativity or universe
   polymorphism, this must be revisited (Rocq forbids `SProp` cumulativity
   for the same reason, §4.2).

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
- *Kernel:* the same position machinery as D1, plus a check of the
  proposition's shape. So it's no simpler than D1.
- *Verdict:* the safety is real but D1's argument (§5.6) is not much weaker,
  and B leaves the motivating example unsolved.

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
  `Prop`; positions still need marks (as D1).
- *Verdict:* the most principled, but it splits the logic, which goes
  against "propositions are types" being one simple story (DESIGN §6), and
  the effort lands on users.

### Option D: Lean-style, for all of `Prop`

Two levels:

**D1 (recommended): ignore proofs at known proof positions, compute nothing
new.** When `conv` compares two values with the same head, it skips the
arguments whose declared type is in `Prop`: a definition's parameters, a
constructor's fields, a data type's parameters. Plus: `rfl` proves `p = q`
whenever `p` and `q` are proofs. Nothing else changes.

- *Gains:* §2.1, §2.2 and §2.3 all become `rfl`; `canonical` and the second
  `[auto]` proofs in the `Int` lemmas become unnecessary; equal records with
  different proof fields are equal (`MkSortedList xs p ≡ MkSortedList xs q`,
  docs/proposals/records.md R7).
- *Not gained:* proofs inside a *local variable's* arguments (`f x p` where
  `f` is a hypothesis: `conv` doesn't know `f`'s type), and anything needing
  computation on a non-canonical proof (`J … h` with `h : a = a` still
  stuck; `steps l 0` still stuck). Stage 3 (§9) can add the first.
- *Kernel:* §7.
- *Soundness:* §5.6. *Decidability:* the evaluator is unchanged, and `conv`
  only compares less, so checking terminates whenever it does today. The
  relation the kernel decides, "normal forms are equal except at proof
  positions", is an equivalence relation on normal forms **[inferred]**, so
  it's *more* predictable than Lean's in one respect: it doesn't fail
  transitivity the way §5.1 describes, because it never equates an
  unreduced term with a reduced one (the price is the same incompleteness:
  `steps l 0` and `steps (MkLoop (Loop.inv l)) 0` stay different).
- *Hashing, JS, erasure:* unchanged (§7.6).

**D2 (not recommended): full Lean.** Typed comparison (infer the type of any
two values being compared, and if it's a proposition, stop), plus K-like
computation for `J`.

- *Gains over D1:* local-variable positions, top-level proofs anywhere, and
  transport along any proof of `a = a` computes.
- *Kernel:* `conv` would need the type of every value it compares, but
  values don't carry types (lambdas have no domain, constructors no
  parameters), so this is a rewrite of `conv` and the unifier, or a parallel
  type-inference for values.
- *Soundness:* as D1 (Lean's model). *Decidability:* the Abel–Coquand term
  (§5.2) loops; Carneiro's argument (§5.1) applies.
- *Verdict:* the gains are rare in Stitchwort's programs so far, and the
  costs are exactly the known pitfalls.

### Comparison

| | A | B | C | **D1** | D2 |
|---|---|---|---|---|---|
| §2.1 divisor | by hand | no | with new types | **yes** | yes |
| §2.2, §2.3 chars | elaborator | yes | with new types | **yes** | yes |
| New kernel code | 1 constant | ~D1 | new sort + rules | **masks + skips** | typed `conv` + K |
| Termination of checking | as today | as today | as today | **as today** | lost (§5.2) |
| Users' mental model | "use `proofIrrel`" | "Bool equations only" | two logics | **"proofs never matter for equality, but still compute"** | "proofs never matter" (mostly) |
| JS / erasure | unchanged | unchanged | `SProp` erased too | **unchanged** | unchanged |

## 7. The recommended design in detail

### 7.1 The rule

> **Proof positions.** A *proof position* is: parameter `i` of a definition
> whose type's `i`-th domain is in `Prop`; field `i` of a constructor whose
> `field_sorts[i]` is `Prop`; parameter `i` of a data type whose declared
> type is in `Prop`. When comparing two values with the same head, arguments
> at proof positions are equal without being compared.
>
> **Proofs of equations between proofs.** `rfl : p = q` checks whenever the
> equation's type is in `Prop`.
>
> Nothing else: evaluation, `J` and `case` are unchanged.

In docs/core.md, "There's no definitional proof irrelevance" (line 121)
becomes this rule, with the sentence: "Proofs are ignored when comparing, but
still used when computing: `J` needs `rfl`, and a `case` on a proof needs a
constructor."

### 7.2 Where `conv` changes (`crates/core/src/value.rs`)

- **`Data` against `Data`** (`:1268`): skip `a1[i]`/`a2[i]` where the data
  type's parameter `i` is a proof position.
- **`Ctor` against `Ctor`** (`:1275`): skip field `i` where
  `g.data(d).ctors[c].field_sorts[i] == Sort::Prop`. **Not**
  `field_erased`.
- **`Neutral` against `Neutral`, same `Def` head** (`:1291`, `spine_pairs`
  at `:1331`): skip `Elim::App` arguments at the definition's proof
  positions. `Elim::J` entries are compared as now (motive and base are
  relevant; the proof is the head, which is compared already). Both branches
  of that arm (fully applied, and the partially applied/eta one) use the
  same pairs, so both get the skip.
- **`Var` heads**: unchanged in stage 1 (no type information).
- **Compact text** (`Chars`): nothing to do. A range against a constructor
  is expanded one cell to `MkChar c rfl`, whose `valid` field is then
  skipped; the comment at `:1220` ("equal only if `h` and `rfl` are")
  changes.
- **`reference.rs` `conv`**: the same change, independently written, so the
  differential tests still mean something.

### 7.3 Deciding "is this a proof position?" cheaply

Like Rocq's relevance marks (§4.2), but read from what the kernel already
computes when it checks declarations, so no new syntax and nothing the
elaborator can get wrong:

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
  `declare_data`.

Cost: one pass over each signature at declaration; then a bit lookup per
argument compared. Comparison does strictly less work than today
**[inferred]**; worth confirming with `bench` (§9).

### 7.4 `rfl` on equations between proofs (`check.rs:411`)

In `(Term::Refl, Value::Eq(ty, a, b))`, accept without `conv(a, b)` when
`sort_of(cx, ty) == Sort::Prop`. `sort_of` is already there (`check.rs:489`).
This makes `theorem pi (p q : P) : p = q := rfl` check, which gives users
propositional irrelevance for free (so option A's `proofIrrel` isn't needed).

### 7.5 The unifier (`crates/elab/src/unify.rs`)

The elaborator must agree, or it rejects §2.1 before the kernel sees it (the
`E-REFL` in §2.1 may come from either). At a proof position:

- if one side is an unsolved metavariable applied to variables, solve it as
  now (any proof will do, and this keeps implicit proof arguments working);
- otherwise succeed without comparing.

The positions are the same masks (they're in `Globals`). The unifier
already mirrors `conv` (`unify.rs:118` for constructors, `:137`, `:183`,
`:194` for spines). Unsolved proof metavariables are still reported as they
are today, and the kernel re-checks the result anyway.

### 7.6 What doesn't change

- **Evaluation**: no new reduction, so programs, tests and natives behave
  exactly as before. The erasure rules (`erase.rs`) and JS extraction
  already ignore proofs at runtime; irrelevance is about checking only.
- **Termination checking**: untouched (§5.4).
- **`E-PROP-ELIM`**: untouched. It's what keeps §5.3 away.
- **Hashes**: no elaborated term changes in stage 1, so no hash changes. In
  stage 2, removing `canonical` changes the elaborated terms (and hashes) of
  definitions with char-pattern arms that mention the character; that's
  allowed (hashes aren't a constraint yet, TODO.md).
- **Caches**: the kernel only accepts more than before; every cache key
  includes the compiler version or source fingerprint (DESIGN §11), so no
  old rejection is reused.

### 7.7 Hashing: should a proof's body affect a hash?

**Yes, still** (no change proposed). A theorem's hash covers its body
(DESIGN §11), and so do the hashes of everything that uses it. One could
argue that with irrelevance a dependent can't observe the body, so its hash
needn't change when a proof is rewritten. That's false under D1: a proof can
still *compute* inside a dependent's check (`J` on `myLemma x` computes if
`myLemma x` evaluates to `rfl`; a `case` on a `Loop`-like proof computes on
its constructor), so changing a proof's body can change whether a dependent
checks **[inferred]**. What *is* true: a proof's body can never change a
test's result, because proofs are erased when running (`erase.rs`). So a
later optimisation could leave theorem bodies out of the *test-result* cache
key. Not proposed here.

Separately, two definitionally equal terms can have different hashes (they
already can: `2 + 2` and `4`). Hashes identify terms, not meanings, so that's
fine.

### 7.8 `auto` and `Decidable` (multi-file note §4.9.4)

Multi-file §4.9.4 says the decision procedure `auto` picks is visible to
proofs, citing `aoc/day02.sw:337-344` (`decIsTrue` exists so that `if IsTrue
c` uses the same procedure as `if lo <= hi`). **D1 doesn't change that
case**: a `Decidable p` is data (it lives in `Type`, DESIGN §6), so
`Bool.decTrue c` and `Bool.decEq c True` stay different, and an `if` that
computes with one doesn't match the other **[inferred]**.

It does change the other half: for an `[auto ok : p]` *proof* argument,
which candidate found the proof becomes invisible to comparison (that's
§2.1). So §4.9.4's point 1 shrinks to "the *procedure* is visible where it's
run as data (`if`, `==`)", and the order rules there stay as they are.

### 7.9 What users will still hit

"Proofs are ignored when comparing, but still used when computing." So these
remain:

- `J P d h` with `h : a = a` a variable or a lemma call: stuck (no K-like
  rule, deliberately: §5.2).
- A function that matches a proof to produce data (`steps`, or `pick` on
  `And`) is stuck on a non-constructor proof.
- Proof arguments of local function variables are compared (until stage 3).

The `E-REFL`/`E-TYPE-MISMATCH` message could add a note when the two sides
print the same, saying they differ in a part the printer hides; that's a
small independent improvement.

## 8. Tests

Per the soundness policy (DESIGN §13), each must-reject test has a nearby
accepted one, and declares its error code.

| # | Must be rejected | Code | Why it matters | Paired accepted example |
|---|---|---|---|---|
| 1 | `rfl : MkTBox Nat = MkTBox Bool` for `type TBox : Type 1 = MkTBox (t : Type)` | `E-REFL` | A type field is erased but relevant: catches `field_erased` used for `field_sorts` | `rfl : MkChar 97 p = 'a'` (§2.2) |
| 2 | `rfl : choose Nat n = choose Bool n`, for `choose : Type -> Nat -> Nat` stuck on `n` | `E-REFL` | The same for definition parameters (`erase::of_def` marks types) | `sameMod` (§2.1) |
| 3 | `rfl : Sorted [1, 2] = Sorted [2, 1]`, for a test-defined `type Sorted (xs : List Nat) : Prop` | `E-REFL` | Data parameters that are data stay relevant | A data type with a proof parameter, two different proofs, `rfl` |
| 4 | With a test-defined `type Exists (p : Nat -> Prop) : Prop = MkEx (x : Nat) (h : p x)`: `def leak (e : Exists (\n => n = n)) : Nat` matching out the witness | `E-PROP-ELIM` | Irrelevance must not leak a proof's data (§5.3) | `rfl : MkEx 1 rfl = MkEx 2 rfl` (two proofs of one `Exists` are now equal) |
| 5 | `J (\y e => P y) d h = d` for a variable `h : n = n` | `E-REFL` | No K-like rule (§5.2) | `J (\y e => P y) d rfl = d`; and `omegaUnfolds` (§5.2) checks within the default budget |
| 6 | `rfl : f = g` for two different `f g : Unit -> {IO} Unit` | `E-REFL` | Effectful functions are data, never proofs | `rfl : p = q` for `p q : Unit` (the `Prop`) |
| 7 | Agda #8699's shape adapted: a recursive call whose argument is smaller only inside a proof field that comparison ignores | `E-TERMINATION` | §5.4 | Structural recursion on a real proof field (`Loop -> Void`, `f (MkLoop n) = f n`) |
| 8 | `rfl : x = y` for two different variables `x y : Nat` inside a record with a proof field | `E-REFL` | Skipping the proof must not skip its neighbours | `rfl : MkSortedList xs p = MkSortedList xs q` for a test-defined record with a proof field |

Must not hang: `steps l 0 = steps (MkLoop (Loop.inv l)) 0` is rejected
promptly (`E-REFL`), documenting the incompleteness of §5.1.

Also:

- **Mutation tests**: skipping nothing must fail the accepted tests;
  skipping erased positions (types too) must fail tests 1–2; skipping every
  argument must fail tests 3, 6 and 8.
- **Differential**: `value::conv` against `reference::conv` on the kernel
  test programs, as for the evaluator.
- **Unifier**: an implicit proof argument solved only by unification still
  gets solved.
- **Regression**: `examples/accept/char-pattern-proofs.sw` checks with and
  without `canonical` (stage 2 removes it).

## 9. Stages

1. **Kernel and unifier** (Sonnet, from this note): the masks (§7.3), the
   `conv` skips (§7.2), the `rfl` rule (§7.4), the reference `conv`, the
   unifier (§7.5), the tests in §8, docs/core.md and DESIGN §6 line 459
   ("isn't needed for the POC" becomes the rule), the pointer in
   mutual-recursion.md §6.7. Bench comparison before and after.
2. **Remove workarounds** (Sonnet or DeepSeek): delete `canonical`
   (`elab/src/lib.rs:2370` and its caller) and check char-pattern proofs
   still pass; optionally simplify `Char.mkExt` and the second `[auto]`
   proofs of `Int.modNatToInt`, `Int.toIntDiv`, `Int.toIntMod`; update
   hash snapshots.
3. **Later, if a program needs it**: local variables' proof positions.
   `conv` would take the context's types (the checker has them) and read the
   variable's type as a telescope; variables bound inside the comparison
   (under a lambda) have no known type and stay relevant. Equations at
   proof types inside `conv` (`Eq(T, …)` with `T` visibly a proposition).
4. **Not planned**: K-like `J`, eta for proofs of single-constructor
   propositions in `case` (Lean doesn't do it either, §4.1), `SProp`.

## 10. Questions for Matt

1. **Adopt D1** ("proofs are ignored when comparing, but still used when
   computing")? *Recommendation: yes.*
2. **No K-like rule**: transport along a proof that isn't literally `rfl`
   stays stuck, accepting that this is less than Lean gives, to keep
   checking terminating (§5.2). *Recommendation: yes.*
3. **Remove `canonical`** once D1 is in (stage 2), changing hashes of
   definitions with char-pattern arms. *Recommendation: yes.*
4. **Local variables' proof arguments** (stage 3): build only when a
   program needs it? *Recommendation: yes, wait.*
5. **Hashes keep proof bodies** (§7.7), with theorem bodies possibly left
   out of the test-result key later. *Recommendation: keep as is for now.*

## 11. Questions for the reviewer

1. **The model (§5.6).** Is there anything in Stitchwort that distinguishes
   two proofs of one proposition, other than computation, which would break
   the "every proposition has at most one element" model? Candidates:
   natives returning proofs, compact text's `rfl`s, `NumCase`, record
   validators, `Effect.Comp` translations, `Partial`.
2. **Sort uniqueness (§3, §5.6).** The argument needs every type to have one
   sort. Is there cumulativity hidden anywhere (`fits_in`, `let`, the
   elaborator's universe handling) that would let a position typed `a :
   Type` hold a proof, or a position typed in `Prop` hold data?
3. **Same-type precondition.** `conv` is untyped. Are there call sites where
   the two values could have different types, so that skipping a position
   compares proofs of *different* propositions (`native.rs:253`,
   `partial.rs:350`, `canonical`, the unifier)? Same head is the guard; is it
   enough when a constructor value doesn't record its data type's
   parameters?
4. **Transitivity claim (§6, D1).** Is "normal forms equal except at proof
   positions" really an equivalence relation alongside the existing eta
   rules (`push_eta`, lambda against neutral)?
5. **Termination (§5.4).** Is the argument that #8699 can't arise
   convincing, and is test 7 a faithful adaptation?
6. **Literature.** Are the summaries in §4 and §5 accurate, especially the
   Lean kernel reading (K-like reduction, no structure eta for `Prop`) and
   the claim that Abel–Coquand needs the K-like rule?
7. **Unifier rule (§7.5).** Is "solve if one side is a metavariable,
   otherwise skip" safe against solving a metavariable with a proof that
   mentions out-of-scope variables (the existing scope check applies, I
   believe)?

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
- Experiments in §2 and §5 used the release build of `80c87a8`; the
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
- **[L5]** *Type Checking in Lean 4*, "Definitional equality" and
  "Reduction".
  <https://ammkrn.github.io/type_checking_in_lean4/type_checking/definitional_equality.html>
- **[AC]** Andreas Abel and Thierry Coquand, "Failure of Normalization in
  Impredicative Type Theory with Proof-Irrelevant Propositional Equality",
  LMCS 16(2), 2020. <https://arxiv.org/abs/1911.08174>
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
  constructor arguments of dot patterns", closed 29 August 2026 by PR #8707.
  <https://github.com/agda/agda/issues/8699>
- **[I1]** Idris 2 documentation, "Multiplicities".
  <https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html>
