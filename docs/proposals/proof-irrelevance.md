# Proposal: treating two proofs of the same fact as equal (proof irrelevance)

**Status:** Draft 5, 4 November 2026. Design only: nothing is built. Drafts 1,
2 and 4 each had an independent review; the responses are in
[Appendix A](#appendix-a-response-to-the-draft-1-review),
[Appendix B](#appendix-b-response-to-the-draft-2-review) and
[Appendix C](#appendix-c-response-to-the-draft-4-review). The draft 2 review's
verdict was "adopt D1′ with changes"; draft 3 made them, and Matt adopted D1′
(§10). Draft 4 fixed a problem found since: glued calls (SW-257) compare two
calls by their arguments before unfolding, and with D1′'s masks that shortcut
would equate things unfolding doesn't (§5.1, §5.7). Matt's D2349 restricts
the masks on definitions; draft 4 specified that, and found that constructor
masks need a matching change in the shortcut (§7.2, §7.10). D2352 to D2355
were decided as recommended. Draft 5 integrates the draft 4 review
(`proof-irrelevance-review.md`) and D1980, and settles the open stage 1
details. **Stage 1 (SW-93) can start from this draft with no further design
decision**; §10 lists the decisions draft 5 made and marks the ones users
would notice.

This note can be read without knowing type theory. §1 explains the words it
needs, with Stitchwort examples. Claims about Stitchwort were checked against
the source at commit `80c87a8` (draft 1), `69dd68a` (draft 2) and `bc89481`
(draft 3). `crates/core/src` and `crates/elab/src` are unchanged across the
three apart from `pretty.rs` and the prelude, which lost four lines after
line 231 (prelude line numbers below are as of `bc89481`); other line numbers
hold for all three. **Draft 4** was checked at `f3769d45`. The code has moved
a lot since `bc89481` (`value.rs`'s `conv` is now at line 2266, and the
prelude became `crates/elab/src/std`), so line numbers in text new in draft 4
are as of `f3769d45`, and older ones are left as they were: they locate the
code as it was when draft 3 was reviewed, and stage 1 has to find the current
places anyway. Programs marked **[run]** were run with a release build of the
CLI on 19 October 2026 (draft 3's at `bc89481`) or, for draft 4, on 4
November 2026 at `f3769d45` (files kept outside the repository). New Stitchwort code in draft 3 uses the new house style
(`(x: Nat)`); older blocks are left as they were. Labels:

- **[checked: S]**: read in source S (listed in [Sources](#sources)), or in
  the Stitchwort source at the `file:line` given;
- **[run]**: a Stitchwort program run as described;
- **[inferred]**: my reasoning from checked facts, not stated in a source;
- **[unverified]**: believed, but not confirmed.

**Draft 5** was checked at `f4674240f` (the draft 4 review's commit); line
numbers in text new in draft 5 are as of that commit, and its **[run]**
programs were run on 4 November 2026 with the release CLI of the main
checkout (`a5fd63861`), files kept outside the repository.

## Changes in draft 5

1. **D1980 is step 0 of stage 1** (§7.11, §9). Before any mask lands,
   `E-PROP-ELIM` gets Lean's condition: a proposition whose constructor has a
   field mentioning the proposition itself can't be matched to produce data.
   `Loop` and `steps` (§5.1) are then refused, so Carneiro's construction has
   no starting point in Stitchwort. Tests 18 and 21 are rewritten with a
   non-recursive proposition, `Tok`; the `Loop`/`steps` program becomes the
   must-reject test 26. Tests 7 and 14 keep `Loop`: they eliminate it into
   proofs, which stays allowed.
2. **Masks stop at the definition's arity, not its type's telescope** (§7.2,
   §7.3). `def g (n: Nat): 0 = 0 → Bool` whose body binds only `n` would
   otherwise get a vacuously inert position 1, and `g n rfl ≡ g n h` would hold
   while `g 0 rfl` computes to `True` and `g 0 h` doesn't. Test 24.
3. **The complete list of places that need the shortcut mode** (§7.2): three
   more in the kernel (the tree memo, hidden opaque calls, the reference
   evaluator's own shortcuts and memo), four more in the unifier (folded
   dictionaries, partial applications, calls blocked on a metavariable, hidden
   opaque calls). The mode is a parameter of each nested comparison, not of
   each pair. Tests 25, 28, 29 and two unit tests.
4. **A new finding: comparing two definitions by their case trees broke
   transitivity** (§7.2, §7.10). `Void.absurd (p rfl)` and `myAbsurd (q rfl)`
   are compared by their trees, which compares the stuck scrutinees `p rfl`
   and `q rfl` (**[run]**: rejected today), while each is equal to the same
   call with the other proof by its inert mask. Fix: two trees stuck on a
   `case` with no possible branch on either side are equal without comparing
   the scrutinees. Test 27.
5. **Index unification** (§7.12): deletion runs before injectivity, so the
   masks reach index unification. The review thought the other order would be
   unsound; it would only be less complete, because injectivity never takes a
   proof apart (Appendix C). Proof-typed *indices* of data types aren't
   masked in stage 1. Test 30.
6. **Stage 1 details settled** (§7.3): the marks are set with the body in
   `install_group`, on both the checked and the trusted (check cache) paths,
   so the cache format doesn't change; a definition with no body has no marks;
   natives must not read inert positions (a unit test); the reference
   evaluator reads the marks but checks them with an independent one-pass
   validator; a mark computation that runs out of budget gives no marks.
7. **§7.10 restated** as a logical relation (related closures applied to
   related arguments give related results), with clause 1 meaning "inside an
   inert argument of *any* enclosing call", and with the case-tree comparison
   added to the transitivity argument (§6).
8. **Tests and done criteria** (§8, §9): 30 tests; the random property tests
   are replaced in stage 1 by an enumerated test over a fixed signature
   (generated values aren't available); a depth-24 test of `CallMemo` with two
   modes; stage 1's done criteria and bench threshold.
9. **Smaller**: §3 updated for indexed families; §0 and §7.3 say the
   shortcut falls back no more often than *today*; §7.1 clause 2 names a
   `let`'s and an `Ann`'s type (kernel lambdas have no domain); D1981 (record
   eta needs a non-proof field) carried in §7.6 and §9; §10 and §11 brought up
   to date; Appendix C.

## Changes in draft 4 (since draft 3)

1. **The problem: glued calls.** Since draft 3 the kernel and the elaborator
   compare two glued calls of the same definition by their arguments first,
   and unfold only if those differ (SW-257, docs/core.md "Glued calls",
   `value.rs:2401` `conv_step`). Draft 3's §6 claimed D1′ "never equates an
   unreduced term with a reduced one". With masks applied to those
   arguments, it would: `steps l 0` and `steps (MkLoop (Loop.inv l)) 0`
   become equal (the `Loop` argument is skipped, `0 = 0`), while the second
   unfolds to `steps (Loop.inv l) 1`, which differs from `steps l 0`. That
   is Carneiro's non-transitivity (§3.1.1 of L4), and with it his
   subject-reduction failure (§3.1.2). The everyday shape is a transport:
   `cast a a rfl x` and `cast a a h x` would be equal by the shortcut, yet
   the first computes to `x` and `x` isn't `cast a a h x`. Not unsound (the
   relation stays inside the proof-irrelevant model), but gluing would stop
   being an optimisation: the same comparison would get different answers
   with gluing on and off. §5.1, §5.7, §6 corrected.
2. **Masks on a definition's arguments only for *inert* proof parameters**
   (Matt's D2349): a proof parameter the definition never computes with.
   §7.1 states it, §7.3 says how it's computed (one flag per parameter,
   from the checked body, a greatest fixed point over a recursion group).
   Working it out sharpened D2349 in three places, each a question for Matt
   (§10): a `case` with no possible branch (`Void.absurd`) doesn't count as
   computing (D2353; without this `Int.modNat`, §2.1's own example, loses
   its mask); passing the proof on is allowed only to another inert
   parameter, not into a constructor field (D2354); and calls of local
   function variables keep their arguments relevant, as in draft 3.
3. **New finding: constructor masks break the shortcut too.**
   `Box.unbox (MkBox p)` and `Box.unbox (MkBox q)` would be equal by the
   shortcut (the boxes are equal by the field mask), yet they compute to `p`
   and `q`, which differ. D2349 doesn't touch this: `Box.unbox` has no proof
   parameter. So the shortcut compares arguments with the constructor masks
   off and the inert masks on (§7.2, D2352). With both changes, a shortcut's
   "equal" implies that the unfoldings are equal, so gluing is again a pure
   optimisation (§7.10, an argument by induction on evaluation, not a
   proof), and the masked relation is transitive on values of one type
   (§6). Constructor masks still don't survive substitution, which is the
   §5.7 gap, now its only source.
4. **§5.6 rests on Carneiro's ideal/algorithmic split**: his Lemma 3.4(3)
   (algorithmic equality of two terms of one type implies ideal equality)
   and his model (§6) cover D1′'s comparison for the rules Stitchwort shares
   with Lean, given §7.4's same-type invariant; Stitchwort's extra rules
   still need their own arguments. His §4.1 split of ideal equality into
   reduction and proof irrelevance (`κ` and `≡p`) shows which side D1′ is
   on: Stitchwort has no type-directed reduction like his `K+`, so D1′ only
   adds to the comparison side.
5. **Which std definitions lose masks** (§7.3): none of the motivating ones
   (`Nat.mod`, `Nat.div`, `Int.modNat` and the other `Int` divisions,
   `Fin.ofNatLt`, the fuel proof of `decreasing`), given D2353. Losing:
   `List.chunksOfPositive`'s `pos` (it reaches a `decreasing` proof, an
   argument of the local `%rec`), `Float.make`'s `p` and
   `Map.Raw.fromSorted`'s `sorted` (into a record's proof field, D2354),
   and theorems that take a hypothesis apart. What that costs is small:
   those definitions always unfold or sit in proof positions (§7.3).
6. **Tests** (§8): 17 to 23, comparing the `cast`, `Loop` and `Box.unbox`
   shapes with gluing on and off and the shortcut disabled, `Int.modNat`'s
   mask still applying, and must-rejects for non-inert parameters (a
   one-branch `case`, a group, a stored proof). Mutation tests for the
   shortcut's mode.
7. **Smaller**: Stitchwort refuses a quotient of a proposition
   (`E-UNIVERSE` **[run]**), which removes Carneiro's second source of
   non-transitivity (§5.1); the masks stay out of hashes, as erasure flags
   do (§7.7); §0, §1, §2.4, §4.5's row, §9, §10 and §12 updated.

## Changes in draft 3 (since draft 2)

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
- [Appendix C: response to the draft 4 review](#appendix-c-response-to-the-draft-4-review)

## 0. Summary

Today the kernel compares two proofs the same way it compares data: they're
equal only if they compute to the same thing. So `x % 100` with a
hand-written proof that `100 != 0` and `x % 100` with `auto`'s proof have
different types that print the same, and a hand-built character
`MkChar 97 p` isn't the literal `'a'` (whose proof is `rfl`). Stitchwort has
worked around both: `[auto]` arguments in the `Int` lemmas, and an
elaborator pass (`canonical`, commit `55c48eb`) for character patterns.

**Recommendation: option D1′, "skip proof positions when comparing".** When
the kernel compares two values with the same head and reaches a constructor
field that the declaration says is a proof (its declared type is in
`Prop`), or a definition's proof argument that the definition never
computes with (an *inert* parameter, D2349), it skips it. Comparing two
calls by their arguments before unfolding them (the glued-call shortcut)
skips only the inert arguments, not proof fields, so that it never says
"equal" where unfolding wouldn't (§7.2, §7.10). Nothing new is *computed*:
the evaluator is untouched, `J` still only computes on `rfl`, a `case` on a
proof still needs a constructor, and `rfl` is still checked only by
comparison. It uses the "relevance marks" idea from Rocq's `SProp` (read the
binder's declared sort, don't infer types during comparison). It fixes all
three programs in §2, needs no change to JS extraction, erasure or hashing,
and comparison does no more work than today: the shortcut falls back to
unfolding no more often than it does now, and only more often than draft 3
would have (§7.3).

What it is, honestly: a *sound but incomplete* version of the proof
irrelevance Lean has. D1′ is enough to *derive* that every two proofs of a
proposition are equal (as a theorem) and to write a computing K by hand
(§5.7), although its comparison recognises irrelevance only at proof
positions of definitions, constructors and data types, not for two bare
proof variables `p` and `q`. Because of the gap, a well-typed term can
compute to one the checker would reject at the same type (§5.7). Assuming
the model argument of §5.6 (Carneiro's for Lean: an equality checked between
two terms of one type lies inside the ideal equality his model validates),
that can make elaboration or checking fail (or
run into the budget), but doesn't by itself let a false term through; Lean
has a gap of the same kind for other reasons (§5.1). With the inert rule
the gap has one source, constructor fields; the masked comparison is
transitive on values of one type, and the same with gluing on or off (§6,
§7.10). The cost of the inert rule: whether `f p` and `f q` are equal
depends on `f`'s body, and `cast a a rfl x` and `cast a a h x` stay
different, as today.

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
checking undecidable (Carneiro 2019, §5.1). Stitchwort's `Prop` admits the
same counterexample today (§5.1, a program accepted today); stage 1 removes
it first, by refusing to match a self-referential proposition into data
(D1980, §7.11).

Stage 1 is that refusal, then a kernel change (the masks, the inert
analysis, the skips and the shortcut's mode) plus the matching change in the
elaborator's unifier and the reference evaluator; stage 2 removes the
elaborator workarounds. Matt adopted D1′ on 19 October and restricted it
with D2349 on 4 November; D2352 to D2355 were decided as recommended, and
draft 5 settles the rest (§10).

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

**Glued calls and the shortcut** (new in draft 4). While checking, a
definition applied to all its arguments is kept as a *call*, `f a b`, and
unfolded only when something looks inside it (docs/core.md "Glued calls").
Two calls of the same definition are compared by their arguments first:
same definition, equal arguments, so equal results. Only if the arguments
differ are the unfoldings compared. That is an optimisation only if
"arguments equal" really implies "unfoldings equal" for the relation being
used; §7.10 is about keeping it so.

**Inert parameter** (new in draft 4). A proof parameter of a definition that
the definition never computes with: its body doesn't take it apart, use it
as `J`'s proof, apply it, return it or store it, and only passes it on to
inert parameters of other definitions (§7.3). Changing an inert argument
can never change what a call computes to, except inside other inert
arguments, which is what makes it safe to skip in every comparison.

**Subject reduction.** "Computing doesn't change a term's type": if the
checker accepts `t : T` and `t` computes to `t'`, the checker also accepts
`t' : T`. Example: it accepts `(x => x) 3 : Nat`, and also `3 : Nat`. When
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

  *Draft 4.* With gluing on, each side is first a call,
  `Call(Int.modNat, [x, 100, ok])`; the shortcut compares the arguments
  (§7.2), and position 2 is skipped because `ok` is inert in `Int.modNat`.
  Its body (`std/Int/Basics.sw:27-30`) uses `ok` only in
  `| x, Zero => Void.absurd (ok rfl)`, inside the argument of
  `Void.absurd`, whose parameter is inert because its `case` has no
  branch (D2353, §7.3) **[checked: the source]**. With gluing off, the
  call unfolds, takes the `Succ` branch for 100, sticks on `x` and stays
  folded with its original spine, as above; the same mask applies. Without
  D2353's clause, `ok` would not be inert and §2.1 would stay `E-REFL`.
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
- **Data types have parameters and indices** (*draft 5*; draft 3 said "no
  indices", which is no longer true: docs/core.md "Unifying indices"). A
  `case` on an indexed family unifies indices, and a branch whose indices
  conflict is impossible and has no body. Lean's `Acc` can now be declared,
  but matching it into data is `E-PROP-ELIM`, because its field `x` is data
  (docs/core.md, D140) **[run]**. Index unification never takes a proof
  apart: an equation between two proofs is stuck, never a conflict
  (`unify_index.rs:238-241`, D137, `examples/soundness/index-proof-conflict.sw`).
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
| **Option D1′** | **Derivable as a theorem: all of `Prop`. Seen by the checker: inert proof parameters of definitions, proof fields of constructors, proof parameters of data types** | **Unchanged** | **No rule; a user can write K by hand (§5.7)** | **Budgeted, as today** | **Evaluator unchanged; no non-normalising term known; unproved (§5.7)** |

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

**Closed by D1980 (new in draft 5).** Matt decided on 30 October to refuse
the construction at its root, as Lean now does (lean4#13851, and Gilbert et
al.'s guard, docs/research/kernel.md §5.1): a proposition may be matched to
produce data only if, besides today's conditions, no field of its
constructor mentions the proposition itself (§7.11). `steps` is then
`E-PROP-ELIM`. `Loop` itself stays legal, and so do `Loop.inv: Loop → Loop`
and recursion on it into proofs (`Loop → Void`): only *data* computed from a
self-referential proof is refused, and that is what Carneiro's argument
needs. So after stage 1's first step the program above is rejected, and the
paragraphs below about `steps` describe what the masks *would* do without
D1980; they stay because the glued-call problem they show isn't specific to
recursive propositions (`cast` and `Box.unbox`, §5.7, have it too), and the
inert rule and the shortcut mode are still needed.

**The same shape through glued calls (new in draft 4).** Carneiro's
algorithmic equality has a congruence rule for applications (two
applications are equal if their parts are) beside its reduction rule, and
no transitivity rule **[checked: L4 §2.3]**. So `f 0 a ⇔ f 0 (intro 0 (inv0
a))` holds by congruence and proof irrelevance, without reducing either
side, while the right side also reduces; that is where his
non-transitivity comes from. Since SW-257
Stitchwort's checker does the same with glued calls (§1, `value.rs:2401`).
Today the shortcut is harmless, because "equal arguments" means equal
values. With draft 3's masks it would not be, even without full
irrelevance:

- `steps l 0` against `steps (MkLoop (Loop.inv l)) 0`: both are calls of
  `steps`; position 0 has type `Loop: Prop`, so draft 3 masks it, and
  `0 = 0`, so the shortcut says "equal".
- With gluing off, the right side unfolds (its argument is a constructor) to
  `steps (Loop.inv l) 1`, and that differs from `steps l 0` in its second
  argument. Today's message says exactly this: "`steps l 0` and
  `steps (MkLoop (Loop.inv l)) 0` aren't equal; computing the right side
  gives `steps (Loop.inv l) 1`" **[run]**.
- So `steps l 0 ≡ steps (MkLoop (Loop.inv l)) 0` and
  `steps (MkLoop (Loop.inv l)) 0 ⟶ steps (Loop.inv l) 1`, but
  `steps l 0 ≢ steps (Loop.inv l) 1`: Carneiro's §3.1.1 non-transitivity,
  with the "creative step" supplied by whoever wrote the middle term, and
  by §3.1.2 a failure of subject reduction **[inferred from the code at
  `f3769d45` and L4 §3.1.1-3.1.2]**.

Two things remove it, and since draft 5 a third removes the example itself
(D1980: `steps` is refused). `steps` computes with its `Loop` argument (it
takes it apart), so under D2349 that position isn't masked at all (§7.3).
And the shortcut never skips constructor proof fields (§7.2), which the
inert rule doesn't cover. Test 18 keeps the shape with a non-recursive
proposition, `tokNat t 0` against `tokNat MkTok 0` (`type Tok: Prop = |
MkTok`, `tokNat` matching on it): the same disagreement between the
shortcut and unfolding, without the recursion. §7.10 argues that the two together make the shortcut's
"equal" imply the unfoldings' "equal", so the problem can't come back in
another shape.

Carneiro names a second source of non-transitivity: a quotient of a
proposition, whose `lift` acts like a subsingleton eliminator
**[checked: L4 §3.1.1, last paragraph]**. Stitchwort refuses that quotient:
`Quot Unit R` with `Unit: Prop` is `E-UNIVERSE`, "the carrier of a quotient
must be a type in `Type`" **[run]**.

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
def delta : Top := z => z Top z
def omega : ((a : Prop) -> (b : Prop) -> a = b) -> Bot :=
  h a => J (y e => y) delta (h Top a)
def bigOmega : ((a : Prop) -> (b : Prop) -> a = b) -> Bot := h => delta (omega h)
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

**Carneiro's frame (new in draft 4).** Carneiro separates two relations:
the *ideal* definitional equality `≡`, a transitive congruence with β, δ,
ζ, ι, η and a rule that any two proofs of one proposition are equal; and
the *algorithmic* `⇔` that Lean actually checks, which "will imply `≡`" and
has no transitivity rule **[checked: L4 §2.2, §2.3]**. The bridge is his
Lemma 3.4(3): if `e : α`, `e' : α` and `e ⇔ e'`, then `e ≡ e'`; he notes
that the induction needs both sides to have the same type at the
application rule **[checked: L4 §3.2]**. His model (§6) interprets `≡`
soundly in ZFC with inaccessible cardinals, every proposition a set with at
most one element, and Corollary 6.8 concludes that no proof of `⊥` passes
the kernel "since algorithmic equality implies definitional equality"
**[checked: L4 §6, Corollary 6.8]**. That is the argument point 1 above
borrows, and it fixes what D1′ has to show:

- **D1′'s comparison is inside the ideal `≡`, given the same-type
  invariant.** Each skip compares two proofs of the same proposition
  (point 2, §7.4), an instance of the ideal proof-irrelevance rule; the
  rest of `conv` is structural comparison of values, which are reached by
  the reduction rules, plus η **[inferred]**. Lemma 3.4(3)'s
  same-type premise is exactly §7.4's invariant: that is why it matters for
  soundness and not just for the answer.
- **Lean's model covers the rules Stitchwort shares with Lean**: β, δ
  (unfolding), `let`, `case` on a constructor (ι), `J` on `rfl` (Eq's
  recursor), `Quot.lift` on `Quot.mk` (his ιq), impredicative `Prop` and
  subsingleton elimination **[inferred: the correspondence is mine]**.
- **Stitchwort's extra rules still need their own justification**, as
  point 1 says: `NumCase` and the natives (checked against their
  definitions), `+` on its second argument (docs/core.md; equations that
  are theorems, so they hold in any model of the theorems), compact text,
  the comparison of different definitions by their case trees (SW-386, a
  congruence for `case`), and the termination checks that make every
  definition denote a total function (size-change, handlers, `decreasing`).
  None of them looks at a proof, so none distinguishes two proofs the model
  identifies **[inferred]**.

Carneiro's §4.1 splits the ideal relation in two: a reduction `κ` (β, δ, ζ,
ι, ιq, and `K+`, which runs a subsingleton's recursor on *any* proof `h` by
replacing it with `intro inv[p, h]`, and so needs the context and types to
fire), and a relation `≡p` for proof irrelevance and η that "picks up the
pieces"; Church–Rosser holds for `κ` up to `≡p` **[checked: L4 §4.1,
Theorem 4.7]**. In those terms D1′ adds only to the `≡p` side: Stitchwort's
evaluator is untyped and has no `K+` (it computes on a proof only when the
proof is a constructor or `rfl`, §3), and D1′ leaves it so. That is the easy
side: no reduction depends on a type or on which proof was given, so the
evaluator's confluence is untouched **[inferred]**. Lean's difficulties
(undecidability, §5.1; Abel and Coquand's loop, §5.2) come from the `K+`
side and from comparing unreduced terms by congruence; draft 4's inert
rule and shortcut mode (§7.2, §7.10) keep Stitchwort away from the second.

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
  J (y e2 => f (Box.unbox y)) x e

theorem piViaBox (a : Prop) (p : a) (q : a) (e : MkBox p = MkBox q) : p = q :=
  J (y e2 => p = Box.unbox y) rfl e
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

**A second source, through glued calls (new in draft 4).** Draft 3 had only
the subject-reduction gap above, which needs a term to compute. The glued
shortcut (§1) adds a gap in *one* comparison: the answer would depend on
whether gluing is on. Two shapes, each rejected today with the message
shown **[run]**:

```
def cast (a: Type) (b: Type) (h: a = b) (x: a): b := J (y e => y) x h

theorem castRefl (a: Type) (h: a = a) (x: a): cast a a rfl x = cast a a h x := rfl
--  today: computing both sides gives `x` and `J (y e => y) x h`

theorem unboxBoth (a: Prop) (p: a) (q: a): Box.unbox (MkBox p) = Box.unbox (MkBox q) := rfl
--  today: computing both sides gives `p` and `q`
```

- **`cast`, a definition's mask.** Both sides are calls of `cast` (every
  definition applied to all its arguments glues, `value.rs:1715`). With
  draft 3's masks the shortcut skips position 2 (`a = b` is in `Prop`) and
  says "equal". Unglued, the sides are `x` and `J (y e => y) x h`, stuck on
  `h`: "different". Under D2349 `h` isn't inert (it's `J`'s proof), so the
  shortcut compares `rfl` with `h` and falls back to the unfoldings:
  "different" both ways.
- **`Box.unbox`, a constructor's mask.** Both sides are calls of
  `Box.unbox`, whose only explicit argument has type `Box a: Type`, so
  D2349 has nothing to restrict. But the shortcut compares `MkBox p` with
  `MkBox q`, and the constructor mask says "equal". Unglued, the sides
  compute to `p` and `q`: "different". This one needs the shortcut change
  of §7.2: the shortcut compares arguments with constructor masks off, so
  it falls back to the unfoldings, and the answer is "different" both ways
  **[inferred from the code at `f3769d45`]**.

Neither is unsound: `cast a a rfl x` and `cast a a h x`, and `p` and `q`,
are equal in the model. But a comparison whose answer depends on an
optimisation is a checker with two meanings, the problem draft 2 removed
from draft 1's `rfl` rule (§6, D1). After §7.2, §7.10 argues, the shortcut
says "equal" only where unfolding does.

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
      J (y e2 => p = Box.unbox y) rfl (boxEq a p q)

    def Loop.expose (l: Loop): Loop :=
      J (y e => Loop) (MkLoop (Loop.inv l)) (Prop.irrel Loop (MkLoop (Loop.inv l)) l)

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

**Where the gap comes from, after D2349 (new in draft 4).** A subject
reduction failure is a comparison that changes when a variable is replaced
by a value. Draft 3's definition masks had that problem of their own:
`steps l 0 ≡ steps l2 0` for two variables `l l2: Loop` (both stuck,
position 0 masked), but replacing `l2` by `MkLoop (Loop.inv l)` lets the
right side compute to `steps (Loop.inv l) 1`, which differs. An inert
parameter can't do that: the definition never computes with it, so
replacing it never lets a call step that couldn't before (§7.10). So the
gap now comes only from constructor fields: `g (MkBox p) n` and
`g (MkBox q) n`, stuck on `n`, are equal, and once `n` is known `g` may take
the box apart and use the proof where it's compared. The `castViaBox`
example above is of this kind **[inferred]**.

*Draft 5.* The draft 4 review found two more sources in draft 4's text, both
removed by spec changes, so "constructor fields are the only source" now
rests on the spec as written:

- *Positions beyond the arity.* Draft 4 took candidates from the type's
  telescope. A definition whose body binds fewer parameters than its type
  has arrows (`g (n: Nat): 0 = 0 → Bool`, computing the function by its case
  tree) would get a vacuously inert position the body never sees, and
  `g n rfl ≡ g n h` would stop holding once `n` is known (`g 0 rfl` computes
  to `True`, `g 0 h` is stuck on `h`). Fixed: candidates are positions below
  `Def::arity` (§7.3; test 24).
- *Hidden opaque calls.* Where an opaque `ou` is hidden, `ou (MkBox p)` is a
  neutral call that never unfolds; compared with every mask, it equals
  `ou (MkBox q)`, while where `ou := Box.unbox` is transparent the two
  compute to `p` and `q`. That is a judgement that stops holding when more is
  known, which opaque definitions are built to avoid (docs/core.md "Opaque
  definitions", rule 3). Fixed: a hidden call's arguments are compared in
  shortcut mode (§7.2; test 25), so being transparent only ever adds
  equalities, as today.

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
whose declared type is in `Prop`: a definition's *inert* parameters (D2349,
§7.3), a constructor's fields, a data type's parameters. The glued-call
shortcut skips only the inert parameters (§7.2). `rfl`, `J`, `case` and
evaluation are unchanged.

- *Gains:* §2.1, §2.2 and §2.3 all become `rfl` (§2.4); `canonical` and the
  second `[auto]` proofs in the `Int` lemmas become unnecessary; equal
  records with different proof fields are equal (`MkSortedList xs p ≡
  MkSortedList xs q`, docs/proposals/records.md R7); propositional proof
  irrelevance becomes a provable theorem (§5.7).
- *Not gained:* two bare proofs (`rfl : p = q` for variables `p q : a`, or
  `f p ≡ f q` with `f` a hypothesis: `conv` doesn't know their types),
  anything needing computation on a non-canonical proof (`J … h` with
  `h : a = a` a variable still stuck; `tokNat t 0` still stuck), and, since
  D2349, two calls of a definition that computes with its proof argument
  (`cast a a rfl x ≢ cast a a h x`; `tokNat t 0 ≢ tokNat t2 0`, §8 test 21). Stage 3 (§9)
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
  **[inferred; to be tested, §8]**. *Corrected in draft 4.* Draft 3 said it
  doesn't fail transitivity the way §5.1 describes "because it never
  equates an unreduced term with a reduced one". That stopped being true of
  `conv` once glued calls landed: the shortcut compares two calls, unreduced,
  by their arguments, and with draft 3's masks `steps l 0 ≡
  steps (MkLoop (Loop.inv l)) 0` while the right side reduces to something
  different (§5.1). What makes the claim true again is §7.10: with inert
  masks and the shortcut's constructor masks off, a shortcut's "equal"
  implies that the unfoldings are equal, so `conv` with gluing gives the
  same answers as `conv` comparing normal forms, and the masked relation on
  normal forms is transitive: masks are fixed by the head, so if `a` and
  `b` agree outside the masked positions, and `b` and `c` do, then `a` and
  `c` do **[inferred]**. That holds for argument masks and field masks
  alike. *Draft 5:* "fixed by the head" doesn't cover the comparison of two
  *different* definitions by their case trees (SW-386, `same_stuck_trees`),
  where the heads differ. It holds there too, once one gap is closed: a tree
  walk takes a `case` only on a non-inert parameter, so `F x p` and `F x q`
  walk the same branches, and the leaves are compared with the same masks.
  The gap was the `case` with no possible branch (D2353's clause 3), whose
  stuck scrutinee *is* compared by the tree walk today: `Void.absurd (p rfl)`
  and `myAbsurd (q rfl)` are compared through `p rfl` against `q rfl`, while
  `Void.absurd (p rfl) ≡ Void.absurd (q rfl)` by the inert mask. So
  `same_stuck_trees` must not compare the scrutinees of two `case`s that have
  no possible branch on either side (§7.2, test 27). The price is incompleteness: `tokNat t 0` and
  `tokNat MkTok 0` stay different, and so do `tokNat t 0` and `tokNat t2 0`
  (draft 4's `steps` examples are refused since D1980). It is *not* a congruence for computation: `MkBox p ≡ MkBox
  q`, yet `Box.unbox (MkBox p)` computes to `p`, `Box.unbox (MkBox q)` to
  `q`, and those differ (§5.7); inert argument masks *are*, which is the
  point of D2349. The claim is not made for values of different types:
  that's what §7.4 excludes.
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
| Users' mental model | "use `proofIrrel`" | "Bool equations only" | two logics | **"proofs in fields, and in arguments the function only passes along, never matter for equality, but still compute"** | "proofs never matter" (mostly) |
| JS / erasure | unchanged | unchanged | `SProp` erased too | **unchanged** | unchanged |

## 7. The recommended design in detail

### 7.1 The rule

> **Proof positions.** A *proof position* is: parameter `i` of a definition,
> with `i` below the definition's arity (the number of parameters its body
> binds, `Def::arity`), whose type's `i`-th domain is in `Prop` and which is
> *inert* (below); field `i` of a constructor whose `field_sorts[i]` is
> `Prop`; parameter `i` of a data type whose declared type is in `Prop` (a
> parameter, not an index: indices are always compared in stage 1, §7.12).
> When comparing two values of the same type with the same head, arguments
> at proof positions are equal without being compared.
>
> **Inert** (D2349, as sharpened in drafts 4 and 5). A definition's
> parameter `x` below its arity whose type is in `Prop` is inert if every
> occurrence of `x` in the definition's checked body is
>
> 1. inside an argument at an inert position of some enclosing call of a
>    definition (one of the call's leading arguments, as in §7.2), however
>    deeply: the walk doesn't look inside such an argument at all; or
> 2. inside a part of the term that values don't keep (a `let`'s type, an
>    `Ann`'s type: kernel lambdas have no domain, `term.rs:179`); or
> 3. the scrutinee of a `case` all of whose branches are impossible (no
>    body: `Void.absurd`, `Void.exfalso`), which never computes whatever its
>    scrutinee is (D2353).
>
> So a parameter isn't inert if the body takes it apart (`case` with a
> branch), uses it as `J`'s proof or in a quotient form, applies it,
> returns it, stores it in a constructor field (D2354), passes it to a
> local function variable, or mentions it in a type that survives into
> values (`J`'s motive, an equation's sides). Inertness is a greatest fixed
> point over a recursion group: a parameter passed only to itself in a
> recursive call is inert.
>
> **The shortcut.** Wherever two calls of the same definition are compared
> by their arguments before (or instead of) unfolding, or that can unfold
> later (a hidden opaque call, a call blocked on a metavariable: §7.2), the
> argument comparison skips inert positions but compares constructor proof
> fields, at every depth (D2352). Data types' proof parameters stay skipped:
> a type is never taken apart, so nothing computes with them. If that says
> "different", the calls are unfolded and compared with all the masks, as
> today (a hidden call, which can't be unfolded, is then different).
>
> **Case trees.** Two different definitions compared by their case trees
> (SW-386): two `case`s with no possible branch on either side are equal
> without comparing their scrutinees (draft 5, §7.2).
>
> Nothing else: evaluation, `rfl`, `J` and `case` are unchanged.

In docs/core.md, "There's no definitional proof irrelevance" (line 143 at
`f3769d45`) becomes this rule, with the sentences: "Proofs in constructor
fields, and proof arguments a definition only passes along, are ignored when
comparing, but still used when computing: `J` needs `rfl`, and a `case` on a
proof needs a constructor. A proof argument the definition computes with
(a `J` on it, a `match`) is compared, so `cast a a rfl x` and `cast a a h x`
differ. Two proof *variables* are still compared, so `rfl : p = q` needs `p`
and `q` to be the same." The "Glued calls" bullet gets the shortcut's rule.
And the precondition of §7.4 goes in `conv`'s doc comment.

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
  `inert_params[i]` is set (so `i` is below the arity; draft 4 said "within
  the telescope", which was wrong, §7.3). Entries at or beyond the arity
  apply the definition's *result* (`g n h` for `g` of arity 1, spine
  `[n, h]`, `value.rs:1652`) and are always compared. Once a `J`
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
- **`reference.rs` `conv`** (`:559` at `f4674240f`): the same change,
  independently written, so the differential tests still mean something. It
  reads the marks from `Globals` and checks them independently (§7.3).

**The shortcuts (draft 4; completed in draft 5).** A *shortcut* is any place
that answers "equal" for two calls of one definition from their arguments,
when the calls can still unfold: now (a glued or folded call), later in the
same elaboration (a call blocked on a metavariable), or where more is known
(a hidden opaque call). Each must compare the arguments in the **shortcut
mode**: inert positions skipped, data types' proof parameters skipped,
constructor proof fields compared. Every one of them
**[checked: the source at `f4674240f`]**:

| # | Where | What it compares |
|---|---|---|
| K1 | `value.rs:2409-2425`, `conv_step`, through `same_spines` (`:2374`) | two glued calls (`Value::Call`) of one definition; numbers reach it too, since `native::compare_lazily` hands their bases back to `conv` |
| K2 | `value.rs:2432-2445`, the `is_folded` arm (`:1790`) | definitions folded by name: dictionaries, theorems, `decreasing` definitions, `Quot.lift` leaves, `k * x` |
| K3 | `value.rs:2552`, `same_spines(…) \|\| push_eta(…)` in the `Neutral` arm | two partially applied definitions (functions: eta would unfold them once applied) |
| K4 | the `Neutral` arm, same `Def` head, when `hidden(g, f)` (`value.rs:1743`) | two hidden opaque calls: they never unfold here, but do where `f` is transparent (§5.7) |
| U1 | `unify.rs:983`, `same_arguments_solving_nothing` | two glued calls |
| U2 | `unify.rs:999-1004`, `same_arguments` | two folded dictionaries |
| U3 | `unify.rs:1185-1204`, `blocked(…)` | two calls stuck on a metavariable, which unfold once it's solved: in normal mode `g ?n (MkBox p)` and `g ?n (MkBox q)` would unify, and after `?n := 0` the kernel could reject what the elaborator accepted |
| U4 | `unify.rs:1205-1226`, "the spines, or else eta" | two partially applied definitions |
| U5 | the unifier's `Neutral` arm when the head is hidden | as K4 |
| R1-R3 | `reference.rs:562-569` (folded), `:650-652` (spines, or else eta), and its hidden calls (`reference.rs:252`) | as K2, K3, K4 |

And two memos must be keyed by the mode, because they remember an answer
that can differ between the modes:

- **`CallMemo`** (`value.rs:2335`, D483) remembers pairs of calls found
  *different*; a pair different in shortcut mode may be equal in normal
  mode. Its key gets the mode.
- **`TreeMemo`** (`value.rs:2858-2930`, SW-395) remembers pairs found
  *equal* by `same_stuck_trees`, for the whole of the outermost tree
  comparison, which can span nested comparisons in both modes. A pair found
  equal in normal mode must not be answered "equal" in shortcut mode, so
  `MemoKey` gets the mode. (A shortcut-mode "equal" would be safe to reuse in
  normal mode, since shortcut mode equates less; not worth the special
  case.) The reference evaluator's own record of equal calls
  (`EQUAL_CALLS`, `reference.rs:659-686`; its tree walk is `same_trees`, `:720`) gets the mode in its key too.

**How the mode is carried.** As a parameter of `conv_with` (and of
`unify`'s nested runs), not of each `ConvTask`: every place that switches to
shortcut mode already starts a nested comparison of its own (`same_spines`,
`same_arguments`, the blocked-call `nested(run)`), except K4 and U5, which
push a hidden call's argument pairs onto the current work list today and
must instead compare them in a nested comparison, as `same_spines` does.
Everything inside a nested comparison has its mode. `same_stuck_trees`'s callback passes on the
caller's mode, and so does `native::compare_lazily`'s, which pushes onto the
same work list. A comparison not inside a shortcut is in the normal mode.
Inside a shortcut, the nested calls and their fallback unfoldings stay in
shortcut mode (§7.10 needs `≈ᵢ` there). When a shortcut says "different",
the outer comparison goes on in its own mode: the calls are unfolded and
compared with every mask.

Places checked that need nothing: `same_closure` and `identical`
(`value.rs:3268-3330`), which test syntactic identity, stronger than either
mode; `meta_against_call` (`unify.rs`), which solves a metavariable with a
call rather than comparing two calls; index unification's deletion
(`unify_index.rs:184`), which compares two values in normal mode (§7.12).

**`set_shortcuts_disabled`** turns off only the glued-call shortcut and the
memos today; the folded-by-name one stays on (it is what keeps theorems
folded). The differential tests of §8 therefore compare glued against
unglued checking (`Globals::glue` off, as `STITCHWORT_GLUE=0` does in the
elaborator) as well as shortcuts on and off.

**Stuck calls** are different: a definition stuck on a `case` stays folded as
`Neutral(Def(f), spine)`, and two of those are compared by their spines with
every mask (`value.rs:2537-2553`), because nothing can unfold them within
this comparison. That isn't a shortcut, and it needs no mode: inert positions
are safe there for the reason of §7.10, and constructor fields are the §5.7
gap. (A refinement the draft 4 review suggested, not adopted for stage 1:
inside a stuck neutral's spine, shortcut mode could keep the field masks,
since nothing takes those fields apart during the comparison. It would make
D2352 cheaper; it isn't needed for correctness, and it adds a third state.)

**Case trees** (`same_stuck_trees`, `value.rs:2731`, used by `conv`, the
unifier and, as `same_trees`, the reference evaluator). Two *different*
definitions stuck on a `case` are compared by walking both trees: the stuck
scrutinees, then branch by branch. Today, two `case`s with no possible branch
on either side still compare their scrutinees (`value.rs:2773`):
`Void.absurd (p rfl) = myAbsurd (q rfl)` at `Nat`, for `def myAbsurd: Void →
Nat | ()`, is `E-REFL` **[run]**, while the same with `p` on both sides
checks **[run]**. With D2353's inert masks that breaks transitivity:
`Void.absurd (p rfl) ≡ Void.absurd (q rfl)` (mask) and
`Void.absurd (q rfl) ≡ myAbsurd (q rfl)` (trees), but not
`Void.absurd (p rfl) ≡ myAbsurd (q rfl)`. Stage 1 changes the walk: when both
sides are stuck on a `case` of the same data type and *every* branch on both
sides is impossible, the pair is equal and the scrutinees aren't compared.
Sound: a well-typed value whose `case` has no possible branch has an empty
type, so no environment reaches it and any two such stuck terms are equal in
the model **[inferred]**. It only accepts more, and it makes the tree walk
independent of inert arguments, which §7.10's transitivity step needs.

### 7.3 Deciding "is this a proof position?" cheaply

Like Rocq's relevance marks (§4.2), but read from what the kernel already
computes when it checks declarations, so no new syntax and nothing the
elaborator can get wrong. Positions count from the start of a `Def` spine
and stop at its first `J` entry (§7.2):

- **Constructors**: `field_sorts` exists (`globals.rs:117`).
- **Definitions** (draft 4, D2349): a new `inert_params: Box<[bool]>` on
  `Def`, set in two steps.
  1. *Candidates*: positions `i < Def::arity` whose domain in the checked
     signature (`check::telescope`) has `sort_of(dom) == Sort::Prop`. Not
     `erase::of_def`, which also marks types. `inert_params` has length
     `arity`. *Draft 5:* draft 4 took every position of the telescope, but
     the telescope peels every `Pi` of the type (`check.rs:3740-3757`), while
     the body binds only `arity` parameters (`globals.rs:38-44`, "the number
     of leading lambdas"). A definition whose result is a function computed by
     its case tree, `def g (n: Nat): 0 = 0 → Bool := match n with | Zero => h
     => J (y e => Bool) True h | Succ m => g m` (accepted today **[run]**),
     has arity 1; its position 1 would be a candidate the body never binds,
     so the walk would find it vacuously inert, and `g n rfl ≡ g n h` would
     hold while `g 0 rfl` computes to `True` and `g 0 h` is stuck (test 24).
  2. *Inert*, from the checked bodies, once per recursion group, where the
     bodies are installed (`check.rs` `install_group`, `:1694-1705`, beside
     `lift_leaf` and `recursive`, which are set from the body the same way): start with every
     candidate of every member marked, then repeatedly clear any marked
     parameter with an occurrence that §7.1's three clauses don't allow
     (clause 1 reads the marks of the group's members as they currently
     stand, and the final marks of earlier definitions), until nothing
     changes. That is the greatest fixed point, so a parameter passed only
     to itself, or around a cycle of members, stays inert. It needs one walk
     of each body per round, and each round clears at least one mark, so at
     most (candidates + 1) rounds; in practice one or two **[inferred]**.

  The walk is over the kernel's own terms, so it follows the case tree: a
  `Case(x, …)` on a candidate `x` with a branch clears it; a case on another
  variable doesn't, but the walk goes into every branch. The kernel's terms
  have `rfl`, `J` and the five quotient forms as term formers
  (docs/core.md), so "is `x` used as `J`'s proof" is a syntactic test, and
  an occurrence in any argument of a `Quot` form clears it (those forms are
  compared "structurally, every argument included", so nothing there is
  masked).

  While a group is being checked its own members have no marks (every
  argument compared, as today), in the kernel and in the elaborator; the
  marks exist once the group is admitted. That costs nothing that matters:
  the comparisons inside a definition's own body rarely compare two calls of
  that definition with different proofs, and if one does it fails as it
  does today. It also means the elaborator and the kernel agree without the
  elaborator computing the marks itself before the kernel has the bodies.
  (An implementation detail, decided in draft 4.)

  *Where they're computed (draft 5).* `install_group` is shared by
  `define_group` (checked) and `admit_trusted_group` (the check cache's
  replay, `check.rs:2690`), so the marks are recomputed on replay from the
  installed bodies, like `lift_leaf` and `recursive`. Nothing new is stored,
  and the check cache's format doesn't change. (Draft 4 said the cache
  "stores and replays them"; it doesn't store the erasure flags either:
  `erase::of_def` computes them on first use, `erase.rs:156`.) Recomputing
  is cheap (one telescope per member, a few walks per group) and keeps the
  marks out of the trust boundary: a stale or edited cache entry can't give
  a definition marks its body doesn't justify. If computing the candidates
  runs out of budget (the telescope evaluates the type), the group gets no
  marks: comparing every argument is always safe.

  *Definitions without a body.* A final definition always has a body
  (`globals.rs:33-36`); a pending or failed one has none, and gets no marks
  (every argument compared). So "bodiless declarations" need no rule of
  their own.

  *Natives.* A definition computed natively (`native::run`, and
  `float::run` for the `Float` operations) runs its implementation, not the
  body its marks come from. §7.10 needs that a native never reads an
  argument at an inert position. Today the only native with a proof
  parameter is `eqNatSound`, which reads only its two numbers
  (`Native::numbers`, `native.rs:113-120`). Stage 1 adds a unit test over
  every native and `Float` definition in std: each inert position is one
  the implementation doesn't read (for the `Native`s, a position at or
  beyond `numbers()`). A new native with a proof parameter then fails the
  test until its implementation is checked.

  *The reference evaluator.* It reads the marks from `Globals` rather than
  computing them again: a second fixed-point analysis would double the
  riskiest new code. What it adds instead is an independent one-pass
  **validator**, written separately from the analysis: for every marked
  parameter of every final definition, each occurrence in the body is one
  §7.1's clauses allow, given the final marks. That checks the direction
  soundness and §7.10 depend on (every mark is justified); it doesn't check
  that the fixed point is the greatest, which only affects what's accepted,
  and which the std listing (§8) checks. The validator runs over std and the
  test programs in a unit test, and on every admitted group in builds with
  the `reference` feature (every test build), not in release binaries.

  Like the erasure flags, the marks are a function of the checked
  definition, so they aren't hashed (§7.7). An *opaque* definition's marks come from its hidden
  body too: with marks from the signature alone, `f p ≡ f q` would hold
  where `f` is opaque and fail where it's unfolded, the same two-meanings
  problem as gluing. So an opaque body can change what checks outside it,
  through its marks, as it already can through a hash.
- **Data types**: `proof_params` from the checked parameter telescope, at
  `declare_data` (and the trusted path's `admit_trusted_data_decls`). A
  parameter `p : Prop` is *not* a proof position (`sort_of(Prop)` is
  `Type 0`); test 9 pins this. Only parameters: `Data(D, args)` holds the
  parameters and then the indices (docs/core.md), and the mask covers the
  first `params.len()` entries (§7.12).

Cost: one pass over each signature and a few passes over each group's
bodies when it's installed; then a bit lookup per argument compared.
Comparison does no more work than today: in shortcut mode the arguments are
compared as today, minus the inert ones, so the shortcut never falls back to
unfolding where it doesn't now. (It falls back more often than draft 3's
design would have: two calls whose arguments differ only in a constructor's
proof field, §7.2.) `CallMemo` keyed by mode can compare a pair once per
mode, at most twice where today it's once; test 29 pins that a deep chain
stays linear **[inferred]**. To be confirmed with `bench` (§9).

**What the motivating definitions get** **[checked: the std source at
`f3769d45`; the walk done by hand]**:

| Definition | Its proof parameter's uses | Inert? |
|---|---|---|
| `Nat.div` (`std/core/Division.sw:31`) | unused | yes |
| `Nat.mod` (`:37`) | at most in `n / divisor`'s `auto` proof, `Nat.div`'s inert `ok` | yes. `Nat.mod x 100 [ok := p] = Nat.mod x 100 [ok := q]` is accepted *today* **[run]**: the proof is gone once the calls unfold, so the mask only saves the unfolding |
| `Int.modNat` (`std/Int/Basics.sw:27`) | `Void.absurd (ok rfl)` in the `Zero` branch | yes, by D2353 (no otherwise) |
| `Int.div`, `Int.mod`, `Int.tdiv`, `Int.tmod`, `Int.fdiv`, `Int.fmod` | the same `Void.absurd (ok rfl)` | yes, by D2353 |
| `Nat.divMod`, `Nat.ceilDiv`, `Int.divMod` | passed to `/` and `%` | yes |
| `Fin.ofNatLt` (`std/Fin/Fin.sw:21`) | `Void.absurd (Bool.falseNotTrue h)`; itself, recursively | yes, by D2353 and the fixed point |
| `Fin.ofNat`, `Vec.getLt` | passed to `Fin.ofNatLt` | yes |
| `Mod.toFin` (`std/Mod/Mod.sw:196`) | into `Mod.ltOfNeZero … ok …` inside `Fin.ofNatLt`'s inert argument | yes (clause 1: the occurrence is inside an inert argument, whatever `Mod.ltOfNeZero` does) |
| `f.%go`, the fuel of every `decreasing` definition (docs/core.md "Recursion on a measure") | absurd at `Zero`; at `Succ`, into `f.%go`'s own `h` | yes, by D2353 and the fixed point **[inferred from the documented shape, not walked]** |
| `Mod.ofNat` (`std/Mod/Mod.sw:36`) | none: no proof parameter. Its `if h:` binds `h` in a lambda, and puts it in `isLt`, a constructor field | n/a; the field mask applies |
| `gcd.induct` / the `if h: b = 0` shape of function-equations.md | the refutation `h` passed as `%`'s `ok` | yes (`Nat.mod`'s `ok`); `Nat.gcd`'s own `[decreasing := …]` goes to `%rec` (below), which `f.unfold` drops anyway |
| D2180's `if h: i < n then Some (Fin.ofNatLt n i h)` | the equation needs `Fin.ofNatLt n i h' ≡ Fin.ofNatLt n i h` | yes, as above |
| characters (`MkChar n p`) | a constructor field | unchanged |

**Which std definitions lose their masks**, from a search of std's `def`s
with a proof-typed binder (`grep` for binders whose type has `<`, `≤`, `≠`,
`=` or `∈`, then each read) and of every `def` body using `J` or `rewrite`
**[checked; the search can miss binders of other proposition types]**:

- `List.chunksOfPositive`'s `pos` (`std/List/Toolkit.sw:551`): it goes into
  `[decreasing := List.dropConsLess ys n y pos]`, an argument of `%rec`, a
  local function variable, whose arguments are all compared (until
  stage 3). Two calls with different `pos` proofs, stuck on the list, stay
  different. The function computes with the list, so it's stuck only on an
  unknown list.
- `Float.make`'s `p` (`std/Float/Float.sw:51`) and
  `Map.Raw.fromSorted`'s `sorted` (`std/Map/Spec.sw:1419`): each goes into
  a record's proof field, through a definition that returns it
  (`Bool.canonicalTrue`'s `| False, p => p`, `Float.sw:45-47`) or stores it
  (`Map.Tree.buildWithin`'s `Both Trivial asc`, `Spec.sw:1366`), so neither
  occurrence is inside an inert argument, and under D2354 a constructor
  field isn't an allowed place. It costs nothing in practice: neither has a
  `case`, so a call always unfolds at once to the record, where the field
  mask applies; the mask would only have helped the shortcut, which then
  falls back to unfolding. (`Bool.canonicalTrue` exists to make `Float`
  records with known bits equal whatever their proof, D731; the field mask
  does that by itself, so it's a stage 2 candidate for removal.)
- The two `def`s using `J` (`List.decCons`, `Pair.decMk`,
  `std/core/ListOptionPair.sw`) use it on proofs bound by patterns, not on
  parameters: no change.
- **Theorems.** A theorem whose proof takes a hypothesis apart, rewrites
  along it, returns it or applies it outside an absurd branch loses that
  parameter's mask, which is most theorems with hypotheses. Those whose
  hypotheses only feed recursive calls and absurd branches keep them
  (`Nat.leTrans`, `std/core/Division.sw`, by the same clauses as
  `Fin.ofNatLt`). The cost: a theorem call compared at a *relevant*
  position with two different hypothesis proofs, for example as the proof
  of two `J`s (`J P d (lemma x h1)` against `J P d (lemma x h2)`), stays
  different, as today. A theorem call in a proof position (the common case:
  an argument to an inert parameter, a constructor field) is skipped
  whole, so its own marks don't matter there.

Apart from `Void.absurd` and `Void.exfalso` (`std/core/Logic.sw:34`, `:39`),
whose `case` has no branch, I found no `def` in std that cases on, or uses
as `J`'s proof, one of its own proof parameters, so the losses above come
from the clauses about returning, local functions and constructor fields,
not from D2349's core **[checked, with the same caveat]**. Stage 1 should print the list the
analysis actually computes for std (a debug listing of every candidate it
clears, and why), and compare it with this one.

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
tests; `reference.rs`'s calls are its own recursion; refreshed in stage 1
at `6650398f6`, when the elaborator had grown from four callers to about
twenty-five) **[checked]**. Most compare types, whose own type is a sort
(see above):

- *Types:* `core/check.rs:541` (inferred against expected), `core/native.rs:372-374, 463, 520`,
  `core/nat_add.rs:259`, `core/float.rs:714`, `core/partial.rs:419` (declared
  types against expected shapes); `elab/cases.rs:673, 685, 912, 1018, 1034,
  1037` (a hypothesis's type against a goal or a fact); `elab/derive.rs:191`,
  `elab/congruence.rs:547`, `elab/shared.rs:177`, `elab/dot.rs:263`,
  `elab/lib.rs:2095`, `elab/partial.rs:735`, `elab/interfaces.rs:762, 1253`
  (interfaces' first arguments, which are types; both only choose a
  diagnostic).

The ones that compare other values:

| Call site | Compares | Same type? |
|---|---|---|
| `core/check.rs:474` | each result index of a constructor against the expected type's, in order, stopping at the first that differs | yes: index `k`'s type depends only on the parameters and the earlier indices, all equal by then |
| `core/check.rs:507` | the two sides of an expected `Eq(ty, a, b)`, for `rfl` | yes: both `: ty` |
| `core/unify_index.rs:178, 184` | binder types, then the two sides of a constraint, the sides only when their types agree (`:178` stops it otherwise) | yes |
| `core/pretty.rs:1551` | a written decision against the computed one, for display only | yes: the same proposition's proofs |
| `core/value.rs:2451, 2652` | recursive, inside `conv` | inherited |
| `elab/check.rs:659, 667` (`conv_now`) | its callers' pairs: `elab/cases.rs:653, 1013`, the two sides of an `Eq` | yes |
| `elab/cases.rs:886` | a constructor equation's fields, pairwise, without stopping at the first difference | yes: a field whose type mentions an earlier field is skipped before `conv` (`mentions_fields`, the `||` before it), so each pair compared has the field's type at the one set of parameters (the equation is at one type, not an indexed family) |
| `elab/data_auto.rs:211` | a data type's arguments, pairwise, not stopping at a difference | not always: a later parameter's type can depend on an earlier differing one; harmless, as it only words the note of an `E-TYPE-MISMATCH` already reported |
| `elab/interfaces.rs:690` | the instance written against the one found for the same goal | yes: both `: goal` |
| `elab/ring.rs:947`, `elab/omega.rs:2099` | an atom against the atoms seen, of the same carrier | yes: the carrier is checked first (`a.sort`, `a.int`) |
| `elab/omega.rs:236`, `elab/lib.rs:4154`, `elab/counterexample/inputs.rs:453` | the two sides of an `Eq` | yes |
| `elab/derive_induct.rs:2580` | two predicates' parameters and indices, pairwise, stopping at the first that differs | yes |
| `elab/partial.rs:785-786` | the members' rows: `ops` and `res`, arguments 0 and 1 of the same `Comp`/`Delay` type | yes: same telescope positions **[inferred]** |
| `elab/unify.rs:864` | the known part of a sum against a number | yes: both `Nat` |

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
types could differ, except `elab/data_auto.rs:211`, which only words a
note.

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
(`unify.rs:1083`, `:1090`, spines through `spine_pairs` at `:1313`, at
`f4674240f`; draft 3's numbers were `:111`, `:118`, `:219`):

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

**The unifier's shortcut mode** (draft 5). At the shortcut sites U1 to U5
of §7.2 the unifier works in shortcut mode, like the kernel: inert positions
follow the two rules above, data types' proof parameters too, and
constructor proof fields are unified as today (so a metavariable inside one
can be solved there, as today, because the kernel's shortcut compares that
field too). U3 matters most: a call blocked on a metavariable is a call that
will unfold, and unifying it in normal mode would accept `g ?n (MkBox p)`
against `g ?n (MkBox q)` for a `g` that, once `?n := 0`, unboxes; the kernel
would then reject the elaborated term (test 28). The mode is carried as in
the kernel: a parameter of the nested runs (`same_arguments`, `nested(run)`,
the `same_stuck_trees` callback), and part of `TreeMemo`'s key.

`same_arguments_solving_nothing` (U1) keeps its rule: if unifying the
arguments solves anything, the calls are compared by their unfoldings
instead, with nothing solved. With masks, `Nat.div m d ?ok` against
`Nat.div m d p` solves `?ok := p` at the inert position (the whole-argument
rule), so U1 undoes it and falls back, exactly as today (`unify.rs:1270-1277`
describes this case) **[checked]**.

### 7.6 What doesn't change

- **Evaluation**: no new reduction, so programs, tests and natives behave
  exactly as before. The erasure rules (`erase.rs`) and JS extraction
  already ignore proofs at runtime; irrelevance is about checking only.
- **`rfl`** (`check.rs:411`): still checks only by `conv`.
- **Termination checking**: untouched (§5.4).
- **`E-PROP-ELIM`**: unchanged by the masks; it's what keeps §5.3 away.
  *Draft 5:* it gains one condition in stage 1's first step (D1980, §7.11),
  which only refuses.
- **Caches**: the kernel accepts more than before, and since D1980 refuses a
  little more; every cache key includes the compiler version or source
  fingerprint (DESIGN §11), so no old answer is reused. The check cache's
  format is unchanged: the marks are recomputed on replay (§7.3).
- **Record eta** (D1981, Matt, 30 October; docs/research/kernel.md §5.2):
  not stage 1 work, but a constraint on it. Once proof fields are masked, a
  record whose fields are all proofs behaves like a unit type, and eta on it
  breaks transitivity of an untyped `conv` (`x ≡ MkR x.h ≡ MkR y.h ≡ y`
  without `x ≡ y`). So record eta, if it lands (SW-55, SW-789), must be
  limited to records with at least one field that isn't a proof (Rocq's
  rule); records.md §7.1's condition 4 should say so. Stage 1 adds the
  sentence to docs/core.md next to the masks.

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

**The inert marks (draft 4)** aren't hashed: they are computed from the
checked body, which the hash already covers, as the erasure flags are. Since
they depend on bodies, they are one more way a theorem's body reaches its
dependents (rewriting a lemma so that it takes a hypothesis apart clears a
mark), which is one more reason to keep proof bodies in hashes. JS and
erasure don't use them.

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

"Proofs in fields, and in arguments a function only passes along, are
ignored when comparing, but still used when computing." So these remain:

- Two calls of a function that computes with its proof argument, with
  different proofs: compared. `cast a a rfl x` and `cast a a h x` differ,
  and so do `tokNat t 0` and `tokNat t2 0` (§8 test 21). Whether a function's proof
  argument counts depends on its body, which a user can't see in its
  signature; `stitchwort doc` (or hover) should say which proof parameters
  are ignored, and the `E-REFL` note could name the one that differs. New in
  draft 4 (D2349).

- `rfl : p = q` for two different proof variables: rejected. Prove it
  through a box as in §5.7 (`piViaBox a p q rfl`), or wait for stage 3. A
  prelude `Prop.irrel` is deferred (§10 question 2). If it's ever added, its
  documentation must say that it computes: `J … (Prop.irrel p q)` reduces
  when `p` and `q` are any proofs, which is surprising.
- `J P d h` with `h : a = a` a variable or a lemma call: stuck (no K-like
  rule, deliberately: §5.2).
- A function that matches a proof to produce data (`tokNat`, or `pick` on
  `And`) is stuck on a non-constructor proof.
- A proposition with a field holding a proof of itself (`Loop`) can't be
  matched to produce data at all (D1980, §7.11), only other proofs.
- Proof arguments of local function variables are compared (until stage 3).
- Rarely, a value that computed from a transport along a hand-made `rfl` is
  rejected at the type of the expression it came from (§5.7).

The `E-REFL`/`E-TYPE-MISMATCH` message could add a note when the two sides
print the same, saying they differ in a part the printer hides; that's a
small independent improvement.

### 7.10 Why gluing stays an optimisation (new in draft 4)

The goal: `conv` gives the same answer with gluing on and off (up to the
budget). That holds if every shortcut's "equal" implies that unfolding
would also say "equal": a shortcut's "different" falls back to unfolding
anyway, and `CallMemo` only ever answers "different" for a pair already
found different in the same mode, and `TreeMemo` only answers "equal" for a
pair already found equal in the same mode (§7.2). "Every shortcut" means
every site in §7.2's table; draft 4 listed four of them, and the argument
covered only those. This is an argument, not a proof **[inferred]**; tests
17 to 19, 24, 25 and 27 check it on the shapes that break it.

Write `≈` for the normal mode's relation on values (every mask: inert
arguments, constructor proof fields, data types' proof parameters, plus
eta), and `≈ᵢ` for the shortcut mode's (the same, except constructor proof
fields are compared). `≈ᵢ` skips less, so `a ≈ᵢ b` implies `a ≈ b`.

**Claim.** Take a definition `f`, and two lists of arguments that are `≈ᵢ`
at every non-inert position and anything (of the right type) at the inert
ones. Then `f`'s unfoldings on them are `≈ᵢ`.

**Why.** Strictly, the claim is about a relation, not single values: it is
a *logical relation* argument. The lambda and call steps below use that
`≈ᵢ` is closed under application: closures that are `≈ᵢ` (at a fresh
variable), applied to `≈ᵢ` arguments, give `≈ᵢ` results. That is itself
part of what's proved, by induction on the length of the evaluation, which
is finite because the kernel's termination checks make every definition
total. It goes through because `≈ᵢ`'s only skips are inert arguments (the
subject of the claim) and data types' proof parameters (types are never
taken apart). The steps, with the second environment differing from the
first only as allowed:

- *An inert parameter is never looked at.* By §7.1's clauses, each of its
  occurrences is inside an argument at an inert position of some enclosing
  call (however deep: `Fin.ofNatLt`'s `Void.absurd (Bool.falseNotTrue h)`
  relies on the outer call, not on `Bool.falseNotTrue`), in a type
  annotation that values don't keep, or the scrutinee of a `case` with no
  branch. The first kind may evaluate to different things on the two
  sides, but only inside inert arguments, which the relation skips; the
  second disappears; the third is stuck on both sides.
- *A call `g …`* gets `≈ᵢ` arguments at `g`'s non-inert positions (by
  induction) and possibly different ones at its inert positions. If it
  stays a call or gets stuck, the two results are `≈ᵢ` because `g`'s inert
  positions are skipped. If it unfolds, the claim for `g` applies (a
  shorter evaluation; for a recursion group this is where the greatest
  fixed point is used: each member's inert parameters were checked assuming
  the others').
- *A `case` on a non-inert variable* sees `≈ᵢ` values: both the same
  constructor with `≈ᵢ` fields, *all* fields, so both take the same branch
  with `≈ᵢ` fields bound; or both stuck. This is the step that needs the
  constructor masks off. With them on, `MkBox p` and `MkBox q` would be
  related, `Box.unbox` would take its branch on both and bind `p` and `q`,
  and the results would be unrelated: §5.7's `Box.unbox` example.
- *`J`*: its proof contains no inert variable outside inert arguments, so
  the two proofs are `≈ᵢ`, and one is `rfl` exactly when the other is; the
  motive and base are `≈ᵢ`. *`Quot.lift` on `Quot.mk`*, natives on numbers
  and text, `NumCase`, and `+`'s rules all decide from values on which `≈ᵢ`
  is equality, or structural.
- *A constructor* gets `≈ᵢ` fields: an inert variable can't be a field
  (D2354). That's the step that needs D2354: with `wrap p := MkBox p`
  allowed, `wrap p ≈ᵢ wrap q` by the mask, but their unfoldings `MkBox p`
  and `MkBox q` aren't `≈ᵢ`, and `Box.unbox (wrap p)` against
  `Box.unbox (wrap q)` is the `Box.unbox` example again.
- *A lambda* gives closures that are `≈ᵢ` at a fresh variable, by induction
  under the binder; *`let`* evaluates its value and goes on with the body.

**So:** if a shortcut finds the arguments `≈ᵢ` (which is what shortcut mode
checks), the unfoldings are `≈ᵢ`, hence `≈`, and unfolding would have said
"equal". The nested comparisons inside a shortcut must stay in shortcut mode
(§7.2) because the claim's premise is `≈ᵢ`, not `≈`.

**What else follows.**

- *Transitivity.* With the shortcuts implied by unfolding, `conv` answers
  as a comparison of normal forms by `≈` would, and `≈` on normal forms is
  transitive on values of one type (masks are fixed by the head; eta as
  today), for argument and field masks alike **[inferred; the property test
  of §8]**.
- *Substitution.* The claim's environments can be any values, so replacing
  a variable in two calls related through an inert argument keeps them
  related: inert masks don't cause subject-reduction failures. Field masks
  do (§5.7), and that is now the only source.
- *Stuck calls* (`Neutral(Def(f), spine)`) compared with every mask are
  safe for inert positions by the same claim: if a later substitution lets
  them unfold, the unfoldings are related. *Hidden opaque calls* are
  compared in shortcut mode (K4), so where the definition is transparent the
  claim applies and the unfoldings are related: transparency only adds
  equalities. *Natives* satisfy the call step only because they never read an
  inert position (§7.3, a unit test).
- *Case trees* (draft 5). Comparing two different definitions by their case
  trees doesn't depend on their inert arguments: a tree takes a `case` only
  on a non-inert parameter, except a `case` with no possible branch, whose
  scrutinee the walk no longer compares (§7.2), and the leaves are compared
  with the same masks. So `F x p ≡ G y r` by trees and `F x p ≡ F x q` by the
  mask give `F x q ≡ G y r`, which the transitivity bullet above needs.
- *The elaborator.* The argument is for the kernel's `conv`, which has no
  metavariables. The unifier's shortcuts (U1 to U5, including calls blocked
  on a metavariable) use the same mode, so that it never solves or accepts
  more than the kernel will; that it agrees is tested (§8, tests 17 to 19
  run through the elaborator and test 28), not argued.

**What it doesn't cover**: termination (a fallback unfolding is the same
work as with gluing off, so no worse than today) and the budget (the
shortcut fires less often, so a check near the budget may need more steps
than before; `bench`, §9).

### 7.11 Step 0: no self-referential proposition into data (D1980, new in draft 5)

Matt's D1980 (30 October 2026, on SW-93): refuse matching a self-referential
proposition to produce data, as part of SW-93, measuring first that nothing
relies on it. It lands as the first commit on SW-93's branch, before any
mask, so that no build of Stitchwort ever has both the masks and `steps`.

**The rule.** `E-PROP-ELIM`'s subsingleton condition (`check.rs:930-937` at
`f4674240f`: alone in its group, no nested field, at most one constructor,
every field a proof) gets a fifth part: **no field type of the constructor
mentions the data type itself**. "Mentions" is syntactic, on the checked
field types (`Term::Data(d, …)` for the same `d` anywhere in the field's
type, including under arrows: `(y: Nat) → r y x → Acc r y` mentions `Acc`).
Nested occurrences (`P ∧ Unit` inside `P`) are refused already by the
nested-field condition (`examples/soundness/nested-prop-elim.sw`). A `case`
whose every branch is impossible still produces anything
(`every_branch_impossible`), since it never computes.

**What stays allowed.** Declaring `Loop`, and matching it into proofs:
`Loop.inv: Loop → Loop`, structural recursion `Loop → Void` (tests 7 and
14). Self-referential propositions with several constructors were refused
already (at most one constructor).

**The message.** The existing `E-PROP-ELIM` error, with a note for the new
case: "`Loop` is a proposition, so its proofs are erased at runtime. Its
field `next` holds a proof of `Loop` itself, and matching on such a proof can
only produce another proof: otherwise checking whether two of its uses are
equal could go on forever." The documentation (docs/core.md's `E-PROP-ELIM`
paragraph, DESIGN §6) gets the condition.

**Measuring first.** A `grep` of the `.sw` files in std, `examples/`,
`aoc/` and `games/` for `Prop` types found no single-constructor proposition
with a field mentioning itself except `examples/accept/nested-data-shapes.sw`'s
`P` (nested, matched into a proof only) **[checked: `grep` for `type … :
Prop`, then each read; it can miss headers split over lines]**. The
measurement that counts is the rule itself: with it in, std builds,
`examples/` passes, and `stitchwort check` on `aoc/` and `games/rogue`
reports no `E-PROP-ELIM`. If anything does rely on it, stop and report
before going on: that is a decision for Matt.

Test 26 is the must-reject, paired with test 7's accepted `Loop → Void`.

### 7.12 Index unification (new in draft 5)

Index unification (`unify_index.rs`) compares two index values by `conv`
first ("deletion", `:184`), then tries a solution, then injectivity and
conflict, which happen only at a data type in `Type`: at a proposition, or
at an equation, the constraint is stuck (`:238-241`, D137) **[checked]**.
With masks, deletion sees them, so `MkBox (Inl ())` and `MkBox (Inr ())` at
`Box (Unit ∨ Unit)` are deleted as equal. For

```
type T: Box (Unit ∨ Unit) → Type =
  | A: T (MkBox (Inl ()))
```

matching a `t: T (MkBox (Inr ()))` is `E-INDEX-STUCK` today ("they're proofs
of `Unit ∨ Unit`, and matching never takes proofs apart") **[run]**; under
D1′ the branch `A` is possible, so `| A => 0` is accepted and an empty match
`| ()` is refused because `A` can be there (`E-NOT-EMPTY`, expected; test 30).

*The order matters for completeness, not soundness.* The draft 4 review
thought that with injectivity before deletion this `T` would give a closed
proof of `Void`. It wouldn't: injectivity on `MkBox` leaves the constraint
`Inl () = Inr ()` at type `Unit ∨ Unit`, a proposition, which is stuck, not a
conflict (the check at `:238-241` comes before any conflict). So either order
is sound; deletion first is what lets the masks help index unification.
Stage 1 keeps the order and adds a comment at `:184` saying why.

*Proof-typed indices aren't masked in stage 1.* An index whose type is a
proposition (`type SameP (x: P): P → Prop`, `examples/soundness/
index-proof-conflict.sw`) is compared like any other index when two `Data`
values are compared. Masking it would be sound (index unification never
decides anything from a proof), but no program needs it, the elaborator's
index handling (`elab/src/families.rs`) would have to agree, and it can be
added later without changing anything else. So `SameP A A` and `SameP A B`
stay different types.

## 8. Tests

Per the soundness policy (DESIGN §13), each must-reject test has a nearby
accepted one, and declares its error code. Tests 9-13 and the changed
pairings of 4 and 6 are new in draft 2; 11b and 14-16 in draft 3.

| # | Must be rejected | Code | Why it matters | Paired accepted example |
|---|---|---|---|---|
| 1 | `rfl : MkTBox Nat = MkTBox Bool` for `type TBox : Type 1 = MkTBox (t : Type)` | `E-REFL` | A type field is erased but relevant: catches `field_erased` used for `field_sorts` | `rfl : MkChar 97 p = 'a'` (§2.2) |
| 2 | `rfl : choose Nat n = choose Bool n`, for `choose : Type -> Nat -> Nat` stuck on `n` | `E-REFL` | The same for definition parameters (`erase::of_def` marks types) | `sameMod` (§2.1) |
| 3 | `rfl : Sorted [1, 2] = Sorted [2, 1]`, for a test-defined `type Sorted (xs : List Nat) : Prop` | `E-REFL` | Data parameters that are data stay relevant | A data type with a proof parameter, two different proofs, `rfl` |
| 4 | With a test-defined `type Exists (p : Nat -> Prop) : Prop = MkEx (x : Nat) (h : p x)`: `def leak (e : Exists (n => n = n)) : Nat` matching out the witness; and `rfl : MkEx 1 rfl = MkEx 2 rfl` | `E-PROP-ELIM`; `E-REFL` | Irrelevance must not leak a proof's data (§5.3); a data field inside a proof is still compared | `rfl : MkEx 1 h1 = MkEx 1 h2` for two proofs `h1 h2 : 1 = 1` (the witness agrees, the proof field is skipped) |
| 5 | `J (y e => P y) d h = d` for a variable `h : n = n` | `E-REFL` | No K-like rule (§5.2) | `J (y e => P y) d rfl = d`; and `omegaUnfolds` (§5.2) checks within the default budget |
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
| 15 | With `def fnEq (n: Nat) (h: Unit): (Nat -> Nat) = (Nat -> Nat)` stuck on `n` and `def apply (f: Nat -> Nat) (x: Nat): Nat := f x`: `rfl : apply (J (y e => y) (x => x) (fnEq n u)) 3 = apply (J … (fnEq n u)) 4` | `E-REFL` | Masks cover only a definition's leading arguments, never an argument after a `J` entry (§7.2). A `J` entry can only come after at least the whole telescope (the proof must be an equation), so a mask indexed by spine position already gets this right; the test pins the rule against a looser implementation **[inferred]**. (`J` with a fourth argument is `E-ARITY`, hence `apply`.) Today: `E-REFL` **[run]** | the same with `fnEq n u1` and `fnEq n u2` and both applied to `3` (position 1 of `fnEq` is a proof position). Today `E-REFL` **[run]**; D1′ must accept |
| 16 | `undo.rs` unit test: inside `undo::unify`, `MkT ?p 1` against `MkT q 2` (field 0 a proof) | unit test | §7.4: a whole-proof solution made before a failure is undone by the transaction (`?p` unsolved afterwards); bare `cx.unify` leaves `?p := q`, documenting why the transaction is needed | `MkT ?p 1` against `MkT q 1` solves `?p := q` |

**New in draft 4: gluing (§7.10) and inert parameters (§7.3).** Each of 17
to 19 is run three ways, and must give the same answer in all three:
gluing on (the kernel's default inside a body); `set_shortcuts_disabled(true)`
(`value.rs:3248`, the glued-call shortcut off); and gluing off
(`Globals::glue` off in the kernel, `STITCHWORT_GLUE=0` in the elaborator).
As `.sw` tests they're in the accept/reject example sets; the three-way
runs are a Rust test over the same programs.

| # | Must be rejected | Code | Why it matters | Paired accepted example |
|---|---|---|---|---|
| 17 | `castRefl` (§5.7): `cast a a rfl x = cast a a h x` for `h: a = a`, with `cast := J (y e => y) x h`. Today `E-REFL`, "computing both sides gives `x` and `J (y e => y) x h`" **[run]** | `E-REFL` | A definition's mask on a parameter it computes with (here `J`'s proof) makes the shortcut disagree with unfolding (§5.7); D2349 clears the mask | `cast a a rfl x = x` (J on `rfl` computes); and test 20 |
| 18 | *Rewritten in draft 5 (D1980 refuses `steps`).* With `type Tok: Prop = \| MkTok` and `def tokNat (t: Tok) (k: Nat): Nat := match t with \| MkTok => k`: `tokNat t 0 = tokNat MkTok 0`. Today `E-REFL`, "computing the right side gives `0`" **[run]** | `E-REFL` | The shape of Carneiro's non-transitivity through the shortcut (§5.1) without recursion: with draft 3's masks the shortcut says "equal" (position 0 masked, `0 = 0`), unglued the right side computes and the left is stuck. `t` is taken apart, so it isn't inert | `tokNat MkTok k = k` (one step of computation) **[run]** |
| 19 | `unboxBoth` (§5.7): `Box.unbox (MkBox p) = Box.unbox (MkBox q)` for `p q: a`. Today `E-REFL`, "computing both sides gives `p` and `q`" **[run]** | `E-REFL` | The shortcut must compare constructor proof fields (D2352): with the field mask on in the shortcut, this is accepted glued and rejected unglued | `MkBox p = MkBox q` (the field mask, normal mode); and `Box.unbox (MkBox p) = p` |
| 20 | `Int.modNat x 100 [ok := p] = Int.modNat y 100 [ok := p]` for variables `x y` | `E-REFL` | Skipping the inert `ok` must not skip the relevant `x` | `Int.modNat x 100 [ok := p] = Int.modNat x 100 [ok := q]` (§2.1; today `E-REFL` **[run]**), with `x` a variable (stuck on `x`) and with `x` a literal (computes), and `Int.modNat x d [ok := p] = Int.modNat x d [ok := q]` with `d` a variable too (stuck on `d`; inert by D2353). Also `Nat.mod x 100 [ok := p] = Nat.mod x 100 [ok := q]` (accepted today too **[run]**; under D1′ the shortcut takes it without unfolding: a Rust test asserts that from the step count) |
| 21 | *Rewritten in draft 5.* `tokNat t 0 = tokNat t2 0` for two variables `t t2: Tok` (test 18's `tokNat`). Today `E-REFL` **[run]** | `E-REFL` | D2353 is only for a `case` with no possible branch: a one-branch `case` on a proof computes, so its parameter is compared in stuck calls too | `Void.absurd (p rfl) = Void.absurd (q rfl)` at `Nat`, `p q: 0 ≠ 0` (today `E-REFL` **[run]**; accepted by D2353) |
| 22 | A group of two definitions passing a proof parameter to each other, one of which also takes it apart: the comparison of two calls of the other member with different proofs | `E-REFL` | The fixed point must clear a mark through the group, not just in the member that computes | The same group with neither taking it apart (both stay inert, by the greatest fixed point); and `Fin.ofNatLt n i h1 = Fin.ofNatLt n i h2` (D2180's shape, recursive) |
| 23 | `def keep (d: Nat) (ok: d ≠ 0): Box (d ≠ 0) := MkBox ok`: `Box.unbox (keep d p) = Box.unbox (keep d q)` at `d ≠ 0` | `E-REFL` | D2354: a parameter stored in a field isn't inert, so the shortcut doesn't skip it (with it skipped, this is test 19 again, accepted glued only) | `keep d p = keep d q`: accepted both ways (no shortcut; the unfoldings are equal by the field mask) |

**New in draft 5.** Tests 24, 25 and 27 are also run the three ways above.

| # | Must be rejected | Code | Why it matters | Paired accepted example |
|---|---|---|---|---|
| 24 | With `def g (n: Nat): 0 = 0 → Bool := match n with \| Zero => h => J (y e => Bool) True h \| Succ m => g m` (arity 1): `g n rfl = g n h` for variables `n`, `h: 0 = 0` | `E-REFL` | Masks stop at the arity (§7.3): position 1 is past it, so it is compared. With telescope-bounded candidates it would be vacuously inert | `g 1 h = g 0 h` (one step of computation; accepted today **[run]**), and `g 0 rfl = True` |
| 25 | With `opaque def ou (b: Box a): a := Box.unbox b` (any opaque `Box.unbox`) and `p q: a`: `ou (MkBox p) = ou (MkBox q)`, checked where `ou` is hidden; and the same inside a declaration with `unfolding ou` | `E-REFL` both | A hidden call's arguments are compared in shortcut mode (K4): otherwise it is equal hidden and different transparent (§5.7) | `MkBox p = MkBox q` (field mask, normal mode), and `ou (MkBox p) = ou (MkBox p)` |
| 26 | `type Loop: Prop = \| MkLoop (next: Loop)` with `def steps (l: Loop): Nat := match l with \| MkLoop n => Succ (steps n)`. Accepted today **[run]** | `E-PROP-ELIM` | D1980 (§7.11): a self-referential proposition can't be matched into data; this is the root of Carneiro's undecidability (§5.1). In stage 1's first commit | `Loop.inv: Loop → Loop` and test 7's `Loop → Void`; `type Tok: Prop = \| MkTok` matched into `Nat` (test 18's `tokNat`) |
| 27 | With `def myAbsurd: Void → Nat \| ()`: none; this is a transitivity test. All three of `Void.absurd (p rfl) = Void.absurd (q rfl)`, `Void.absurd (q rfl) = myAbsurd (q rfl)` and `Void.absurd (p rfl) = myAbsurd (q rfl)` at `Nat`, `p q: 0 ≠ 0`, must be accepted. Today the first and third are `E-REFL` and the second checks **[run]** | (accept) | The case-tree comparison must not compare the scrutinees of two `case`s with no possible branch (§7.2), or the masked relation isn't transitive | must-reject partner: with `def tokA (t: Tok): Nat := match t with \| MkTok => 0` and `tokB` the same, `tokA t = tokB t2` for variables `t t2: Tok`: `E-REFL`, because the tree walk still compares the scrutinees of a `case` that has a branch |
| 28 | Unifier unit test: `unify(g ?n (MkBox p), g ?n (MkBox q))`, `g` stuck on `?n`, `g`'s second parameter of type `Box a` | unit test: fails, nothing solved | U3: a call blocked on a metavariable is compared in shortcut mode, so the unifier doesn't accept what the kernel rejects after `?n := 0` | `unify(g ?n (MkBox p), g 0 (MkBox p))` solves `?n := 0` |
| 29 | none: a Rust test, like SW-395's. Two chains `f (f (… (MkBox p)))` and `f (f (… (MkBox q)))`, 24 deep, `f` glued, differing only in the innermost proof field | (accept, in bounded steps) | `CallMemo` keyed by mode stays linear: each inner pair is compared at most once per mode. The test asserts a step count linear in the depth (and runs well under a second) | the same at depth 1 and 2, to fix the per-level count |
| 30 | With `type T: Box (Unit ∨ Unit) → Type = \| A: T (MkBox (Inl ()))`: `theorem noA: T (MkBox (Inr ())) → Void \| ()`. Today `E-INDEX-STUCK` **[run]** | `E-NOT-EMPTY` (expected; record the actual code) | §7.12: deletion runs before injectivity, so the field mask reaches index unification and `A` is possible | `def useA: T (MkBox (Inr ())) → Nat \| A => 0` (today `E-INDEX-STUCK` **[run]**; accepted under D1′) |

Must not hang: every test above is rejected or accepted promptly, well
within the default budget.

Unit tests beside them: comparing the same pair of calls in both modes within
one `conv` (one for `CallMemo`, one for `TreeMemo`: a pair found equal by
trees in normal mode, met again inside a shortcut, must be compared again);
the native test of §7.3; the reference validator over std (§7.3).

Also:

- **Mutation tests**: skipping nothing must fail the accepted tests;
  skipping erased positions (types too) must fail tests 1, 2 and 9; skipping
  every argument must fail tests 3, 4 (second part), 6 and 8; unifying
  inside skipped proofs must fail tests 11 and 11b; skipping every `App`
  after a head that has any proof position must fail test 15; solving proof metavariables without the undo
  trail must fail test 16. New in draft 4: masking every `Prop` parameter
  (draft 3's rule) must fail tests 17, 18, 21 and 22; keeping the field
  masks in shortcut mode must fail test 19; allowing a constructor field as
  an inert use must fail test 23; dropping D2353's clause must fail test 20
  and the accepted half of 21; a `CallMemo` key without the mode must fail
  a unit test that compares the same pair of calls in both modes in one
  `conv`. New in draft 5: candidates from the telescope instead of the arity
  must fail test 24; hidden calls compared in normal mode must fail test 25;
  dropping D1980's condition must fail test 26; comparing the scrutinees of
  two all-impossible `case`s must fail test 27; the unifier's blocked calls
  in normal mode must fail test 28; a `TreeMemo` key without the mode must
  fail its unit test; a native reading an inert position must fail the native
  test. *How (draft 5):* each mutation is a temporary local edit, not a
  switch kept in the code; the lane applies it, runs only the named tests
  (`task test:one`), records on the ticket which failed, and reverts it.
- **Differential**: `value::conv` against `reference::conv` on the kernel
  test programs, as for the evaluator.
- **Equivalence and gluing, enumerated (draft 5, in stage 1).** Drafts 3
  and 4 asked for property tests on *generated* well-typed values. There is
  no generator of well-typed kernel values, and writing one is a project of
  its own, so stage 1 replaces them with an enumerated Rust test over a
  fixed signature, well-typed by construction: a proposition `a` with proof
  variables `p`, `q`; `Box`; `Tok`; definitions with an inert proof
  parameter (`Int.modNat`'s shape), a non-inert one (`cast`, `tokNat`), one
  that unboxes (`Box.unbox`), one with an absurd branch (`Void.absurd`,
  `myAbsurd`), and a partially applied one; and a variable `n: Nat` to get
  stuck on. The test builds every term of one type up to depth 2 from these
  (a few hundred), and checks, for every pair and triple: reflexivity,
  symmetry and transitivity of `conv`; the same answer with gluing on,
  shortcuts disabled and gluing off; the same answer from `value::conv` and
  `reference::conv`; and, for the stuck ones, that substituting `n := 0`
  and `n := 1` never turns a "different" into "equal" for inert-only
  differences (the substitution bullet of §7.10). It includes by-tree pairs
  (two different definitions with the same tree shape) and eta pairs
  (`f` against `y => f y`). A random generator stays a possible follow-up,
  not a stage 1 requirement.
- **The std listing**: the inert analysis's debug listing for std matches
  §7.3's table, or the differences are explained on the ticket.
- **Unifier**: an implicit proof argument solved only by unification still
  gets solved.
- **Regression**: `examples/accept/char-pattern-proofs.sw` checks with and
  without `canonical` (stage 2 removes it); `aoc/` still checks. (SW-93's
  third motivating example, `dialExt`/`dialExtAt` in AoC 2025 day 1, no
  longer exists: `Aoc/Year2025/Day01/Proofs/Part2.sw` has been rewritten
  without it **[checked: `grep`]**, so it isn't a criterion.)
- **Glue-off corpus run**: once, before merging, the elaborator's accept and
  reject examples with `STITCHWORT_GLUE=0`, compared with the default run:
  the same verdicts. That is a corpus-sized run, so it goes in the daily-tier
  run D2348 already asks for (Matt approves it first), not in the lane's own
  tests.

## 9. Stages

1. **Kernel and unifier** (SW-93; Opus, as CLAUDE.md has it for kernel
   work: a mistake in the inert analysis or the shortcut mode changes what
   the kernel accepts). In this order, each a commit (or a few) on one
   branch:
   1. *Step 0, D1980* (§7.11): the `E-PROP-ELIM` condition, the measurement
      (std, `examples/`, `aoc/`, `games/rogue`), test 26, docs/core.md's
      `E-PROP-ELIM` paragraph. Stop and report if anything relies on it.
   2. *The marks*: `inert_params` (length `arity`) and `proof_params`, set
      in `install_group` and `declare_data` on both paths (§7.3); the std
      listing; the reference validator; the native test.
   3. *The skips* in `conv` (§7.2) with the `J` and arity boundaries, the
      case-tree change for all-impossible `case`s, and the reference `conv`.
   4. *The shortcut mode* at K1-K4, `CallMemo` and `TreeMemo` keyed by mode,
      the reference evaluator's R1-R3 and `EQUAL_CALLS`.
   5. *The unifier* (§7.5): the masks with the whole-metavariable rule,
      proof solutions through `solve`, the mode at U1-U5.
   6. *Tests* (§8): 1-30 with 11b, the three-way runs of 17-19, 24, 25 and
      27, the unit tests, the enumerated equivalence test, the mutations.
   7. *Docs*: docs/core.md (the rule, "Glued calls", the precondition,
      D1981's sentence), DESIGN §6 line 459 ("isn't needed for the POC"
      becomes the rule), the doc comments of §7.4, the comment at
      `unify_index.rs:184`, the pointer in mutual-recursion.md §6.7.

   **Done when** (draft 5):
   - every test of §8 passes (1-30 and 11b, the unit tests, the
     enumerated test), the three-way runs agree, and each mutation of §8
     fails the tests it names, recorded on the ticket;
   - §2.1's `sameMod` and §2.2's `handBuilt` check with `rfl`;
   - the std listing matches §7.3's table, or the ticket explains each
     difference;
   - the reference validator passes over std and the test programs;
   - `bench` before and after: no benchmark more than 10% slower, and any
     more than 5% slower explained on the ticket;
   - hash snapshots: unchanged, or each change explained (stage 1 changes
     no elaborated term on purpose; the unifier's opaque proof positions could
     leave a metavariable for `auto` that was solved from inside a proof
     before);
   - the orchestrator's merge tier is green, and the daily-tier run D2348
     asks for (approved by Matt first) is green, including the glue-off
     corpus run of §8.
2. **Remove workarounds** (Sonnet or DeepSeek): delete `canonical`
   (`elab/src/lib.rs:2370` and its callers at `:2479`, `:2528`) and check
   char-pattern proofs and `aoc/` still pass; optionally simplify
   `Char.mkExt` and the second `[auto]` proofs of `Int.modNatToInt`,
   `Int.toIntDiv`, `Int.toIntMod`; perhaps `Bool.canonicalTrue` in `Float`
   (§7.3); the `if h:` limit of function-equations.md (D2180), for branches
   whose `h` reaches only inert parameters and fields; update hash
   snapshots. No `Prop.irrel`
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
   draft 1 `rfl` rule. **A constraint on later work** (D1981, §7.6): record
   eta, if it lands, only for records with at least one field that isn't a
   proof.

## 10. Questions for Matt

**Decided (Matt, 19 October 2026):** all four as recommended: adopt D1′; leave `Prop.irrel` out of the prelude for now; remove `canonical` in stage 2, accepting the hash changes; wait for a real need before stage 3.

**Decided (Matt, 4 November 2026), D2349:** masks on a definition's
arguments only for proof parameters the definition never computes with
(§7.1, §7.3).

**Decided (4 November 2026), D2352 to D2355**: as recommended below, by the
orchestrator with Matt's delegation ("above my pay grade - can you make good
decisions?"); recorded on SW-93. D2355's review is
`proof-irrelevance-review.md`, answered in Appendix C.

**Decided in draft 5**: technical decisions inside the approved design, made
by this draft's author with the reasons given where they're specified.
Those marked **(visible)** change what a user can see, slightly; the
orchestrator may want to bring them to Matt, though none blocks stage 1:

1. Masks stop at `Def::arity` (§7.3). A correction, not a choice.
2. The complete shortcut list and the mode as a nested comparison's
   parameter (§7.2, §7.5).
3. **(visible)** A hidden opaque call compares its arguments in shortcut
   mode (§7.2 K4): `ou (MkChar 97 p)` and `ou 'a'` are different where `ou`
   is opaque and hidden, though equal where it's transparent. Reason: being
   transparent then only ever adds equalities, which opaque definitions
   promise (docs/core.md rule 3). Cost: probably none today. There are 49
   `opaque` declarations in std, `examples/`, `aoc/` and `games/`; the ones
   in AoC and rogue take seeds, levels, areas and entries **[checked:
   `grep`, signatures only]**, so a comparison of two calls differing only
   in a proof field is unlikely, though not traced. The alternative, normal
   mode, accepts more but lets an equality checked where the body is hidden
   fail where it's visible.
4. **(visible, accepts more)** Two definitions compared by their case trees,
   both stuck on a `case` with no possible branch, are equal without
   comparing the scrutinees (§7.2; test 27). Needed for transitivity.
5. **(visible, accepts more)** Index unification sees the masks, because
   deletion runs first (§7.12; test 30): a match that is `E-INDEX-STUCK`
   today can check.
6. **(visible)** Proof-typed indices of data types aren't masked in stage 1
   (§7.12): `SameP A A` and `SameP A B` stay different types.
7. The marks are computed in `install_group` on both paths; the check
   cache's format doesn't change (§7.3).
8. No marks for a definition without a body, or when computing them runs out
   of budget (§7.3).
9. Natives must not read inert positions; a unit test enforces it (§7.3).
10. The reference evaluator reads the marks and checks them with an
    independent validator, rather than recomputing them (§7.3).
11. D1980's step lands first on SW-93's branch (§7.11, §9). D1980 itself is
    Matt's; its error message is new text **(visible)**.
12. The random property tests are replaced in stage 1 by an enumerated test
    over a fixed signature (§8); mutations are temporary local edits,
    recorded on the ticket.
13. Stage 1's done criteria and bench threshold (§9).

The draft 4 questions, as they were asked:

- **D2352. The shortcut compares constructor proof fields.** In plain terms:
  when the checker compares two calls of the same function by their
  arguments, to save unfolding them, it treats a proof stored inside a
  constructor as mattering; only if that says "different" does it unfold
  the calls, and then the proof is ignored as usual. Without this, D2349
  isn't enough: `Box.unbox (MkBox p)` and `Box.unbox (MkBox q)` would be
  equal with gluing on and different with it off (§5.7, §7.10). The cost is
  speed only: two calls whose arguments differ only in such a proof (say
  `f 'a'` against `f (MkChar 97 p)`) are unfolded instead of matched.
  *Recommendation: yes.* The alternative that also works is a shortcut that
  skips no proofs at all (inert ones included): simpler to argue, but it
  gives up the shortcut for exactly the `Int.modNat x 100 [ok := …]` calls
  §2.1 is about.
- **D2353. A `case` with no possible branch doesn't count as computing.** In
  plain terms: `Void.absurd h` never computes, whatever `h` is, so a
  function that only hands its proof to `Void.absurd` (as `Int.modNat`
  does with `ok rfl` when the divisor is 0) still ignores that proof. Without
  it, `Int.modNat`, the other `Int` divisions, `Fin.ofNatLt` and every
  `decreasing` definition's fuel proof lose their masks, and §2.1 and
  D2180's `if h:` equations aren't fixed (§7.3). *Recommendation: yes.* It
  is safe for the reason §7.10 gives: such a `case` is stuck on both sides
  of any comparison.
- **D2354. Storing a proof parameter in a constructor field doesn't count
  as "passing it on".** D2349 said a parameter may be passed on to "other
  masked positions"; constructor fields are masked, but a field can be
  taken apart later and its proof used where it is compared, so allowing it
  makes the shortcut wrong again (`keep d p := MkBox p`, test 23, §7.10).
  The cost is that `Float.make` and `Map.Raw.fromSorted` lose their masks,
  which changes nothing in practice: they always unfold at once, to a
  record whose field mask applies (§7.3). *Recommendation: yes.* The
  alternative, two marks per parameter (one allowing fields, used only for
  stuck calls; one not, used by the shortcut), is more machinery for
  definitions that are almost never stuck.

- **D2355. A short independent review of draft 4's §7.3 and §7.10 before
  stage 1?** Draft 4 changes the design (the inert analysis, the shortcut's
  mode), and §7.10 is a new argument that the kernel's answers don't
  depend on gluing; the earlier reviews didn't see it. *Recommendation: yes*,
  scoped to §5.1's glued-call part, §5.7's new part, §7.1-7.3 and §7.10, by
  a reviewer given the code (`value.rs` `conv_step`, `same_spines`,
  `CallMemo`) rather than this note's conclusion.

Draft 3's questions follow, as decided.

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

Draft 3 said none was needed. Draft 4 changed the design, so D2355 asked for
a focused review; it was done (`proof-irrelevance-review.md`) and is answered
in Appendix C. Its answers, in short: (1) the induction is right in outline
but covered only the shortcuts listed, and there were more (§7.2's table now
has all of them); (2) yes, D2353 is right with indices: a branch is
impossible only by a conflict, and conflicts never involve a proof; (3) yes
for eta, and for case trees once the reviewer's step is stated, plus the gap
draft 5 found (all-impossible `case`s, §7.2). Draft 5 asks for no further
review: its changes are corrections the review asked for, plus the case-tree
fix, which only accepts more and is pinned by test 27. The questions were:

1. Is §7.10's induction right, and are §7.1's three clauses for "inert"
   enough for it? In particular: are there places other than the four in
   §7.2 that answer "equal" for two calls without unfolding?
2. Is D2353 (a `case` with no possible branch never computes) right in the
   presence of indexed families, where "impossible" is decided by index
   unification (docs/core.md "Unifying indices")?
3. Is the claim that the masked relation on normal forms is transitive on
   values of one type (§6) right once eta and the comparison of different
   definitions by their case trees (SW-386) are included?

The open theoretical question (normalisation, §5.7) isn't one that another
review of this note can settle.

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
- Draft 4: what the glued shortcut does with masks (§5.1, §5.7) is read
  from `value.rs` at `f3769d45`, not run, since masks aren't built; the
  programs were run only to confirm today's rejections and messages.
  §7.10 is an argument, not a proof, and it covers the kernel's `conv`,
  not the unifier. §7.3's table was worked out by hand from the source, and
  its std search was by `grep` for binders of a few proposition shapes,
  so it can miss definitions; stage 1's listing is the check. The
  `f.%go` row is from docs/core.md's description of `decreasing`, not from
  generated terms. That Lean's lazy delta compares a constant's arguments
  before unfolding, like the glued shortcut, is from Carneiro's rules
  (L4 §2.3), not from re-reading Lean's source.
- Experiments in §2 and §5.1–5.2 used the release build of `80c87a8`; the
  `E-REFL` in §2.1 wasn't traced to the elaborator or the kernel.
- Draft 5: the programs of tests 18, 21, 24, 26, 27 and 30 were run on
  today's build for today's answers; their answers under D1′ are inferred.
  The case-tree fix's soundness (an all-impossible `case` has an empty
  scrutinee type) is an argument, not a proof. D1980's measurement is a
  `grep`; the rule itself is the real check (§7.11). That no other place in
  the kernel or unifier answers "equal" for two calls that can still unfold
  comes from reading `conv_step`, `unify_step`, `reference::conv` and their
  helpers at `f4674240f`, not from a mechanical search.

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
  abstract; §2.2 (ideal `≡` and algorithmic `⇔`); §2.3 (the rules of `⇔`,
  no transitivity); §2.6 (subsingleton elimination, K-like reduction); §3.1
  (undecidability); §3.1.1 (non-transitivity, and quotients of
  propositions); §3.1.2 (subject reduction); §3.2 Lemma 3.4(3); §4.1 (`κ`,
  `K+`, `≡p`) and Theorem 4.7; §6 Corollary 6.8. Draft 4 read these from a
  copy of the PDF (text extracted locally), 4 November 2026.
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

## Appendix C: response to the draft 4 review

The review (`proof-irrelevance-review.md`, SW-1268, at `f4674240f`) found
the design sound and decidable, with gaps in the spec. Each point, checked
against the code where it could be:

| # | Point | Verdict | Where changed |
|---|---|---|---|
| 1.1 | Evaluation untouched; the masks only add equations true in Carneiro's model, given the same-type invariant; the note's uses of the thesis are accurate | **Agree.** | — |
| 1.2 | Acc-style recursion on proofs needs a `case`, which clears the mark; `Acc`'s large elimination is refused for its data field; Carneiro's construction would need a `Loop`-like type, which D1980 refuses | **Agree**, and checked: `Acc` declares and its match into `Nat` is `E-PROP-ELIM` **[run]**. | §3, §7.11 |
| 1.3 | Constructor fields, partial application, eta, mutual recursion, stuck cases: safe; clauses 1-3 are a whitelist | **Agree.** | — |
| 1.4a | D2353 is safe with indices: impossibility is only by conflict, never at a proposition | **Agree** (`unify_index.rs:238-241`). | §11 |
| 1.4b | Deletion before injectivity is needed for soundness: with injectivity first, `T (MkBox (Inl ()))` would give a closed proof of `Void` | **Disagree with the reason, keep the order.** Injectivity on `MkBox` leaves `Inl () = Inr ()` at `Unit ∨ Unit`, a proposition, which is stuck, not a conflict; today the shape is `E-INDEX-STUCK` for exactly that reason **[run]**. So the order matters for completeness: deletion first lets masks reach index unification. Comment and test kept, with that reason. | §7.12, test 30 |
| 1.4c | Prop-typed indices: say whether masked | **Adopt: not masked in stage 1.** | §7.1, §7.3, §7.12, §10 item 6 |
| 1.5 | Candidates must be below `Def::arity`, not the telescope (`g (n: Nat): 0 = 0 → Bool`) | **Adopt.** Checked: `telescope` peels every `Pi` (`check.rs:3740-3757`), `arity` counts leading lambdas (`globals.rs:38-44`); `g` and `g 1 h = g 0 h` check today **[run]**. | §5.7, §7.1, §7.2, §7.3, test 24 |
| 1.6 | The unifier's undo of shortcut solutions is right | **Agree**; and `Nat.div m d ?ok` still falls back as today. | §7.5 |
| 2 | Decidability: sound; the fallback cost is relative to draft 3, not today; `CallMemo` stays linear with two modes; add a depth-24 test | **Adopt** all three. | §0, §7.3, test 29 |
| 3.1 | State §7.10 as a logical relation (closure under application); clause 1 means any enclosing call; the walk stops at an inert argument | **Adopt.** | §7.1, §7.10 |
| 3.2 | More shortcuts: `TreeMemo`, hidden opaque calls, the unifier's folded, partial-application and blocked-on-metavariable sites | **Adopt, and extended**: the unifier's hidden calls (U5), the reference evaluator's folded and partial-application arms and its own `EQUAL_CALLS` memo. The mode is carried as a parameter of each nested comparison rather than of `ConvTask`, since every switch to shortcut mode already starts one. | §7.2's table, §7.5, tests 25, 28, unit tests |
| 3.2′ | Optional refinement: keep field masks inside a stuck neutral's spine in shortcut mode | **Not for stage 1**: not needed for correctness, and a third state. | §7.2 |
| 3.3 | Transitivity across SW-386's comparison by case trees needs its own step | **Adopt, and found a gap the review didn't**: the tree walk compares the scrutinees of a `case` with no possible branch, so `Void.absurd (p rfl)` against `myAbsurd (q rfl)` fails while each is equal to the same call with the other proof by its inert mask. Fixed by not comparing those scrutinees. | §6, §7.1, §7.2, §7.10, test 27 |
| 4 | Two more subject-reduction sources (beyond the arity; hidden calls); then constructor fields are the only one | **Adopt.** Both closed by 1.5 and K4. | §5.7 |
| 5.1 | D1980 is missing; tests 18 and 21 can't be written; tests 7 and 14 survive | **Adopt.** D1980 is step 0 of stage 1; tests 18 and 21 use `Tok`; `Loop`/`steps` is the must-reject test 26. | §5.1, §7.11, §8, §9 |
| 5.2 | Carry D1981 | **Adopt.** | §7.6, §9 |
| 5.3-5.5 | Prop indices, arity, shortcut list | As 1.4c, 1.5, 3.2. | — |
| 5.6 | Natives and bodiless declarations | **Adopt**: natives must not read inert positions (a unit test); a final definition always has a body (`globals.rs:33-36`), and one without gets no marks. | §7.3 |
| 5.7 | Clause 2: kernel lambdas have no domain; say a `let`'s type and an `Ann`'s type | **Adopt** (`term.rs:179`, `:181`). | §7.1 |
| 5.8 | `reference.rs`: recommend recomputing the flags independently | **Changed**: it reads them, and an independent one-pass validator checks every mark is justified. A second fixed-point analysis would double the riskiest code; the validator checks the property soundness depends on, and the std listing checks the rest. | §7.3 |
| 5.9 | The check cache storing the flags is a format change; list it | **Changed**: it doesn't store them. The marks are recomputed in `install_group`, which the cache's replay goes through (`admit_trusted_group`), so the format doesn't change, and a cache entry can't carry wrong marks. (Draft 4's "stores and replays" was wrong: the erasure flags aren't stored either.) | §7.3, §7.6 |
| 5.10 | Done criteria: say whether the property tests are in stage 1, and what bench must show | **Adopt**: an enumerated test over a fixed signature replaces them in stage 1; bench threshold 10% (5% explained). | §8, §9 |
| 6 | Small: §3 stale on indices; §0's fallback wording; §7.2's unifier line numbers | **Adopt.** | §0, §3, §7.5 |

