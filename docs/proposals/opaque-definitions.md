# Proposal: opaque definitions

**Status:** draft 2, 25 October 2026. Design only, nothing built. Ticket SW-505, decision
D1262 (Matt: write this note). D1263, D1264 and D1267 ([§10](#10-decisions)) are open; D1265 and
D1266 are decided (yes, as build details). Draft 1 was written against commit `11e029b2` (all
**[run]** results are from that build); draft 2 folds in an external review
([§11](#11-review)) and was revised at `eb1476ca`. Related: [folded-calls.md](folded-calls.md) (glued calls,
D483, D484), [equation-lemmas.md](equation-lemmas.md), [well-founded-recursion.md](well-founded-recursion.md)
(`f.unfold`), [attributes.md](attributes.md), `games/rogue/NOTES.md` (stage 2, item 1),
SW-501 (zero-argument constants in goals).

Labels, as in the other notes:

- **[run]**: a Stitchwort program I ran for this note (release CLI built from `11e029b2`,
  plus the scratch prototype of [§7.3](#73-the-prototype), which is not committed);
- **[checked]**: read in the Stitchwort source or docs at the place given;
- **[cited]**: read in the primary source linked in [Sources](#sources) while writing this;
- **[inferred]**: my reasoning from checked or cited facts;
- **[unverified]**: believed, not confirmed. Anything speculative says so.

## Contents

0. [Summary](#0-summary)
1. [Words used here](#1-words-used-here)
2. [What actually sank the roguelike's proofs](#2-what-actually-sank-the-roguelikes-proofs)
3. [How unfolding works in Stitchwort today](#3-how-unfolding-works-in-stitchwort-today)
4. [How other languages do it](#4-how-other-languages-do-it)
5. [Is it sound? The metatheory](#5-is-it-sound-the-metatheory)
6. [The design](#6-the-design)
7. [Worked example: the roguelike, generating on the stairs](#7-worked-example-the-roguelike-generating-on-the-stairs)
8. [Fix the checker anyway](#8-fix-the-checker-anyway)
9. [Build plan](#9-build-plan)
10. [Decisions](#10-decisions)
11. [Review](#11-review)
- [Sources](#sources)

## 0. Summary

- **The roguelike's failure has two causes, both found** ([§2](#2-what-actually-sank-the-roguelikes-proofs), **[run]**).
  1. *Elaborator.* To build a `match e:` motive and to search for a `rewrite`, the elaborator
     reads the goal back **fully unfolded** (`matching.rs:582`, `rewrite.rs:654`; D484). That
     read-back goes inside both branches of an `if` that can't step, so in `resolve`'s `Descend`
     branch it runs `seeded` over the whole generator on an unknown seed and passes the
     10-million-node limit: the `E-RESOURCE` "a value was too large to show". It happens even
     in a proof that only takes the "not on the stairs" branch.
  2. *Kernel.* The descent lemma itself then hangs (over 60 s) in the kernel's conversion,
     which compares two separately computed copies of the generated level cell by cell, because
     the kernel never compares two calls by their arguments first (D483).
- **Opacity would have fixed it, but only if the kernel enforces it too.** A scratch prototype
  (`generateLevel` opaque) makes the stage-2 design check in 4 s with `stepValid` unchanged;
  opaque in the elaborator only, it still hangs in the kernel. **[run]**
- **Both checker weaknesses are worth fixing anyway** ([§8](#8-fix-the-checker-anyway)): a
  kernel that compares same calls by their arguments first (1 s instead of over 60 s on the
  descent lemma, **[run]**), and a `match`/`rewrite` read-back that doesn't expand untaken
  branches (not a one-liner: reading back folded breaks `std`, **[run]**).
- **Other languages** ([§4](#4-how-other-languages-do-it)): Agda's `opaque … unfolding` is a real
  rule with a use-site opt-in, which its manual says is "handled entirely at the elaborator
  level"; Lean's `@[irreducible]` binds only the elaborator, while its separate `opaque`
  declaration kind binds the kernel but can never be reopened; Rocq's `Opaque` is a hint but
  `Qed` is final; Idris hides bodies per module; F\* and Dafny hide bodies from the SMT solver,
  with `reveal`. What Stitchwort adds is the combination: kernel-enforced opacity that a
  declaration can reopen selectively.
- **Soundness** ([§5](#5-is-it-sound-the-metatheory)): Danielsson and Geng (TyDe 2025) mechanise
  an Agda-style design and prove subject reduction, well-formedness preservation, consistency
  and decidable conversion. Their design needs exactly this note's two rules (the type is
  checked with nothing unfolded; unfolding is transitive), and they give a counterexample for
  the non-transitive variant. Their calculus isn't Stitchwort's, so this supports the design
  rather than proving it.
- **The proposal** ([§6](#6-the-design)): `opaque def f …`, enforced by the elaborator and the
  kernel and part of `f`'s hash; a declaration that needs the body says `unfolding f`; every
  opaque `f` whose equation can be stated gets `f.unfold`. Opacity is *definitional*: it keeps a
  body out of conversion, and hides nothing (`f.unfold` states the body). The kernel invariant
  is stated in [§6.4](#64-who-enforces-it-the-kernel-too). Running, `--js`, tests and the
  counterexample search are unaffected. `decreasing` definitions stay transparent;
  zero-argument constants are a display fix (SW-501), not opacity.


## 1. Words used here

- **Unfolding** a definition: replacing a call `f a b` by `f`'s body with `a` and `b` put in.
  The checker does this whenever it needs to know what a value *is*.
- **The elaborator** (`crates/elab`) turns what you wrote into small, explicit core terms,
  filling in hidden arguments and building `match` and `rewrite` steps. It is large and
  clever, and not trusted.
- **The kernel** (`crates/core/src/check.rs`) re-checks every core term the elaborator
  produces. It is small, and it is the only part that has to be right for a proof to be
  trusted (DESIGN.md §2, principle 4).
- **Conversion** is the kernel's "are these two the same?" test: two types are the same if
  they compute to the same thing.
- **Reading back** (`quote`) turns a computed value into a term again. Read back *unfolded*,
  every call is replaced by what it computes to, all the way down, including inside the
  bodies of functions; read back *folded* (`quote_folded`), a call stays a call.
- **A glued call** (`Value::Call`, [folded-calls.md](folded-calls.md)) is the elaborator's
  way of keeping both: the call, and (computed only when something looks) its unfolding.
- **Neutral**: a value that can't compute further and isn't a constructor: a variable, or a
  stuck call, applied to arguments (its *spine*). Two neutrals with the same head are compared
  by comparing their spines, argument by argument.
- **Opaque**: a definition the checker treats as a name with a type and no body, so a call of
  it is neutral, like a variable applied to arguments. Running the program still uses the
  body. This is **definitional opacity**: the body takes no part in "are these two the same?".
  It is not information hiding; anyone can read the body, and `f.unfold` states it as a
  theorem.
- **Transparency set**: the opaque definitions whose bodies a declaration may use, fixed
  before its body is checked ([§6.4](#64-who-enforces-it-the-kernel-too)).

## 2. What actually sank the roguelike's proofs

### 2.1 The reproduction

Stage 2 of `games/rogue` first made the next level inside the pure turn function. I rebuilt
that version in a scratch copy of the project: `descend` takes the turn's dice and runs the
generator under the game's own `seeded` handler; nothing else in the game changes. **[run]**

```stitchwort
def descend (dice: Dice) (state: State): State :=
  let plan := seeded dice.seed (() => generateLevel (state.level.depth + 1))
  let arrived := arrive state plan
  { arrived | turn = state.turn + 1, message = "You go down the stairs." }
```

The four `descend…` lemmas get the obvious new proofs (each is now about `plan` rather than
the head of `state.below`; for example `descendOutOfWalls` is
`startOnFloor (seeded dice.seed (() => generateLevel (state.level.depth + 1))).level`), and
`resolve…` pass `dice` on. `stepValid` and every other theorem are unchanged.

`stitchwort check` on that copy ran for 120 s and was stopped. **[run]** Taking it apart
showed **two separate problems**, neither of them the counterexample search (which `check`
doesn't run unless asked, `--counterexamples`) and neither of them `seeded` itself.

| What I checked (scratch, `check --no-cache`) | Result | Where the time goes |
|---|---|---|
| The four theorems `resolveAtMost`, `resolveOutOfWalls`, `resolveOnFloor`, `resolveClear` | `E-RESOURCE`, "a value was too large to show", in 2 to 7 s | **elaborator**: `match` and `rewrite` read the goal back unfolded |
| A theorem that only rewrites by the phase and by `isStairs … = False` (so it never reaches `descend`): `rewrite playing, offStairs in atMost` | `E-RESOURCE` in 5 s | the same |
| `descendOutOfWalls` alone | over 60 s, stopped | **kernel**: conversion compares two copies of a whole generated level |
| `descendAtMost` (`atMost`) and `resolve dice state Quit` with a `match` on the phase | checks at once | nothing unfolds the generator |

### 2.2 Problem 1: `match` and `rewrite` read the goal back fully unfolded

The `E-RESOURCE` is raised by the read-back's size limit of 10 million nodes
(`crates/core/src/value.rs`, `quote_as`; the limit is `Limits::size` in `budget.rs`).
**[checked]** I made the scratch build print a backtrace when it's hit. **[run]** For
`resolveAtMost`, the fatal one is:

```text
quote_as         crates/core/src/value.rs
generalised      crates/elab/src/matching.rs:582   let goal_term = generalise.apply(g, &quote(g, base, goal)?)?;
check_match      crates/elab/src/matching.rs:241
…
```

and for the `rewrite`-only theorem:

```text
quote_as         crates/core/src/value.rs
quote            crates/elab/src/check.rs:434
rewrite_once     crates/elab/src/rewrite.rs:654    let mut goal_term = cx.quote(&goal_value)?;
check_rewrite    crates/elab/src/rewrite.rs:262
```

(Two earlier hits in each run come from `zonk`'s `both_forms` under `cheaply`, a 10,000-node
budget whose failure is caught and ignored, `unify.rs:1450`: harmless.)

So: to build the motive of `match e: … with` (the goal with `e` replaced by each pattern), and
to find what to replace in a `rewrite`, the elaborator reads the goal back **unfolded**. That
was a deliberate choice when calls were glued (D484: "`rewrite` and other searches still
seeing the unfolded goal, so no proof needs to change", folded-calls.md §6) **[checked]**,
and it is why the roguelike's proofs work at all: `isStairs state.level state.player` only
appears in the goal of `resolveAtMost` once `resolve` is unfolded.

The catch is *how far* an unfolded read-back goes. In the `Descend` branch the goal is
`(if isStairs … then descend dice state else …).hitPoints ≤ maxHitPoints`. The `if` can't
step (whether the player is on the stairs isn't known), and an `if` takes its two branches as
functions, so a full read-back goes inside both of them and unfolds `descend dice state`:
`seeded` runs the whole generator with an unknown seed (`dice.seed` is a variable). Every
roll is then an expression in that unknown, and `Level.build` draws all 20 by 66 cells of the
terrain from those expressions, each copy written out in full. That passes 10 million nodes.
The branch the proof never takes is read back as eagerly as the one it does, which is why
"every theorem about a turn" failed. **[run]** for the failure and the backtrace;
**[inferred]** for which part of the generator makes the term large (I didn't measure the
term, only that it exceeds the limit).

### 2.3 Problem 2: the kernel compares two generated levels piece by piece

`descendOutOfWalls` gets through the elaborator; then the kernel runs for over a minute. A
stack sample taken 12 s in (macOS `sample`, 2,402 samples) has every sample under
`stitchwort_core::check::define_group` → `check` → `value::conv`, mostly in
`native::compare` and big-number additions and subtractions. **[run]**

The kernel checks with gluing off (D483, `crates/elab/src/kernel.rs:21`), and its conversion
compares calls by their unfoldings, never by their arguments first (`value.rs:2221`: "Calls
are compared by their unfoldings (D483 …)"). **[checked]** The goal says
`isWall (descend dice state).level (descend dice state).player = False`; the proof's type
says the same about `(seeded dice.seed (() => generateLevel …)).level`. They are equal, but
the kernel finds that out by computing both levels (a second, separate run of the generator
on an unknown seed) and comparing them cell by cell, with the arithmetic of every roll.

### 2.4 Would opacity have fixed it?

**Yes, but only if the kernel respects it too.** With a scratch flag that makes
`Rogue.generateLevel` opaque ([§7.3](#73-the-prototype)), the stage-2 design checks: **[run]**

| Scratch run on the "generate on the stairs" copy | Result |
|---|---|
| no flag | stopped after 120 s |
| `generateLevel` opaque in the elaborator **and** the kernel | **checks in 4 s** (the proofs alone: 1.8 s, against 1.25 s for today's game) |
| opaque in the elaborator only | stopped after 90 s; sampled: all in the kernel's `conv` |
| opaque in the elaborator only, plus the kernel comparing two calls of the same definition by their arguments first (glued, as the elaborator does) | checks in 4 s |
| no opacity, kernel arguments-first only | the four `resolve…` theorems still fail (problem 1) |

Opaque, `generateLevel depth` is a name the checker can't look inside, so `seeded` can't run
it: the plan stays the small expression `seeded seed (() => generateLevel depth)`, the full
read-back stays small, and the kernel sees the same small expression on both sides.

**And it's also a checker weakness that should be fixed anyway** ([§8](#8-fix-the-checker-anyway)).
Neither problem is wrong (each answer would be correct given time); both are the checker
doing far more work than the question needs:

1. A read-back for `match` and `rewrite` that goes inside the branches of an `if` that
   can't step. A cheap experiment, reading back folded in both places, broke the standard
   library (`std/Result/Result.sw` stopped checking: "`rewrite` found no
   `Result.traverseLoop f [y] xs` in the goal") **[run]**, so the fix is not a one-liner;
   D484 had a reason.
2. A kernel that compares two copies of the same call by computing both
   (stage 4 of folded-calls.md, "Optional, later (D483)").

Fixing the checker helps every program; opacity helps when a definition's body really is
none of the proof's business, which the roguelike's generator is: "No proof looks inside
the generator" (`games/rogue/NOTES.md`, stage 2, "What went well") **[checked]**.

## 3. How unfolding works in Stitchwort today

**The evaluator** (`crates/core/src/value.rs`) is shared by the elaborator, the kernel and
the reference runner. Its policy (docs/core.md, "Evaluation and conversion") **[checked]**:

- A definition with all its arguments unfolds **only if its case tree can take a step**;
  otherwise it stays a folded call (`List.length xs` with `xs` unknown). That is what keeps
  comparison from unfolding recursive definitions forever.
- **Zero-argument constants always unfold** on sight (`eval_step`, `value.rs:922`, the
  `def.arity == 0` arm), which is why goals print `12` for `maxHitPoints` (SW-501).
- **Dictionaries and theorems stay folded by name** until something takes them apart
  (`folds`, `value.rs:1571`). This changes *when* things are computed, never *what* is
  equal, so it isn't hashed. It is the closest thing Stitchwort has to opacity, and it is
  not opacity: any comparison that the name alone can't settle unfolds them.
- **Glued calls** (elaborator only, D483): a call is kept as a `Value::Call` that means its
  unfolding, computed the first time something looks. The elaborator's unification tries two
  calls of the same definition by their arguments first; goals and hidden-argument solutions
  are read back folded; `rewrite`'s search, `match`'s motive and the decision search read back
  unfolded (D484).

**The kernel** never glues (`kernel.rs:21`, `unglued`): it computes values directly and
compares them structurally, with the dictionary and theorem shortcuts. Everything the
elaborator decides is re-checked there, so anything that changes *what is equal* has to be
known to the kernel, or the kernel will compute more than the elaborator did (problem 2) or
disagree with it.

**Where the elaborator unfolds on purpose** **[checked]**: `rfl` (`E-REFL` "`rfl` proves
`a = b` only when both sides compute to the same value"), `decide` and `auto` (a decision
procedure is computed), `match e:` on an expression and `rewrite` (unfolded read-back, D484),
unification (lazily, through glued calls), and `omega` (which treats what it can't read as an
atom: rogue's stage-2 item 2 shows `Nat.divFuel n n 2` as an atom). All of them go through
the one evaluator, so one rule there ("this name has no body while checking") covers them all.

**Where unfolding doesn't matter**: running. `stitchwort run`, `run --js`, `build --js` and
`test` run programs with erasure on (`erasure.program_running()`), and the counterexample
search evaluates under `g.erasure.running()` too (`counterexample/mod.rs:635`) **[checked]**.
In the prototype, today's roguelike with `generateLevel` opaque still passes all 99 tests
**[run]**.

## 4. How other languages do it

Everything in this section is **[cited]** from the sources listed at the end unless marked
otherwise.

**Agda: `opaque` blocks with `unfolding`, and the older `abstract`** [A1, A2, A3, A4].
Since 2.6.4, definitions in an `opaque` block "behave like postulates" outside it, and "opacity
can be selectively controlled at use-sites": another block that starts with `unfolding x`
sees `x`'s body. Unfolding is transitive: if a block that unfolds `x` defines `y`, unfolding
`y` unfolds `x` too. Opaque definitions "do not reduce in type signatures", even in their own
block. No equation is generated; `unfolding` is the only way in. The manual gives the
motivation as "goal readability and performance", and bases the design on Gratzer et al.
[P2]. `abstract` is the older form: hidden outside the defining module (child modules see
through it), and its only way in is to be inside another `abstract` block. `opaque` was added
because that was "much too coarse" (the design discussion, [A4]). The unfolding set "is
per-block, not per-definition": "Unfolding any name in an opaque block will cause any of the
other names in that block to be unfolded as well" [A1]. **Where it's enforced:** the manual
says the implementation is "based on the theory introduced by Gratzer et. al. in Controlling
unfolding in type theory, but handled entirely at the elaborator level, without a dependency
on our (cubical) extension types" [A1] (the page for 2.10.0 and for 2.8.0.2 both say it). In
context the sentence contrasts Agda with Gratzer et al.'s elaboration into a core with
extension types, rather than describing a kernel; either way it means Agda is no precedent
for a *separate* kernel enforcing opacity. **[cited]**, with the reading of the sentence
**[inferred]**.

**Lean 4: reducibility attributes, `seal`, irreducible well-founded definitions** [L1–L6].
`@[irreducible]`, `@[semireducible]` (the default) and `@[reducible]` set when the
elaborator's `whnf` and `isDefEq` may unfold a definition, by *transparency mode*:
`reducible` (used by `simp`, `rw` and instance search), `default` (ordinary checking, which
unfolds everything except `@[irreducible]`), and `all` (which unfolds even those).
**The kernel ignores these attributes**: its own reducibility hints "only affect performance
… but never prevent the kernel from unfolding a definition during type checking", and they
"are not related to the `@[reducible]`/`@[irreducible]`/`@[semireducible]`" attributes [L2].
**Lean does have kernel opacity**, in the separate `opaque` declaration kind: "Opaque
constants are defined constants that are not subject to δ-reduction in the kernel"; "Opaque
definitions with right-hand sides are elaborated like other definitions. This demonstrates
that the type is inhabited; the inhabitant plays no further role", except that "the
inhabitant of the type is used in compiled code" [L3]. So an `opaque` is checked against its
body, runs its body, and has no way back in: no `unfolding`, no equation. What Lean lacks is
kernel opacity that can be *reopened selectively*. Theorems "are irreducible by default"
[L4]. Since v4.9.0, definitions by well-founded recursion are `@[irreducible]` by default, to
avoid "the expensive and often unfruitful unfolding of such definitions"; the same release added
`seal f` / `unseal f in …` to change reducibility locally [L5]. The way back in is an
equation: `unfold f` uses "the 'unfolding lemma' `id.eq_def`, which is generated for each
recursive definition", and `rw [f]` uses `f`'s equation lemmas [L6]. Mathlib's
`irreducible_def foo := 42` makes a constant that "does not reduce to the value" plus "a theorem
`foo_def : foo = 42`" [L7].

**Rocq (Coq): `Opaque`, `Strategy`, and `Qed`** [R1]. `Opaque f` is a hint, scoped to the
section or module by default: it stops tactics unfolding `f` and makes conversion "delay
unfolding" it. `Strategy` orders unfolding "both at the tactic level and at the kernel level",
lower levels first. Real opacity comes from how a proof ends: "Theorems ending with Qed are
permanently marked opaque. These are never unfolded and they can't be made transparent";
`Defined` leaves them transparent.

**Idris 2: `export` against `public export`** [I1]. Visibility is per module. With `export`
only a function's type leaves the module; with `public export` "the type and definition are
exported, and the definition can be used after it is imported", which is what you need "if
it's … meant to be used at *compile* time (e.g. to prove a theorem)". There's no opacity
inside a module and no opt-in.

**F\*: `irreducible` and `opaque_to_smt`** [F1, F2]. `irreducible` means "a definition may
never be reduced by F*'s normalizer nor by the SMT solver". `[@"opaque_to_smt"]` hides a body
from the SMT solver only; `reveal_opaque (`%f) f` puts it back for "the rest of the scope", by
normalising the definition and passing it to Z3. The wiki warns that revealing the same
definition many times is brittle.

**Dafny: `opaque`, `hide` and `reveal`** [D1, D2, D3]. Functions are visible to the verifier
by default; `hide f;` (newer) or the `opaque` modifier (older, formerly `{:opaque}`) makes the
verifier treat `f` as an uninterpreted function, and `reveal f();` brings the body back "until
the end of the block containing the reveal statement". `--default-function-opacity opaque`
flips the default for a whole program. The motivation is verification time and brittleness:
"Making definitions opaque can be particularly important when they are recursive or involve
quantifiers" [D3].

**Liquid Haskell and Isabelle** [H1, S1]. In Liquid Haskell a Haskell function reaches the
logic only if asked: `reflect` makes it an uninterpreted function whose body proofs unfold
(through PLE), `inline` expands a non-recursive one, and anything else is an uninterpreted
symbol. In Isabelle, a constant's definition "can be used as simplification rules, but by
default they are not"; a proof unfolds it with `simp only: f_def` or `unfolding f_def`.

**smalltt** [K1]. Glued evaluation keeps "lazy ("non-deterministic") choice between unfolding
the definition, and not unfolding it"; "top definitions are never unfolded in any meta
solution". That is unfolding control inside the checker, not a user-visible opacity.

**Content hashes.** I found no language in which opacity is part of a definition's hash.
Unison, the nearest case, hashes structure "with all identifiers removed" and has unique types
[U1]; it has no notion of unfolding to hash.

### 4.1 Comparison

| Language | How you mark it | Unit | Hidden from | How a proof gets the body | Equation generated | Enforced by the kernel |
|---|---|---|---|---|---|---|
| Agda (`opaque`) | `opaque` block | block | everything outside the block, type signatures too | `unfolding f` at the start of another block (transitive) | no | n/a: "handled entirely at the elaborator level" [A1] |
| Agda (`abstract`) | `abstract` block | block, by module | parent and sibling modules | only from another `abstract` block (coarse) | no | as above |
| Lean 4 | `@[irreducible]` | definition | elaborator at `default` transparency | `unfold f`, `rw [f]`, `unseal f in`, `with_unfolding_all` | `f.eq_def`, equation lemmas | **no** (hints only) |
| Lean 4 (well-founded) | automatic since 4.9 | definition | as above | as above | yes | no |
| Lean 4 (`opaque`) | `opaque` declaration | constant | elaborator and kernel, for good | none: "the inhabitant plays no further role" | no | **yes**, not reopenable |
| Rocq | `Opaque f`; `Qed` | constant | `Opaque`: tactics, and delays conversion; `Qed`: everything | `Transparent f`; never for `Qed` | no | `Opaque`: no (a delay); `Qed`: yes, not reopenable |
| Idris 2 | `export` (vs `public export`) | definition | other modules | none | no | n/a (per module) |
| F\* | `irreducible`; `[@"opaque_to_smt"]` | definition | normaliser and SMT; SMT only | `reveal_opaque` (SMT only) | no | n/a (SMT-based) |
| Dafny | `opaque` / `hide` | function | the verifier | `reveal f();` in a block | lemmas internally | n/a (SMT-based) |
| Isabelle | (default for `definition`) | constant | the simplifier | `unfolding f_def`, `simp only: f_def` | `f_def` | n/a (LCF kernel proves equations) |
| **Stitchwort (proposed)** | `opaque def` | definition | the elaborator and the kernel, outside running | `unfolding f` on the declaration (transitive) | `f.unfold` | **yes**, reopenable per declaration |

So kernel opacity itself has precedent (Lean's `opaque`, Rocq's `Qed`), and so does selective
reopening (Agda's `unfolding`, enforced in its one checker). What I found nowhere is both at
once: opacity the trusted kernel enforces, which a declaration can reopen by name, with the
reopening recorded in the declaration the kernel checks. That combination is the distinctive
part of this design. **[inferred]** from the rows above.

What to take [inferred]: Agda's model (opacity as a real rule with an `unfolding` opt-in);
Lean's and Isabelle's equation (`f.eq_def`, `f_def`) as the everyday way in, which Stitchwort
already has a name for (`f.unfold`); Lean's lesson that elaborator-only opacity leaves the
kernel doing the work (what §2.4 measured); Lean's `opaque` and Rocq's `Qed` as the precedents
for opacity the kernel enforces. Not Dafny's `reveal`-in-a-block, which suits SMT verification, where the
cost is in what the solver is told, rather than a kernel that re-checks terms.

## 5. Is it sound? The metatheory

Draft 1 had read only the abstract of the paper this section rests on. Draft 2 read the full
text [P1]; everything quoted from it here is **[cited]**, with section and theorem numbers.

**The paper.** Danielsson and Geng (TyDe 2025, "A Formalization of Opaque Definitions for a
Dependent Type Theory") extend the graded-type-theory Agda formalisation with top-level
definitions, then opaque ones, "based on Agda", and present it as "the first mechanization of
the metatheory of opaque definitions for a language with dependent types" (§1). An entry of
their definition context carries an opacity, `tra` or `opa(φ)`, where the bits of the
*unfolding vector* φ are the definition's `unfolding` clause (Definition 5.2). Only an opaque
entry carries a φ: a transparent definition has no `unfolding` clause at all, which is this
note's refusal of `unfolding` on a plain `def` (§6.3).

**The two rules are theirs.**

1. *The type is checked with nothing unfolded.* In the well-formedness rule for an opaque
   entry the type is checked in the original context ∇ and only the body in the
   transparentised ∇′ (Definition 5.8, `extend-opa`): "even in the opaque case, the type of
   the definition must check in the original context: the type signature of an 'interface'
   definition must not leak the 'implementation details' of any opaque definitions."
2. *Unfolding is transitive.* The *transparentisation* relation φ » ∇′ ⇝ ∇ (Definition 5.7)
   makes the marked definitions transparent, and its `yes-opa` rule merges an opaque
   definition's own vector into the running one: "Note the ⊔ in the yes-opa rule, which stands
   for bitwise disjunction. The idea is to enforce transitive unfolding by merging the
   definition's unfolding vector into the running vector." The relation is deterministic.

**What breaks without transitivity.** The introduction: "Implicit unfolding of transitive
dependencies as above is used by Agda to ensure subject reduction. Suppose, for example, that
we wrote a new definition unfolding 0ℤ without transitively unfolding ℤ. In that definition's
body, 0ℤ of type ℤ would reduce to (0 , 0) of type ℕ × ℕ, but we would not be able to deduce
that ℤ is equal to ℕ × ℕ!" Formally, Counterexample 5.13: with the merge replaced by
"φ ⊔ φ′ = φ", there is a well-formed ∇ whose transparentisation isn't well-formed. Their
context is `opaque N : U` followed by `opaque (unfolding the first) 0 : α₀`; the unfolding
vector `01` makes the second transparent but not the first, and "The resulting transparentized
context is ill-formed: we cannot show that 0 : α₀, because we cannot deduce that α₀ ≡ N." They
add that "Gratzer et al. [7] observe that subject reduction is lost with non-transitive
unfolding; we see a similar result" (§5.1). (Strictly, what fails in their system is
well-formedness preservation, not Theorem 5.11: "Most of our results actually hold with either
of the two definitions of ⊔", but a checker would then have to re-check the whole
transparentised context, which "seems terrible from a performance perspective", and
"the problem can be avoided entirely through the use of transitive unfolding".) In Stitchwort
words the counterexample is:

```stitchwort
opaque def Code: Type := Nat
opaque def start: Code unfolding Code := 0
-- A declaration that unfolds `start` but not `Code` would see `start` compute to `0: Nat`
-- while its type `Code` stays stuck: the body no longer fits the type.
```

which is why `unfolding start` must mean `unfolding start, Code` (§6.3).

**What they prove**, for the system with transitive unfolding:

- Theorem 5.11 (Subject Reduction): "If ∇ » Γ ⊢ t ⇒ u : A and ∇ » Γ ⊢ t : A, then ∇ » Γ ⊢ u : A."
- Theorem 5.12 (Well-formedness Preservation): "Given φ » ∇′ ⇝ ∇, if » ∇, then » ∇′, and if
  ∇ » Γ ⊢ J, then ∇′ » Γ ⊢ J." Unfolding more never breaks what already checked.
- Theorems 5.22 and 5.23 (Consistency; Definition Consistency): ⊥ is uninhabited in the empty
  context, and "No definition in a well-formed definition context has the empty type ⊥."
- Theorems 5.24 to 5.27: normalisation to weak head normal form, decidable conversion, and
  decidable type checking for a "checkable" fragment.
- Definition 5.14: "A term is neutral if it has either a variable or an opaque definition in
  its head position", and "neutrals blocked on opaque definitions have more or less the same
  reduction semantics as neutrals blocked on variables" (§5.2). §6.4 borrows that wording.

**A consequence worth knowing.** Canonicity is stated only for the fully transparent
("glass") context, "to avoid situations where a term is stuck on an opaque definition"
(Theorem 5.19), and Counterexample 5.21 shows a proof `eq : Id ℕ x 0` (by `unfolding x`) where,
with `x` opaque, `x` and `0` aren't judgementally equal. So a closed term of a data type need
not compute to a constructor while checking. Stitchwort already lives with that: `J` "with any
other proof … is stuck. In a closed term that can still happen", for quotient proofs
(docs/core.md, Equality) **[checked]**. Any checker code that assumes closed means canonical
must treat a stuck opaque call like a variable. **[inferred]**

**What the paper doesn't cover**, so what Stitchwort still owns **[inferred]**:

- *Their calculus isn't Stitchwort's.* No algebraic effects or handlers, no `case` trees with
  index unification, no quotients, no native numbers; grades are ignored in the text ("to some
  extent, supported in the formalization", §1); and equality reflection is supported "in the
  presence of definitions, but not opaque definitions".
- *Erasure.* Running erases proofs and types; checking never does (docs/core.md, Evaluation).
  The paper has no run-time semantics, so the claim that running with bodies agrees with
  checking without them is ours: it holds because opacity only removes equations while
  checking and changes nothing the runner does (§6.7).
- *Our conversion.* Stitchwort's conversion has shortcuts the paper's doesn't (folded
  dictionaries, stuck case trees compared by tree, eta, compact numbers). Each must treat an
  opaque head as a neutral, with no fallback to the body (§6.4).
- *Groups.* The paper has only top-level definitions in order, so the unfolding graph has no
  cycles. Stitchwort's mutual groups need the least fixed point of §6.11.
- *Scope of directives.* "We based the design on that of Agda, and do not support local
  definitions or expression-level unfolding directives: an obvious opportunity for further work"
  (§6), which fits D1264 (no `reveal` term).

So the paper turns the most uncertain part of draft 1 from inference into prior metatheory for
the opacity mechanism itself, but it is not a proof *of Stitchwort*.

**Gratzer et al.** [P2] justify the unfolding control Agda's is based on, by elaboration to a
core theory with extension types and a normalisation theorem; Danielsson and Geng note that
proof "does not seem to be mechanized" (§2).

**Why the kernel must agree with the elaborator** is in §6.4: Stitchwort's index unification
treats "stuck" and "conflict" differently, so a checker that could unfold `f` and one that
couldn't would disagree about which `case` branches exist.

## 6. The design

### 6.1 What it means

An opaque definition is checked like any other (its body against its type, its termination,
its effects), and then, **while checking other declarations**, it has a type and no body,
unless that declaration asks for the body. Running the program uses the body as always.

What is promised is **definitional opacity**: the body takes no part in conversion ("are these
two the same?"), so no comparison, `rfl`, `match` motive or `rewrite` search looks inside it.
It is not information hiding or a module boundary: the body is in the source, in the core
term, and in the statement of `f.unfold` (§6.3), and any proof may use that equation. A user
wanting an abstract type in the security sense should not read `opaque` that way; error
messages and docs/syntax.md say "opaque to the checker", not "private".

### 6.2 Syntax: a modifier on one definition

```stitchwort
opaque def generateLevel (depth: Nat): {Random} Plan :=
  …
```

- A modifier, like `export def` and `instance` (docs/syntax.md) **[checked]**, and like
  Scala 3's `opaque type` (cited in [microtypes.md](microtypes.md)) and Agda's `opaque`
  keyword. Not an attribute: [attributes.md](attributes.md) reserves bare `@[name]` for
  language-level attributes, so `@[opaque]` would also fit, but opacity changes what the
  kernel accepts and is part of the definition's identity (§6.6), which makes it a property
  of the declaration rather than metadata about it. **[inferred]**
- **Per definition, no blocks.** Agda needs blocks because an opaque definition there can
  depend on another one's body in the same block; Stitchwort can say that with `unfolding`
  on the dependent definition (§6.3). A block form can come later if a real program wants
  one; none does today. Definitions that call each other are still checked together as a
  group; how opacity works there is §6.11.
- `opaque` becomes a keyword. Two example files use it as a name
  (`examples/reject/omega-opaque-atom.sw`, `examples/reject/let-effectful-opaque.sw`); they are
  renamed (no backwards compatibility, as usual).
- **The `opaque` modifier** is allowed on `def` (with or without parameters, effectful or not,
  `decreasing` or not). `opaque theorem` is refused: theorems already stay folded, and a
  proof's body is never needed except by `J` and `case`, which are rare. `opaque instance` is
  refused: a dictionary that can't be taken apart can't be used.

Draft 1 described the `opaque` modifier here and the `unfolding` clause in §6.3, each with its
own "allowed on" list, and the two lists were easy to read as one. Together:

| Declaration | `opaque` modifier | `unfolding f` clause |
|---|---|---|
| `def` | allowed | refused (`E-UNFOLDING-TRANSPARENT`): write `opaque def`, or use `rewrite f.unfold` |
| `opaque def` | (is one) | allowed |
| `theorem` | refused | allowed; the theorem then stays stuck under `case` and `J` too |
| `instance` | refused | refused |

### 6.3 How a proof gets the body back: `unfolding` on the declaration

```stitchwort
theorem generateLevelDepth (depth: Nat) (seed: Nat):
    (seeded seed (() => generateLevel depth)).level.depth = depth
    unfolding generateLevel
  := …
```

- Written after the signature, where `decreasing` goes today (docs/syntax.md, the
  `decreasing n` clause of `Nat.digitsAcc`) **[checked]**: one place for "how to check this
  declaration". Several names: `unfolding generateLevel, randomRoom`.
- Within that declaration's **body**, the named definitions unfold as usual; its type is
  checked without them, as Agda never reduces opaque definitions in type signatures. This is
  Agda's `unfolding` clause, on a single declaration rather than a block.
- **The `unfolding` clause is allowed on `opaque def` and on `theorem` only** (the table in
  §6.2). A declaration with `unfolding f` is itself never unfolded by a declaration that
  doesn't unfold `f` (for a theorem: a `case` or `J` on it stays stuck, like Rocq's `Qed`), and
  unfolding it unfolds `f` too (Agda's transitivity). On a plain `def` it's refused
  (`E-UNFOLDING-TRANSPARENT`: "a definition that unfolds others must be `opaque`, or use
  `rewrite f.unfold`"), because a transparent definition unfolds everywhere, including where
  `f`'s body isn't known: Danielsson and Geng's counterexample (§5). The precise rule is the
  kernel invariant of §6.4.
- An opaque definition whose own body calls another opaque one doesn't see that one's body
  either, unless it says `unfolding` too.
- **A transparent definition may still `rewrite f.unfold`.** `def g … := … rewrite f.unfold …`
  is fine although `g` unfolds everywhere: its body uses `f`'s body only through an explicit
  equality proof, a term (`f.unfold x`) whose type checks with nothing unfolded. Unfolding `g`
  where `f` is hidden reproduces that proof term, which still has its type there. A hidden use
  in conversion is what `unfolding` would add, and it would not survive the trip. **[inferred]**
- **A generated equation as well.** Every opaque `f` gets `f.unfold`, a theorem
  `f.unfold (x…): f x… = body`, proved by `rfl` with `unfolding f`, so most proofs can
  `rewrite f.unfold` and never unfold anything themselves. The name is the one `decreasing`
  already generates (docs/core.md, "Recursion on a measure") **[checked]**, and the role is
  Lean's `f.eq_def` and Isabelle's `f_def` ([§4](#4-how-other-languages-do-it)). For a
  definition by pattern matching the right-hand side is the `match`, as written.
- **`f.unfold` exists only when its statement makes sense outside.** Like every type, its
  statement is checked with nothing unfolded. For an `f` with no `unfolding` clause that always
  works (the body already checked against `f`'s type without unfolding anything). For one with
  a clause it may not: in §5's `opaque def start: Code unfolding Code := 0`, the statement
  `start = 0` compares a `Code` with a `Nat`, and with `Code` hidden that's ill-typed (the
  paper's "interface" warning, Definition 5.8). Then no `start.unfold` is generated, and naming
  it is `E-NO-UNFOLD-EQUATION` ("`start.unfold` can't be stated without unfolding `Code`; prove
  what you need in a theorem with `unfolding start`"). Decided here, not a decision: it's forced
  by the type rule, and the error only replaces a confusing "not found". **[inferred]**
- **Its size.** The statement contains the whole body, so for `generateLevel` it's a large
  term. Generating it costs one more linear pass over the body (the kernel checks the
  statement is a type; the hash walks it once), with nothing unfolded. It must cost nothing
  more: no read-back of it when unused, and printed by name (`Rogue.generateLevel.unfold
  depth`), never by statement, in goals and errors. For comparison, `decreasing`'s `f.unfold`
  is generated **eagerly**, when `f` is checked (`crates/elab/src/decreasing.rs`,
  `decreasing_unfold`: `kernel::declare_def` then `define_group`), but its statement is small,
  `f x c = f.%step x (y c' => f y c') c`, because the body lives in the generated `f.%step`
  **[checked]**. The tests in §9 lane 2 check the dormant cost; if they show more than the one
  pass, `f.unfold` switches to that shape (`f x = f.%body x`, with `f.%body` a generated
  transparent copy of the body), which is possible for an `f` with no `unfolding` clause.
  Decided here as a build detail.
- **Not a `reveal` term inside a proof** (Dafny's `reveal f;`). A local reveal needs the
  kernel to change what a name means part-way through a term, a new kind of core term; the
  declaration-level clause needs only a per-declaration list. A proof that wants the body for
  one step can put that step in a small lemma with `unfolding`. **[inferred]**

### 6.4 Who enforces it: the kernel, too

The prototype settles the practical side: elaborator-only opacity doesn't fix the roguelike,
because the kernel then does the expensive comparison (§2.4). There are two more reasons.

- **One meaning.** If only the elaborator hid bodies, a proof could depend on unfolding
  without saying so (the kernel would accept it), and opacity would be advice, not a rule
  (Lean's `@[irreducible]` and Rocq's `Opaque` are like this, [§4](#4-how-other-languages-do-it)). DESIGN.md §2 principle 7
  ("one meaning per word").
- **The elaborator and kernel must agree on what is stuck.** A `case` on an indexed type is
  refused when index unification gets stuck, and a branch is impossible only on a constructor
  conflict ("Only a conflict makes a branch impossible; stuck never does", docs/core.md,
  Unifying indices) **[checked]**. If one side could unfold `f` and the other couldn't, one
  would find a conflict where the other is stuck, and the kernel would refuse what the
  elaborator built (a body on a branch it thinks impossible, or the reverse) **[inferred]**.

**The kernel invariant.** This is the rule the kernel enforces, and the heart of the
implementation. For a declaration `d`, write `U(d)` for the names in its `unfolding` clause.

1. **A fixed transparency set.** `d` is checked under one transparency set `T(d)`, computed
   before its body is checked and never changed while checking it. `T(d)` is the closure of
   `U(d)`: the least set that contains `U(d)` and, for each opaque `g` it contains, all of
   `T(g)` (and, by §6.11, `g`'s opaque group-mates). This is Danielsson and Geng's merge of
   the unfolding vector (§5).
2. **Type outside, body inside.** `d`'s type is checked with the empty set (every opaque
   definition hidden); its body with `T(d)`.
3. **No escape.** If `U(d)` isn't empty, `d` is itself opaque (an `opaque def`, or a theorem
   that stays stuck even under `case` and `J`). So `d`'s body is only ever unfolded inside a
   declaration whose set contains `d`, and by (1) that set then contains all of `T(d)`: `d`
   can never become definitionally transparent where something it unfolds is hidden. Without
   this rule a transparent `d` would carry its privilege everywhere, which is §5's
   counterexample.
4. **Explicit equalities are not privileges.** A transparent `g` may use `f.unfold` (§6.3):
   that dependency is a proof term with a type that checks under the empty set, not a step
   of conversion.
5. **Running ignores it.** While a program runs every definition unfolds.

**How opaque calls compare.** An application whose head is an opaque definition not in the
current set is **neutral**, exactly like a variable applied to arguments (Danielsson and Geng's
Definition 5.14). Conversion compares two neutrals with the same head by comparing their
spines, argument by argument, and **never falls back to the body**; different heads, or a
neutral against a constructor, are not convertible. This replaces draft 1's "same name,
convertible arguments" (the review brief's "equal only if their arguments are"), which is
easy to misread once conversion has non-structural rules. Today's rules and what they mean here **[checked]** in
`crates/core/src/value.rs` (`conv_step`, `spine_pairs`) and docs/core.md:

- *Every argument is in the spine*, types and proofs included: `spine_pairs` pairs up every
  `App` in the two spines. Erasure happens only while running (docs/core.md, Evaluation:
  "`stitchwort run` and `stitchwort test` (never the checker) also **erase**"), so checking
  compares erased-at-run-time arguments like any others.
- *No definitional proof irrelevance*: "two different proof terms aren't automatically equal"
  (docs/core.md, Equality). So `f p₁` and `f p₂` for different proofs `p₁`, `p₂` of the same
  proposition are not convertible when `f` is opaque, even if `f`'s body ignores its proof.
  That is the same answer as for any stuck call today, and the fix is the usual one (prove
  `f p₁ = f p₂` by `rewrite f.unfold`, or with `unfolding f`). If Stitchwort later adds
  definitional proof irrelevance, spine comparison inherits it: the neutral wording is chosen
  so that it will.
- *Eta* still applies around a neutral (`push_eta`), as for a variable.
- *The dictionary shortcut* (`is_folded`) compares the same folded dictionary by spine and, if
  that fails, "compared unfolded". An opaque head must not take that fallback, nor the stuck
  case-tree comparison (`same_stuck_trees`), which looks at bodies.
- *Index unification* in a `case` (docs/core.md, Unifying indices): an opaque call against a
  constructor is **stuck**, never a conflict, as for a variable. Conversion saying "not
  equal" and unification saying "stuck" are both the neutral reading.

How: the kernel's `Def` gets an `opaque` flag, each declaration submitted to the kernel
carries its `unfolding` list (the kernel computes the closure), and `unfold_now` and the
zero-argument arm of `eval_step` return the folded call for an opaque definition not in the
current set, unless a program is running. The prototype is exactly that, about 25 lines
(§7.3); the shortcut paths above are the part the prototype didn't audit.

### 6.5 Soundness

Opacity can only make **fewer** things equal, never more, so it can't make a false statement
provable. [§5](#5-is-it-sound-the-metatheory) gives the metatheory: Danielsson and Geng's
mechanised results for an Agda-style design with the same two rules, with the caveats there
about what their calculus leaves out. In Stitchwort terms
**[inferred]**: an opaque `f` behaves in the kernel like a variable of `f`'s type that is
bound outside the declaration. Any proof the kernel accepts with `f` opaque is a proof about
an arbitrary function of that type, so it is also a proof about the real `f`; and the
definition itself was checked with its body, so `f` exists (no empty type is assumed into
being). Nothing is added to the trusted rules, so `stitchwort axioms` reports nothing new.

### 6.6 Hashing: opacity is part of the hash

DESIGN.md §2 principle 5: a definition is identified by its *whole elaborated declaration*;
`def_hash` already hashes `theorem` and `instance` (`crates/core/src/hash.rs`, `def_hash`)
**[checked]**. Opacity changes what the kernel accepts about *other* declarations, so:

- `f`'s hash includes its `opaque` flag, so making `f` opaque or transparent changes the hash
  of `f` and of everything that uses it. That keeps the kernel-check cache exact: a cached
  "accepted" for a user of `f` was computed under the same opacity.
- A declaration's `unfolding` list is hashed with it: it changes what the kernel does with
  that declaration. Two declarations checked under different conversion relations must not
  share a hash.
- **What is hashed is the list as written, not its closure.** Each name is hashed as the
  referenced declaration's hash, as any reference is (hash.rs: "A reference to another
  declaration is hashed as that declaration's hash"); the list is put in a canonical order (by
  those hashes, duplicates dropped), so writing `unfolding a, b` or `unfolding b, a` doesn't
  change it. The closure `T(d)` is a function of the referenced declarations, whose hashes
  cover their own flags and lists, so hashing it as well would add nothing. In a group (§6.11)
  each member's flag and list are part of its full declaration, and so of the group's hash and
  of the member's *shape* that orders the group.
- Unlike the dictionary and theorem folding (§3), which is deliberately *not* hashed because
  it never changes what is equal.

Content hashes change only for declarations that use the new forms; the existing snapshots
don't move.

*Remark, not a plan.* Making `f` opaque changes no run-time code, yet changes `f`'s hash and so
every dependant's, which also invalidates cached test results and builds. The reviewer
suggested a possible later split into a *checking identity* (what the kernel accepted, which
includes opacity) and a *running identity* (what code runs, which doesn't). That is a cache
architecture change, not a reason to leave opacity out of the definition's identity, and
nothing in this note depends on it; it's recorded here in case test re-runs after opacity
changes ever become a cost worth a ticket.

### 6.7 Running, JavaScript, tests and the automatic tools

| | Effect of `opaque` |
|---|---|
| `stitchwort run`, `run --js`, `build --js` | None. The body runs; erasure is unchanged. |
| `test` | None: tests run with the program evaluator. Shown in the prototype: all 99 roguelike tests pass with `generateLevel` opaque **[run]**. |
| Counterexample search | None: it evaluates under `erasure.running()` (`counterexample/mod.rs:635`), so it still finds counterexamples about an opaque function's real behaviour. A counterexample can therefore be shown for a statement the proof can't use the body to disprove; the message should say the definition is opaque. |
| `rfl` | Doesn't see through `f`. `f 3 = 7` needs `unfolding f` or `rewrite f.unfold`. |
| `decide`, `auto`, `if` on a proposition | A decision procedure computes as before; a proposition about `f x` stays stuck where it needs `f`'s value. |
| `omega` | Treats `f x` as an atom, as it already does with anything it can't read. |
| `match e:` and `rewrite` | Never look inside `f`: the reason for the feature. |
| Goals and messages | Show `f x` as written. |

### 6.8 Definitions with `decreasing`: stay transparent

Lean 4.9 made definitions by well-founded recursion irreducible by default ([§4](#4-how-other-languages-do-it)).
Its reason doesn't apply here: Lean's well-founded definitions unfold through a proof of
well-foundedness, which is slow and fragile to compute, while Stitchwort compiles `decreasing`
into structural recursion on a native-number fuel, which computes quickly
(well-founded-recursion.md §0: "`Nat.digits` of a 30-digit number takes 30 steps"). And proofs
rely on it: `std/Nat/Digits.sw` has `theorem Nat.digitsExample: Nat.digits 1205 = [1, 2, 0, 5]
:= rfl`, about a `decreasing` definition (`Nat.digitsAcc`). **[checked]** So: transparent by
default, `opaque def … decreasing m` when wanted.

### 6.9 Zero-argument constants: not opacity

Making `maxHitPoints` opaque would fold it in goals, but breaks proofs that need its value. In
the prototype, today's roguelike with `Rogue.maxHitPoints` opaque fails `healedAtMost`
("`Nat.leq Rogue.maxHitPoints Rogue.maxHitPoints` and `True` aren't equal") and
`startingValid`. **[run]** What goals need there is a display change: keep the name, unfold when
something looks (a glued zero-argument call). That is SW-501, and stays separate.

### 6.10 Error messages

When a check fails where a step would have needed an opaque body, say so and name the fix.
The evaluator can record which opaque definitions it declined to unfold during the failing
comparison (only on the error path), and the message adds a note:

```text
[E-REFL] Error: `rfl` can't prove this
   │ theorem levelDepth … := rfl
   │                         ─┬─
   │                          ╰── `(seeded seed (() => Rogue.generateLevel depth)).level.depth` and `depth` aren't equal
   │
   │ Note 1: `Rogue.generateLevel` is opaque, so its body isn't used here
   │ Note 2: add `unfolding Rogue.generateLevel` after this theorem's signature, or rewrite with `Rogue.generateLevel.unfold`
```

The same note for `E-TYPE-MISMATCH`, `E-REWRITE-NOTHING` (when the pattern occurs only inside
an opaque body), `E-AUTO-STUCK`, `E-INDEX-STUCK` and the counterexample note. `unfolding g`
where `g` isn't opaque is an error (`E-NOT-OPAQUE`: "`g` isn't opaque, so it always unfolds;
remove it from `unfolding`"), so the list stays honest.

### 6.11 Definitions checked together

The paper has only top-level definitions in order (§5), so its unfolding graph can't have a
cycle. Stitchwort has groups. What it has today **[checked]**:

- **Mutual groups.** "The elaborator collects each declaration's free references …, splits the
  declarations into strongly connected components and checks them in dependency order"; "A
  component of several definitions, or of one that calls itself, is one group" (docs/core.md,
  The elaborator's groups). The kernel takes a group in one `define_group` call, and "Every
  body is checked with every member opaque: none has a body until all are accepted"
  (`crates/core/src/check.rs`, `define_group`). There is no user-written `mutual` block.
- **Hashing.** A group of two or more "is hashed as a unit": members in a canonical order by
  *shape*, "each member's hash is the group's hash and its index" (`crates/core/src/hash.rs`).
- **`decreasing`** refuses mutual groups (`E-DECREASING`: "… a mutual group …", docs/core.md
  error table), so its generated declarations (`f.%go`, `f.%step`, `f.%irrel`, `f.unfold`, …)
  are never part of a user's cycle.
- **Data groups** can't contain definitions (`E-MUTUAL-KIND`), so opacity never meets them.

The rules, all following from the invariant of §6.4:

1. **Opacity is per member.** Each member is `def` or `opaque def` as written; a group may mix
   them. That is sound because, while the group is checked, *every* member is already opaque
   to every other (the `define_group` rule above), so no member's body can depend on another's
   unfolding; a transparent member just unfolds afterwards to a body that may contain stuck
   calls of an opaque one, as `isEven n` would unfold to a stuck `isOdd (n - 1)`.
   **[inferred]**
2. **A member can't unfold a group-mate.** `unfolding g` adds an edge `d → g` to the
   dependency graph the elaborator splits into components, so `g` is checked first. If `g` also
   refers to `d`, they are one component, `g` has no body while `d` is checked, and the clause
   is refused: `E-UNFOLDING-GROUP` ("`isEven` can't unfold `isOdd`: they are checked together,
   so neither has a body yet; prove it in a theorem after both"). So `unfolding` only ever
   names declarations that are already final, and the graph of `unfolding` clauses between
   groups is acyclic, as in the paper.
3. **Unfolding one opaque member unfolds its opaque group-mates** (D1267). Under that rule a
   cycle *does* appear, inside one group (`isEven` brings `isOdd`, which brings `isEven`), and
   the clause of rule 1 in §6.4 is a **least fixed point**: start from `U(d)`; repeatedly add,
   for every opaque `g` in the set, `T(g)` and `g`'s opaque group-mates; stop when nothing
   changes. It terminates because the set only grows within the finite set of declarations
   checked so far, and the result is unique. Computed once per declaration, when it's
   submitted, and stored with it. Without D1267, rule 3 goes away and the closure is the same
   definition with no group term.
4. **Hash.** Each member's `opaque` flag and written `unfolding` list are part of its full
   declaration, so part of its shape, the group's hash and every member's hash (§6.6). Group
   membership is already in the hash, so rule 3 needs nothing more.

## 7. Worked example: the roguelike, generating on the stairs

### 7.1 The program

`resolve` as it was before stage 2's workaround, with `generateLevel` opaque:

```stitchwort
-- Making levels. Opaque: no proof needs to look inside the generator, and
-- turns run it on an unknown seed (see the note on `descend`).
opaque def generateLevel (depth: Nat): {Random} Plan :=
  … unchanged …

def descend (dice: Dice) (state: State): State :=
  let plan := seeded dice.seed (() => generateLevel (state.level.depth + 1))
  let arrived := arrive state plan
  { arrived | turn = state.turn + 1, message = "You go down to level ${plan.level.depth}." }
```

`State.below` and the level-making in `newGame` go away.

### 7.2 The proofs

`stepValid` is unchanged, word for word. The four descent lemmas no longer split on
`state.below`; each applies the lemma that already holds for every plan:

```stitchwort
theorem descendOutOfWalls (dice: Dice) (state: State) (inside: isWall state.level state.player = False):
    isWall (descend dice state).level (descend dice state).player = False :=
  startOnFloor (seeded dice.seed (() => generateLevel (state.level.depth + 1))).level
```

None of them says `unfolding`: the invariants hold whatever the generator planned, because
`arrive` re-checks the placements. That is the point: the proofs were already independent of
the generator's body, and opacity lets the checker know it.

### 7.3 The prototype

What I ran, on a scratch copy of `games/rogue` with §7.1's `descend` (keeping `State.below`
unused, to change as little as possible) and the four lemmas above:

- A scratch patch to `value.rs` (not committed): definitions named in an environment variable
  never unfold unless a program is running, in `unfold_now` and in `eval_step`'s
  zero-argument arm; a second variable limits it to the elaborator (glue on). Two further
  scratch switches: one keeps gluing on in the kernel and compares two calls of the same
  definition by their arguments first; one makes `match` and `rewrite` read back folded.
- Results, all `check --no-cache` (the table in §2.4): opaque in both, the whole project
  checks in 4 s, with `stepValid`, `stepAtMost`, `stepOutOfWalls`, `stepOnFloor`,
  `stepClear` and `seededStep` unchanged. **[run]**
- `test` on the copy: 91 of 99 pass. The 8 failures are the scripted 232-turn game, its frame
  and the stairs test, which pin the levels and messages that pre-made levels produce; levels
  made from the turn's seed differ, so those tests would be re-recorded in a real change. Today's
  game with `generateLevel` opaque passes 99 of 99. **[run]**

## 8. Fix the checker anyway

There are three separate things here, and only the third is language design:

| | What | Kind |
|---|---|---|
| 1 | The kernel compares `f a` with `f b` by comparing `a` with `b` before unfolding `f` | checker engineering |
| 2 | The elaborator's read-back doesn't explode under branches that can't step | checker engineering |
| 3 | A programmer marks a body as none of the proofs' business (`opaque`, `unfolding`) | language semantics |

The measurements keep them apart: 1 alone takes the descent lemma from over 60 s to 1 s but
leaves the four `resolve…` theorems failing; 3 alone fixes both, but only because the
generator's body really is irrelevant (§2.4) **[run]**. Opacity must not become *the* fix for
expensive evaluation: users shouldn't need to mark ordinary functions `opaque` because the
checker picks a bad evaluation order, and a definition whose body proofs do need (most of
`std`) can't be marked anyway. So 1 and 2 are fixed on their own, whatever happens to
D1263, and no `std` or AoC definition is made opaque as a performance workaround.

The two weaknesses of §2 hurt programs that do want their bodies seen, so they're worth
fixing independently (implementation choices, so no decisions below; each is a lane in §9):

1. **Kernel: compare two calls of the same definition by their arguments first**
   (folded-calls.md §7 stage 4). Sound by congruence (same function, equal arguments, equal
   results), and when it fails the comparison falls back to today's. It needs the kernel to
   keep calls as calls (glued), which is a change inside the trusted code, so it deserves its
   own review. The prototype shows the gain on the roguelike's descend case: 1 s against more
   than 60 s. **[run]**
2. **Elaborator: don't read back inside the branches of a stuck `if` (or any stuck call)
   when building a motive or searching for a rewrite**, unless the expression being replaced
   occurs there. A design is needed (read back folded first and unfold only the calls whose
   unfolding contains an occurrence; or bound the read-back and fall back), measured against
   `std` and AoC, since the folded read-back alone breaks `std/Result/Result.sw` **[run]**.
   *Speculative:* the first option is how smalltt's approach would extend; I haven't tried it.

## 9. Build plan

Each lane is one stage, with `task test:lane` for its area and the merge gate at merge.

1. **Kernel: opaque definitions.** `Def::opaque`, the per-declaration `unfolding` list in the
   kernel's entry points, the closure `T(d)` as a least fixed point (§6.4, §6.11), the
   evaluator rule (unfold only while running or when in the set), opaque heads as neutrals
   in every conversion path with no fallback to the body (the dictionary and stuck-tree
   shortcuts included, §6.4), the invariant of §6.4 (type checked with the empty set; a
   declaration with `unfolding` stays opaque; refused on a plain `def`), hashing of the flag
   and of the written list in canonical order, `E-NOT-OPAQUE`. Kernel tests in the "must
   reject" style:
   - an `rfl` through an opaque definition is refused; the same with `unfolding` is accepted;
   - §5's counterexample: a declaration unfolding `start` sees `Code` unfolded too (accepted),
     and no route gives it `start` without `Code`;
   - a type that needs an unfolding is refused even when the body lists it;
   - an opaque head against a different head, and against a constructor: not convertible;
     in index unification, stuck rather than a conflict;
   - two calls of an opaque `f` with different proof arguments: not convertible;
   - groups: a mixed group checks; unfolding one opaque member of a two-member cycle
     unfolds the other (if D1267) and the closure terminates; `unfolding` a group-mate is
     `E-UNFOLDING-GROUP`; a chain `a` unfolds `b` unfolds `c` gives `c` to `a`;
   - hashes: a cached acceptance doesn't survive a change of opacity or of an `unfolding`
     list; reordering a list doesn't change the hash; changing a group member's opacity
     changes every member's hash.
2. **Surface: `opaque def` and `unfolding`.** Lexer keyword, parser, formatter, elaborator
   wiring (`unfolding` names as dependency edges), `f.unfold` generation and
   `E-NO-UNFOLD-EQUATION`, the refusals in §6.2's table, `E-UNFOLDING-GROUP`, the two renamed
   examples, docs/syntax.md (saying "opaque to the checker", §6.1),
   `examples/accept/opaque-*.sw` and `examples/reject/opaque-*.sw`. **Size tests for
   `f.unfold`** (§6.3), on a scratch copy of the roguelike with `generateLevel` opaque,
   comparing evaluation steps and core term nodes (`STITCHWORT_TIMINGS=decls`) with and
   without the equation:
   - generating `generateLevel.unfold` costs at most one linear pass over the body (no
     evaluation steps inside it);
   - a project that loads it and never uses it checks with no extra read-back;
   - one `rewrite Rogue.generateLevel.unfold` reads back only the goal it rewrites;
   - an error whose goal mentions it prints `Rogue.generateLevel.unfold depth`, by name.

   If any of these shows the body being traversed beyond the one pass, switch `f.unfold` to
   the `f.%body` shape of §6.3 in the same lane.
3. **Messages.** The "is opaque" notes of §6.10 on `E-REFL`, `E-TYPE-MISMATCH`,
   `E-REWRITE-NOTHING`, `E-AUTO-STUCK`, `E-INDEX-STUCK` and the counterexample note; snapshot
   tests.
4. **The roguelike, generating on the stairs** (§7), with its NOTES updated: removes
   `State.below` and the workaround's comments. Re-record the scripted game.
5. **Kernel arguments-first comparison** (§8.1), measured with `task bench` and the AoC
   check; independent of 1 to 4.
6. **Elaborator read-back for `match` and `rewrite`** (§8.2): a short design note first
   (design review gate), then a lane.

Lanes 1, 5 and 6 can start in parallel; 2 needs 1; 3 and 4 need 2.

## 10. Decisions

- **D1263. Add opaque definitions, as an `opaque def` modifier on single definitions (no
  blocks), enforced by the kernel as well as the elaborator?** Context: an opaque definition
  is checked as usual and runs as usual, but other declarations see only its name and type.
  The roguelike's stage-2 design (making a level on the stairs, inside the turn) checks in 4 s
  with the generator opaque in both, and still hangs with it opaque in the elaborator only.
  Opacity can only make fewer things equal, so it can't make a false theorem provable, and a
  mechanised paper (Danielsson and Geng) proves an Agda-style design with the same rules
  sound. Lean's kernel has opacity too, but it can't be reopened; Stitchwort's would be
  reopenable per declaration. It's opacity to the checker only: the body is still visible
  (`f.unfold` states it). An external review recommended going ahead. **Recommendation: yes.**
- **D1264. A declaration that needs an opaque definition's body says `unfolding f` after its
  signature (Agda's way), rather than a `reveal f` step inside the proof (Dafny's way)?**
  Context: the clause applies to the declaration's body, like `decreasing` it goes after the
  signature, and the kernel only needs a list per declaration; a step inside a proof would need
  a new kind of core term. Allowed on theorems and opaque definitions, which then stay opaque
  themselves (Agda's rule, which keeps the theory safe; Danielsson and Geng show what goes
  wrong without unfolding being transitive). A proof that wants the body for one step puts it
  in a small lemma. The paper, like Agda, has only declaration-level unfolding and leaves the
  expression-level kind as future work. **Recommendation: yes.**
- **D1265. Generate `f.unfold`, the equation `f x = body`, for every opaque definition?**
  Context: then most proofs `rewrite f.unfold` instead of unfolding, as Lean (`f.eq_def`) and
  Isabelle (`f_def`) do; `decreasing` definitions already get an `f.unfold`. It costs one
  generated theorem per opaque definition. Draft 2 adds two details: no equation where its
  statement can't be written without unfolding something (§6.3), and size tests (§9 lane 2).
  **Decided: yes** (Matt, as a build detail).
- **D1266. Keep `decreasing` definitions transparent by default, unlike Lean, which made
  well-founded definitions irreducible in 4.9?** Context: Lean's reason (unfolding through a
  well-foundedness proof is slow and fragile) doesn't hold here, because `decreasing` compiles
  to fuel that computes quickly, and `std` proves `Nat.digits 1205 = [1, 2, 0, 5]` by `rfl`.
  **Decided: yes, keep them transparent** (Matt, as a build detail).
- **D1267. When a declaration unfolds one opaque member of a group of definitions that call
  each other, does it get the group's other opaque members too?** Context: functions that call
  each other (`isEven` and `isOdd`) are checked together as one group, and each can be marked
  `opaque` separately. Proofs about one usually need the other's body as well; Agda does it
  this way ("Unfolding any name in an opaque block will cause any of the other names in that
  block to be unfolded as well"). The alternative is to name each one (`unfolding isEven,
  isOdd`). Both are sound; the first makes a group behave as one unit, as it already does for
  hashing. **Recommendation: yes, unfold the whole group's opaque members together.**

Decided in the note rather than raised (build details or forced by soundness): opacity per
member with mixed groups allowed, and `unfolding` of a group-mate refused (§6.11); the
closure as a least fixed point, and hashing the written list rather than the closure (§6.6);
no `f.unfold` when its statement needs an unfolding (§6.3); the `f.%body` fallback for
`f.unfold`'s size (§6.3). D1268 and D1269 are unused.

## 11. Review

An external reviewer read a brief of draft 1 (a self-contained page, not this note) and
recommended approving it "with relatively minor revisions". Each point, checked against the
sources before use:

| # | Reviewer's point | What changed in draft 2 | Agreed? |
|---|---|---|---|
| 1 | Danielsson and Geng's full text supports the two rules: counterexample for non-transitive unfolding, the merge, subject reduction and well-formedness preservation | §5 rewritten from the full text, with quotes, theorem numbers and the counterexample in Stitchwort syntax; caveats about effects, erasure, our conversion and groups kept | Yes. One refinement: their formal Counterexample 5.13 is to well-formedness preservation (Theorem 5.12); the introduction, and Gratzer et al. as they cite them, frame it as subject reduction, and they note "Most of our results actually hold with either" variant. The conclusion (transitivity is needed) is the same |
| 2 | Kernel enforcement is right; Lean's `opaque` is kernel opacity, so Lean is precedent, just not reopenable | §4 Lean paragraph and table: `opaque` row, quoted from the Lean reference rather than the thesis the reviewer linked; summary and D1263 say so | Yes |
| 2 | Agda's manual says "handled entirely at the elaborator level" | Confirmed on the manual page (not the PDF dump); Agda row corrected | Mostly. The sentence contrasts Agda with Gratzer et al.'s extension types, so it says less about kernels than the reviewer read into it; the conclusion (Agda isn't precedent for a separate kernel) stands |
| 3 | State the kernel invariant explicitly | §6.4, "The kernel invariant", five numbered rules | Yes |
| 3 | Explain why a transparent `g` may `rewrite f.unfold` | §6.3 bullet and invariant rule 4 | Yes |
| 4 | Declaration-level `unfolding` over `reveal`; the paper also leaves expression-level unfolding as future work | Quoted in §5; D1264 context | Yes |
| 5 | Say opacity is definitional, not information hiding | §1, §6.1, summary, D1263; docs wording in §9 | Yes |
| 5 | `f.unfold`'s type contains the whole body; test it stays dormant | §6.3 size bullet; four tests in §9 lane 2; notes `decreasing`'s eager generation with a small statement | Yes. Draft 2 also found a gap neither draft 1 nor the review mentioned: `f.unfold`'s statement may not type-check outside when `f` has an `unfolding` clause (§6.3) |
| 6 | Contradiction between "allowed on theorem" and "refused on theorem" | The brief merged two lists; the note had them in different sections (the `opaque` modifier in §6.2, the `unfolding` clause in §6.3) but they were easy to conflate. Now one table in §6.2 | Yes, as an ambiguity rather than a contradiction in the note |
| 7 | Specify opaque calls as neutrals with spine comparison | §6.4, with how Stitchwort's conversion treats proofs (no definitional irrelevance), erased arguments (not erased while checking), eta, the dictionary and stuck-tree shortcuts, and index unification | Yes |
| 8 | Hash both opacity and the `unfolding` list; maybe later split checking identity from running identity | §6.6: written list hashed in canonical order, closure not hashed; the split as a remark | Yes; the split stays a remark, as suggested |
| 9 | Keep the two checker fixes separate from opacity; users shouldn't need `opaque` to dodge bad evaluation | §8 opens with the three-way table and that rule | Yes |
| 10 | Specify mutual definitions: per member or group, least fixed point, hash, tests | §6.11, D1267, kernel tests in §9 lane 1 | Yes. Stitchwort has no `mutual` blocks, only automatic groups, and pending members can't unfold each other, which makes most of it simpler than the question suggests |

Nothing the reviewer recommended was rejected.

## Sources

Read on 25 October 2026.

- [A1] Agda manual, "Opaque definitions": <https://agda.readthedocs.io/en/latest/language/opaque-definitions.html> (2.10.0 documentation; the "stable" page, 2.8.0.2, has the same "entirely at the elaborator level" sentence: <https://agda.readthedocs.io/en/stable/language/opaque-definitions.html>)
- [A2] Agda 2.6.4 release notes: <https://github.com/agda/agda/blob/master/doc/release-notes/2.6.4.md>
- [A3] Agda manual, "Abstract definitions": <https://agda.readthedocs.io/en/latest/language/abstract-definitions.html>
- [A4] Agda issue #6354, "`opaque`: use-site control of unfolding": <https://github.com/agda/agda/issues/6354>; implementation PR #6628: <https://github.com/agda/agda/pull/6628>
- [L1] Lean API, reducibility attributes: <https://lean-lang.org/doc/api/Lean/ReducibilityAttrs.html>; transparency modes in `src/Init/MetaTypes.lean`: <https://github.com/leanprover/lean4/blob/master/src/Init/MetaTypes.lean>
- [L2] Lean API, `ReducibilityHints` (`Lean.Declaration`): <https://lean-lang.org/doc/api/Lean/Declaration.html>; also *Type Checking in Lean 4*: <https://ammkrn.github.io/type_checking_in_lean4/declarations/declarations.html>
- [L3] Lean reference, "Definitions", section "Opaque Constants": <https://lean-lang.org/doc/reference/latest/Definitions/Definitions/>
- [L4] Lean reference, "Theorems": <https://lean-lang.org/doc/reference/latest/Definitions/Theorems/>
- [L5] Lean v4.9.0 release notes (#4061 irreducible well-founded definitions, #4053 `seal`/`unseal`): <https://lean-lang.org/doc/reference/latest/releases/v4.9.0/>
- [L6] Lean reference, tactic reference (`unfold`, `delta`, `rw`): <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- [L7] Mathlib, `irreducible_def`: <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/IrreducibleDef.html>
- [R1] Rocq manual, "Controlling reduction strategies and the conversion algorithm" (`Opaque`, `Transparent`, `Strategy`, `Qed`): <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html>
- [I1] Idris 2 tutorial, "Modules and namespaces" (export modifiers): <https://idris2.readthedocs.io/en/latest/tutorial/modules.html>
- [F1] F\* wiki, "Qualifiers for definitions and declarations": <https://github.com/FStarLang/FStar/wiki/Qualifiers-for-definitions-and-declarations>
- [F2] F\* wiki, "Code pattern for hiding definitions from Z3 and selectively revealing them": <https://github.com/FStarLang/FStar/wiki/Code-pattern-for-hiding-definitions-from-Z3-and-selectively-revealing-them>
- [D1] Dafny reference manual (§6.4.4 function hiding, §8.20 `reveal`): <https://dafny.org/latest/DafnyRef/DafnyRef>
- [D2] Dafny attributes (`{:opaque}`, `--default-function-opacity`): <https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Attributes.md>
- [D3] Dafny, "Verification optimization": <https://github.com/dafny-lang/dafny/blob/master/docs/VerificationOptimization/VerificationOptimization.md>
- [H1] Liquid Haskell, specifications (`reflect`, `inline`, `measure`): <https://ucsd-progsys.github.io/liquidhaskell/specifications/>
- [S1] Isabelle tutorial source, definitions as rewrite rules: <https://isabelle.in.tum.de/repos/isabelle/comparison/751fde5307e4/doc-src/TutorialI/Misc/def_rewr.thy>
- [P1] N. A. Danielsson and E. Geng, "A Formalization of Opaque Definitions for a Dependent Type Theory", TyDe 2025, pp. 39–51, doi:10.1145/3759538.3759653: <https://conf.researchr.org/details/icfp-splash-2025/tyde-2025-papers/6/A-Formalization-of-Opaque-Definitions-for-a-Dependent-Type-Theory>, <https://research.chalmers.se/en/publication/549312>; full text (read for draft 2, converted with `pdftotext`; every page converted): <https://research.chalmers.se/publication/549312/file/549312_Fulltext.pdf>
- [P2] D. Gratzer, J. Sterling, C. Angiuli, T. Coquand, L. Birkedal, "Controlling unfolding in type theory", MSCS 35 (2025), arXiv:2210.05420: <https://arxiv.org/abs/2210.05420>
- [K1] smalltt README: <https://github.com/AndrasKovacs/smalltt>
- [U1] Unison, "Hashes" and "Unique types": <https://unison-lang.org/docs/language-reference/hashes>, <https://unison-lang.org/docs/language-reference/unique-types>

**Unverified:** whether Agda has any separate re-checking of opacity beyond what its manual
calls "the elaborator level" (draft 1's "no separate kernel" is now moot for this note: Agda
isn't used as precedent for kernel enforcement); whether Danielsson and Geng prove opaque
definitions conservative (I found no such theorem in the full text; they prove consistency,
definition consistency and the theorems listed in §5); how `irreducible_def` is built in the
kernel; the `[@@"opaque_to_smt"]` spelling (the wiki shows `[@"opaque_to_smt"]`). Resolved since
draft 1: which designs lose subject reduction (non-transitive unfolding, §5); whether Lean's
`opaque` has a way back in (no, [L3]).
