# Proposal: opaque definitions

**Status:** draft 1, 25 October 2026. Design only, nothing built. Ticket SW-505, decision
D1262 (Matt: write this note). Decisions D1263 to D1266 ([§10](#10-decisions)) are open.
Written against commit `11e029b2`. Related: [folded-calls.md](folded-calls.md) (glued calls,
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
  rule with a use-site opt-in; Lean's `@[irreducible]` binds only the elaborator, while its kernel
  can always unfold; Rocq's `Opaque` is a hint but `Qed` is final; Idris hides bodies per module;
  F\* and Dafny hide bodies from the SMT solver, with `reveal`. Danielsson and Geng (TyDe 2025)
  prove an Agda-like design consistent, and warn that some designs lose subject reduction.
- **The proposal** ([§6](#6-the-design)): `opaque def f …`, enforced by the elaborator and the
  kernel and part of `f`'s hash; a declaration that needs the body says `unfolding f`; every
  opaque `f` gets the equation `f.unfold`. Running, `--js`, tests and the counterexample search
  are unaffected. `decreasing` definitions stay transparent; zero-argument constants are a
  display fix (SW-501), not opacity.


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
- **Opaque**: a definition the checker treats as a name with a type and no body, so two
  calls are the same only if they are the same name applied to the same arguments. Running
  the program still uses the body.

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
because that was "much too coarse" (the design discussion, [A4]). *Unverified:* that Agda,
which has no separate re-checking kernel as far as I know, enforces this in its one checker.

**Lean 4: reducibility attributes, `seal`, irreducible well-founded definitions** [L1–L6].
`@[irreducible]`, `@[semireducible]` (the default) and `@[reducible]` set when the
elaborator's `whnf` and `isDefEq` may unfold a definition, by *transparency mode*:
`reducible` (used by `simp`, `rw` and instance search), `default` (ordinary checking, which
unfolds everything except `@[irreducible]`), and `all` (which unfolds even those).
**The kernel ignores these attributes**: its own reducibility hints "only affect performance
… but never prevent the kernel from unfolding a definition during type checking", and they
"are not related to the `@[reducible]`/`@[irreducible]`/`@[semireducible]`" attributes [L2].
What the kernel never unfolds is the separate `opaque` declaration kind, "not subject to
δ-reduction in the kernel" [L3]; it has no way back in. Theorems "are irreducible by default"
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
| Agda (`opaque`) | `opaque` block | block | everything outside the block, type signatures too | `unfolding f` at the start of another block (transitive) | no | one checker *(unverified: no separate kernel)* |
| Agda (`abstract`) | `abstract` block | block, by module | parent and sibling modules | only from another `abstract` block (coarse) | no | as above |
| Lean 4 | `@[irreducible]` | definition | elaborator at `default` transparency | `unfold f`, `rw [f]`, `unseal f in`, `with_unfolding_all` | `f.eq_def`, equation lemmas | **no** (hints only); only the `opaque` declaration kind is |
| Lean 4 (well-founded) | automatic since 4.9 | definition | as above | as above | yes | no |
| Rocq | `Opaque f`; `Qed` | constant | `Opaque`: tactics, and delays conversion; `Qed`: everything | `Transparent f`; never for `Qed` | no | `Opaque`: no (a delay); `Qed`: yes |
| Idris 2 | `export` (vs `public export`) | definition | other modules | none | no | n/a (per module) |
| F\* | `irreducible`; `[@"opaque_to_smt"]` | definition | normaliser and SMT; SMT only | `reveal_opaque` (SMT only) | no | n/a (SMT-based) |
| Dafny | `opaque` / `hide` | function | the verifier | `reveal f();` in a block | lemmas internally | n/a (SMT-based) |
| Isabelle | (default for `definition`) | constant | the simplifier | `unfolding f_def`, `simp only: f_def` | `f_def` | n/a (LCF kernel proves equations) |
| **Stitchwort (proposed)** | `opaque def` | definition | the elaborator and the kernel, outside running | `unfolding f` on the declaration (transitive) | `f.unfold` | **yes** |

What to take [inferred]: Agda's model (opacity as a real rule with an `unfolding` opt-in);
Lean's and Isabelle's equation (`f.eq_def`, `f_def`) as the everyday way in, which Stitchwort
already has a name for (`f.unfold`); Lean's lesson that elaborator-only opacity leaves the
kernel doing the work (what §2.4 measured); Rocq's `Qed` as the precedent for kernel-enforced
opacity of proofs. Not Dafny's `reveal`-in-a-block, which suits SMT verification, where the
cost is in what the solver is told, rather than a kernel that re-checks terms.

## 5. Is it sound? The metatheory

**Consistency.** Opacity makes fewer things equal. Danielsson and Geng (TyDe 2025, "A
Formalization of Opaque Definitions for a Dependent Type Theory") study "a type theory with
opaque definitions, inspired by Agda" and prove "subject reduction, normalization, consistency,
and decidability of conversion", mechanised in Agda [P1]. Gratzer, Sterling, Angiuli, Coquand
and Birkedal justify their unfolding control (which Agda's is based on) by elaboration to a
core theory and a normalisation theorem [P2]. In Stitchwort terms [inferred]: in the kernel an
opaque `f` acts as a variable of its type bound outside the declaration; a proof accepted that
way holds for every function of that type, so for the real one; and `f` itself was checked with
its body, so nothing is assumed into existence.

**The catch: subject reduction.** The same abstract warns that "subject reduction fails to hold
for certain designs" [P1]. I couldn't read which designs (the PDF didn't convert;
*unverified*). The risk is easy to see [inferred]: if a *transparent* `g` were checked with
`unfolding f`, then `g` unfolds everywhere, including where `f` is opaque, and its unfolding may
only make sense with `f`'s body known. Agda avoids this with transitivity (unfolding `y` also
unfolds what `y`'s block unfolds) and by never reducing opaque definitions in type signatures
[A1]. Stitchwort takes the same two rules (§6.3): `unfolding` applies to a declaration's body,
not its type; and a declaration that says `unfolding f` is itself opaque to anyone who doesn't
unfold it, and unfolding it unfolds `f` too. So `unfolding` is allowed on `opaque def` and on
`theorem` (theorems already stay folded unless a `case` or `J` takes them apart), and refused on
a plain `def`, which can use `rewrite f.unfold` instead.

**Why the kernel must agree with the elaborator** is in §6.4: Stitchwort's index unification
treats "stuck" and "conflict" differently, so a checker that could unfold `f` and one that
couldn't would disagree about which `case` branches exist.

## 6. The design

### 6.1 What it means

An opaque definition is checked like any other (its body against its type, its termination,
its effects), and then, **while checking other declarations**, it has a type and no body,
unless that declaration asks for the body. Running the program uses the body as always.

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
  one; none does today.
- `opaque` becomes a keyword. Two example files use it as a name
  (`examples/reject/omega-opaque-atom.sw`, `examples/reject/let-effectful-opaque.sw`); they are
  renamed (no backwards compatibility, as usual).
- Allowed on `def` (with or without parameters, effectful or not, `decreasing` or not). On a
  `theorem` it is refused: theorems already stay folded, and a proof's body is never needed
  except by `J` and `case`, which are rare. On `instance` it is refused: a dictionary that
  can't be taken apart can't be used.

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
- **Allowed on `opaque def` and `theorem` only.** A declaration with `unfolding f` is itself
  never unfolded by a declaration that doesn't unfold `f` (for a theorem: a `case` or `J` on it
  stays stuck, like Rocq's `Qed`), and unfolding it unfolds `f` too (Agda's transitivity). On a
  plain `def` it's refused (`E-UNFOLDING-TRANSPARENT`: "a definition that unfolds others must
  be `opaque`, or use `rewrite f.unfold`"), because a transparent definition unfolds
  everywhere, including where `f`'s body isn't known: the subject-reduction risk of §5.
- An opaque definition whose own body calls another opaque one doesn't see that one's body
  either, unless it says `unfolding` too.
- **A generated equation as well.** Every opaque `f` gets `f.unfold`, a theorem
  `f.unfold (x…): f x… = body`, proved by `rfl` with `unfolding f`, so most proofs can
  `rewrite f.unfold` and never unfold anything themselves. The name and the statement shape
  are those `decreasing` already generates (docs/core.md, "Recursion on a measure"; the same
  `f.unfold`) **[checked]**, and the role is Lean's `f.eq_def` and Isabelle's `f_def`
  ([§4](#4-how-other-languages-do-it)). For a definition by pattern matching the right-hand
  side is the `match`, as written.
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

How: the kernel's `Def` gets an `opaque` flag, each declaration submitted to the kernel
carries its `unfolding` list, and `unfold_now` and the zero-argument arm of `eval_step`
return the folded call for an opaque definition not on the current list, unless a program is
running. The prototype is exactly that, about 25 lines (§7.3). Conversion then compares two calls
of an opaque definition as it compares any stuck calls: same name, convertible arguments.

### 6.5 Soundness

Opacity can only make **fewer** things equal, never more, so it can't make a false statement
provable. [§5](#5-is-it-sound-the-metatheory) gives the metatheory. In Stitchwort terms
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
  that declaration.
- Unlike the dictionary and theorem folding (§3), which is deliberately *not* hashed because
  it never changes what is equal.

Content hashes change only for declarations that use the new forms; the existing snapshots
don't move.

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

Opacity is the right tool when a body is none of the proof's business. The two weaknesses of
§2 hurt programs that do want their bodies seen, so they're worth fixing independently
(implementation choices, so no decisions below; each is a lane in §9):

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
   kernel's entry points, the evaluator rule (unfold only while running or when listed),
   the rules of §6.3 (body only; a declaration with `unfolding` stays opaque; transitivity;
   refused on a plain `def`), hashing of both, `E-NOT-OPAQUE`. Kernel tests in the "must reject" style: an `rfl` through
   an opaque definition is refused; the same with `unfolding` is accepted; a cached
   acceptance doesn't survive a change of opacity (hash test).
2. **Surface: `opaque def` and `unfolding`.** Lexer keyword, parser, formatter, elaborator
   wiring, `f.unfold` generation (reusing `decreasing`'s), refusal on `theorem` and
   `instance`, the two renamed examples, docs/syntax.md, `examples/accept/opaque-*.sw` and
   `examples/reject/opaque-*.sw`.
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
  Opacity can only make fewer things equal, so it can't make a false theorem provable.
  **Recommendation: yes.**
- **D1264. A declaration that needs an opaque definition's body says `unfolding f` after its
  signature (Agda's way), rather than a `reveal f` step inside the proof (Dafny's way)?**
  Context: the clause applies to the declaration's body, like `decreasing` it goes after the
  signature, and the kernel only needs a list per declaration; a step inside a proof would need
  a new kind of core term. Allowed on theorems and opaque definitions, which then stay opaque
  themselves (Agda's rule, which keeps the theory safe). A proof that wants the body for one
  step puts it in a small lemma. **Recommendation: yes.**
- **D1265. Generate `f.unfold`, the equation `f x = body`, for every opaque definition?**
  Context: then most proofs `rewrite f.unfold` instead of unfolding, as Lean (`f.eq_def`) and
  Isabelle (`f_def`) do; `decreasing` definitions already get an `f.unfold` with the same
  shape. It costs one generated theorem per opaque definition. **Recommendation: yes.**
- **D1266. Keep `decreasing` definitions transparent by default, unlike Lean, which made
  well-founded definitions irreducible in 4.9?** Context: Lean's reason (unfolding through a
  well-foundedness proof is slow and fragile) doesn't hold here, because `decreasing` compiles
  to fuel that computes quickly, and `std` proves `Nat.digits 1205 = [1, 2, 0, 5]` by `rfl`.
  **Recommendation: yes, keep them transparent.**

## Sources

Read on 25 October 2026.

- [A1] Agda manual, "Opaque definitions": <https://agda.readthedocs.io/en/latest/language/opaque-definitions.html>
- [A2] Agda 2.6.4 release notes: <https://github.com/agda/agda/blob/master/doc/release-notes/2.6.4.md>
- [A3] Agda manual, "Abstract definitions": <https://agda.readthedocs.io/en/latest/language/abstract-definitions.html>
- [A4] Agda issue #6354, "`opaque`: use-site control of unfolding": <https://github.com/agda/agda/issues/6354>; implementation PR #6628: <https://github.com/agda/agda/pull/6628>
- [L1] Lean API, reducibility attributes: <https://lean-lang.org/doc/api/Lean/ReducibilityAttrs.html>; transparency modes in `src/Init/MetaTypes.lean`: <https://github.com/leanprover/lean4/blob/master/src/Init/MetaTypes.lean>
- [L2] Lean API, `ReducibilityHints` (`Lean.Declaration`): <https://lean-lang.org/doc/api/Lean/Declaration.html>; also *Type Checking in Lean 4*: <https://ammkrn.github.io/type_checking_in_lean4/declarations/declarations.html>
- [L3] Lean reference, "Definitions" (opaque constants): <https://lean-lang.org/doc/reference/latest/Definitions/Definitions/>
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
- [P1] N. A. Danielsson and E. Geng, "A Formalization of Opaque Definitions for a Dependent Type Theory", TyDe 2025, pp. 39–51, doi:10.1145/3759538.3759653: <https://conf.researchr.org/details/icfp-splash-2025/tyde-2025-papers/6/A-Formalization-of-Opaque-Definitions-for-a-Dependent-Type-Theory>, <https://research.chalmers.se/en/publication/549312>. (Only the abstract was read.)
- [P2] D. Gratzer, J. Sterling, C. Angiuli, T. Coquand, L. Birkedal, "Controlling unfolding in type theory", MSCS 35 (2025), arXiv:2210.05420: <https://arxiv.org/abs/2210.05420>
- [K1] smalltt README: <https://github.com/AndrasKovacs/smalltt>
- [U1] Unison, "Hashes" and "Unique types": <https://unison-lang.org/docs/language-reference/hashes>, <https://unison-lang.org/docs/language-reference/unique-types>

**Unverified:** that Agda has no separate kernel; which designs Danielsson and Geng show lose
subject reduction, and whether they prove opaque definitions conservative; how `irreducible_def`
is built in the kernel; the `[@@"opaque_to_smt"]` spelling (the wiki shows `[@"opaque_to_smt"]`).
