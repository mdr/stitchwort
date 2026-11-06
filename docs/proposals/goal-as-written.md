# Proposal: `rewrite` and `match` look at the goal as written first

**Status:** decided (D2475–D2480, Matt, 6 Nov 2026: all as recommended), being built. Ticket
SW-706 (D1422; D2453, Matt, 6 Nov 2026: "yes"), covering SW-1589 and SW-1562 too. Stage 1
(`rewrite`) is built (SW-1627, `crates/elab/src/rewrite/as_written.rs`); stage 2 (`match` and
`cases`) is built (SW-1628, `crates/elab/src/matching/as_written.rs`; as built, below the
plan in [§6](#6-recommendation-and-staged-plan)); stages 3–5 are not. Draft 1 was the design
note, which stopped for Matt's decisions ([§8](#8-decisions), Q1–Q6). Written against `main` at `cb58d7916`. Migration cost (hashes,
snapshots, sweeps) is not counted; options are judged by where they end up.

Related notes: [folded-goals.md](folded-goals.md) (SW-742, 28 Oct: the same question for AoC
2024, with a prototype; this note builds on it), [folded-calls.md](folded-calls.md) (glued
calls, D483, D484), [rewrite-hypothesis.md](rewrite-hypothesis.md) (`rewrite … at h`,
D463–D465), [glued-closed-types.md](glued-closed-types.md) (SW-1534, parked),
[docs/research/aoc-2020-friction-days-10-20.md](../research/aoc-2020-friction-days-10-20.md)
§2 theme A (the evidence).

Labels:

- **[checked]**: read in this repository at the place given.
- **[ran]**: run for this note on 6 Nov 2026 with the release CLI built from `cb58d7916`, on
  scratch files outside the repository or on `aoc/` (§9 lists them).
- **[proto]**: run with the prototype patch `dev/patches/sw-706-folded-rewrite.patch` (§5.1).
- **[cited]**: read in the source linked, on 6 Nov 2026 (§9).
- **[inferred]**: my reasoning from checked or cited facts.

## Contents

0. [Summary](#0-summary)
1. [The problem](#1-the-problem)
2. [What was decided before, and what has changed](#2-what-was-decided-before-and-what-has-changed)
3. [Prior art](#3-prior-art)
4. [The options](#4-the-options)
5. [Measurements](#5-measurements)
6. [Recommendation and staged plan](#6-recommendation-and-staged-plan)
7. [What changes elsewhere](#7-what-changes-elsewhere)
8. [Decisions](#8-decisions)
9. [Sources](#9-sources)

## 0. Summary

**The problem.** When a goal or a hypothesis mentions a definition, `rewrite` and `match`
look for their term in what the goal *computes to*, which the source doesn't show. A rule's
left side that is plainly there as written (`isSafe r`, `Spec.edges image.flip`) is not found
once the goal has computed past it; a `match` refines copies inside definitions the reader
can't see, or nothing at all; and every step after a `match` or `rewrite` works on a goal
with all the names gone. It hit 14 of the 20 AoC 2020 days, and is the most common friction
of the track. It costs detours more than lines: helper lemmas written only to dodge it (day
20's `memEq`), a program changed to suit a proof, bisecting with `?`.

**The change.** Search the goal *as written* first: read it back with calls kept as calls
(the form goals are already printed in), find the left side (or the scrutinee) there by its
head as written, and keep that result when it is complete, that is when no occurrence is left
hidden inside a call it kept folded. Otherwise do exactly what is done today. Where today's
search finds nothing, the as-written search may still succeed, and it may solve the rule's
unknowns (`isSafeCorrect _`). The same goes for a hypothesis after `at`, and for SW-1538's
transport along a `match`'s equation.

**What it should do.** Every proof that checks today still checks (the fallback is today's
search); day 20's `rewrite flipEdges image at member` and AoC 2024 day 2's `rewrite
isSafeCorrect _` check as first written; goals after `match` and `rewrite` keep the names the
user wrote, so the next step looks for what the reader sees. A prototype of the `rewrite` half
checks both repros, and over AoC finds four in five left sides as written, keeps the folded
next goal in 1,556 rewrites, and broke one declaration, through a hidden proof argument that
the real version must fall back on (§5). Lean's rule broke five.

**What it does not do.** Days 10 and 14 were hurt by `rewrite` and `match` reaching *into*
hidden copies; the completeness check keeps that behaviour (it is what `std` relies on).
Changing it is Lean's rule (only what is visible), which breaks existing proofs; Q4
recommends keeping today's reach, with occurrence selection as the later remedy if needed. Arithmetic that computes as it is
elaborated (day 13's `+ 1`) is not helped by any of this.

## 1. The problem

### 1.1 How the search works today

`rewrite p in t` with `p: a = b` (`crates/elab/src/rewrite.rs`, `rewrite_once`, `:698`):

1. forces the goal (`force(&g, goal)`, `:713`), which unfolds an outer call;
2. reads it back **unfolded** (`cx.quote`, `:714`): every glued call written as what it
   computes to, the full normal form;
3. reads the left side `a` back unfolded too (`:732`), and takes its key, the head and number
   of arguments of that normal form (`key`, `:1328`);
4. visits every subterm with that key and compares it with `a` by unification (`Search`,
   `:1092`), abstracts the matches into a motive, and builds `J`.

So a rule about `isSafe` is keyed by `List.all` (what `isSafe` computes to), and the next goal
is evaluated from a term with no calls in it. This is D484 (folded-calls.md: "`rewrite` and
the decision search see … the unfolded goal, as today, so every existing proof keeps working").
`rewrite … at h` runs the same function over `h`'s type (`rewrite_at`, `:146`). **[checked]**

A generalised `match e:` (`crates/elab/src/matching.rs`, `generalised_now`, `:867`) reads the
goal and every hypothesis's type back unfolded (`:889`, `:892`), reads the scrutinee back the
same way (`normals`, `:1107`), and replaces each **syntactically identical** subterm (`occurs`,
`Generalise`, `:1549`) by the new variable. The arms' goals are that term evaluated with the
constructor put in, so they hold no calls either. `cases` goes through the same function.
**[checked]**

SW-1538's transport along a match's equation (`crates/elab/src/check.rs`,
`along_match_equation_now`, `:1303`) reads `found` and `expected` back unfolded (`:1311`) and
fires only if the scrutinee's normal form `occurs` syntactically in one of them (`:1336`).
**[checked]**

The goal value itself is mostly as written: the elaborator glues calls (`Value::Call`), and
`quote_folded` reads them back as calls, except one that "steps at once" (its case tree starts
on a constructor or number, `matches_at_once`, `crates/core/src/value.rs:584`). That is the form
goals and hypotheses are printed in. So "as written" in this note means **the folded read-back
of the goal's value**, not the source text: the two differ only where a call steps at once
(`if True then a else b` is `a`) and in arithmetic, which computes as it is elaborated. **[checked]**

### 1.2 The cases, from the notes

All from aoc/NOTES-2020.md (cited `N:line`) unless said; the research note's theme A has the
summary. Grouped by what goes wrong.

**(a) The left side is there as written, but the search looks only in the computed form.**

- *Day 20, `withinFlip`* (`N:5365`, SW-1589). `rewrite flipEdges image at member`, with
  `member: edge ∈ Spec.edges image.flip` and `flipEdges: Spec.edges image.flip = [...]`, was
  `E-REWRITE-NOTHING`: the search compared "what the rule's left side computes to,
  `[List.headOr (List.map …) [], …]`, a list, against a disjunction", which is what `member`'s
  type computes to (`∈` on a list literal). The left side is literally in `member`'s type as
  printed. Workaround: a lemma `memEq (same: xs = ys) (member: x ∈ xs): x ∈ ys := rewrite same
  at member in member`, where `xs` is a variable so nothing computes; it is still in
  `Day20/Proofs/Orientations.sw:211`, used six times. Reduced to eight lines in §5.2
  (`member.sw`). **[ran]**
- *AoC 2024 day 2* (folded-goals.md repro 4, the trigger of SW-706). `rewrite isSafeCorrect _`
  on a goal `isSafe { levels = xs.reverse } = …` finds no `isSafe ?0`: unfolded, the left side
  is `List.all ?0.levels (…)`, and `?0.levels`, a field of an unknown, can't be solved by
  comparing with `List.reverse xs`. As written, `isSafe ?0` against `isSafe {levels = …}` is
  solved at once by the argument. **[ran]**
- *Day 5* (`N:1144`). `rewrite idsWritten input passes parsed` (left side `seatIds (…)`) ran
  out of budget comparing the unfolded forms of `seatIds` and `Text.lines`, both of which were
  visible as calls in the goal. Fixed by `J` by hand.

**(b) After a `match` or `rewrite`, the goal has computed, and the next step can't find what
the source shows.**

- *Day 18, `loop`* (`N:4779`). `rewrite shifted` found no `Succ (fuel + steps)`: "the arm's
  patterns had already computed the goal past `fuel + Succ steps` into `readSteps`'s inner
  `match`". An `Eq.trans` chain of `Eq.cong`s, which never looks inside the goal, worked.
- *Day 11, `walkSeen`* (`N:2870`). `match layout.grid.at next` refined nothing: "the goal had
  computed `Grid.at` into `cellAt`'s inner `match`".
- *Day 15* (`N:3967`). `match below: game.turn < …` didn't refine; "the goal had already
  computed `<` into `<=` of the tail".
- *AoC 2024 days 3, 6, 7* (folded-goals.md §2): the next goal after a `rewrite` or in a `match`
  arm lost `sumBy`, `concatenate`, so a lemma about them no longer applied.

**(c) A `match` or `rewrite` reaches into a copy the reader can't see.**

- *Day 10, `cutAbove`* (`N:2540`). `match near: adapter <= joltage + 3` also refined the copy
  inside the unfolded `canFeed joltage adapter` (whose second half is the same comparison), to
  `False` in one arm and `if if … then True else False` in the other, "while the facts I stated
  after the `match` kept the original form". Fixed by restating the lemma so the goal has no
  definitions to unfold.
- *Day 14, `toBitsAnd`* (`N:3692`). Rewriting with `Nat.andDiv` (about `Nat.and m n / 2`)
  first, then with a lemma about `Nat.and m n % 2`, failed: "the `% 2` apparently computes to
  something containing the `/ 2`, which the first rule then rewrote". Rewriting in the other
  order worked.

**(d) The scrutinee is there, written differently.**

- *Day 19, `chainBounded`* (`N:5087`, SW-1575). `match found: sequences.map (rules.chainThrough
  more) |> .maximum` refined nothing: the goal had the lambda eta-expanded, the scrutinee
  didn't, and the occurrence test is syntactic. Reduced in §5.2 (`eta.sw`): the arm's goal and
  the hypothesis `all` are unrefined, silently. **[ran]**
- *SW-1562*: SW-1538's transport has the same syntactic test (§1.1), so it misses the same
  way, and also when the scrutinee only appears inside a definition that doesn't unfold in the
  read-back (an opaque or well-founded one). **[inferred]**

**(e) Out of scope here, for completeness.**

- *Day 11, E-RESOURCE* (`N:2896`, SW-1477): `match found: start.settle rule roundLimit` with
  `roundLimit` = 1000 unfolded 1000 rounds to find the scrutinee. A folded search finds it
  without unfolding only if it is visible; the completeness check (§4) would still unfold. See
  Q5 for a bounded check.
- *Day 13* (`N:3464`): which side of `+ 1` computes. `+` on `Nat` computes as it is
  elaborated, so the as-written form is the computed one; nothing here changes it.
- *Day 11's first item* and *day 12* (`N:2870`, `N:3128`): an occurrence that appears only
  after the goal computes further, and a scrutinee no longer in the goal at all. Messages
  (SW-1478, SW-1485), not search.

## 2. What was decided before, and what has changed

- **D484** (folded-calls.md, Oct 2026): `rewrite` and the decision search see the unfolded
  goal, "so every existing proof keeps working and only the written-back terms and messages
  change". The reason was no regressions, not that the unfolded search is better.
- **SW-742 / folded-goals.md** (28 Oct) proposed exactly the shape of this note for 2024's
  days: folded-first with a completeness check for `match`, `cases` and `rewrite` (its option
  B), a folded search to solve a rule's unknowns (C), `rewrite f` (D), and a read-back fix (A).
  It measured B: for `match`, 442 of AoC's generalisations kept folded, no result changed in
  std, AoC, the roguelike or 893 examples, no measurable time; for `rewrite`, 1,355 rules kept
  folded, 8 with a different goal. It found Lean's rule (no check) breaks
  `std/Result/Result.sw`'s `traverseCons` and `List/Toolkit.sw`'s `foldMaxMem`.
- **D1422** (28 Oct) filed SW-706, the `rewrite` half, "measure on AoC and std proofs first".
- **D1431–D1435** were that note's questions. D2360 (Matt, 4 Nov: "happy to go with your best
  recommendation") closed **D1431** (folded-first with the check) as "answered by events: yes:
  goals stay folded in rewrite/match (SW-742, SW-1052, SW-1106)", D1434 (print a statement's
  `match` as `match`, done by SW-1000) and D1435 (no transparency levels). **D1432** (folded
  search for unknowns, SW-795) and **D1433** (`rewrite f`, SW-796) are still open.

**What has changed since:**

1. **D1431 was closed, but its option B was never built.** SW-1052 made the *kernel context*
   `rewrite` uses read back folded (`kernel_context`, `rewrite.rs:1267`), and SW-1106 kept
   context values as they are in case splits; neither touches the search. `rewrite_once` and
   `generalised_now` still read the goal back with `quote` (§1.1). Stage 1 of folded-goals.md
   (the read-back stepping once) was merged as `quote_shown`, for display only
   (`value.rs:1937`). So the decision exists and the work doesn't. **[checked]**
2. **Twice the evidence.** 2024's four days are now 2020's fourteen, with new kinds: the
   hypothesis case (day 20, which `at h` didn't exist for when D484 was taken), and the
   over-reaching cases (days 10, 14), which folded-first with the check does *not* fix.
3. **SW-1538** (transport along a match's equation, 6 Nov) is a third consumer of the
   unfolded, syntactic occurrence test, and SW-1562 is its version of the problem.
4. **The messages got much better** (E-REWRITE-NOTHING's notes "already computed past it",
   "replaced by the match", the goal as written). Several days praised them. So what remains
   is behaviour, not explanation.
5. **The prototype bug.** Rewriting at a hypothesis forces its type first (`rewrite.rs:713`),
   unfolding `∈` before anything reads it; a folded search must start from the unforced type
   (found while prototyping, §5.1). **[proto]**

## 3. Prior art

Two families. Lean, Rocq and ssreflect match against the goal **as written**, keyed by the
head symbol, and compare candidates up to a chosen transparency; Agda and Idris 2
**normalise** the goal first. Stitchwort today is in the second family; this note proposes
the first family's search with the second's as a fallback.

**Lean 4.** `rw` instantiates metavariables and calls `kabstract` on the goal, with no
reduction: `let e ← instantiateMVars e` / `kabstract e lhs config.occs` [L1]. `kabstract`
"detect[s] subterms equivalent to `p` using key-matching. That is, only perform `isDefEq`
tests when the head symbol of subterm is equivalent to head symbol of `p`" [L2]. The
comparison is at `transparency : TransparencyMode := .reducible` by default, and occurrences
can be chosen, `occs : Occurrences := .all` [L3]; "`erw [rules]` is a shorthand for `rw
(transparency := .default) [rules]`" and `rw (occs := .pos L) [e]` rewrites only the listed
occurrences, counted from 1 [L4]. A subterm mentioning a bound variable is never a candidate
(`if e.hasLooseBVars then visitChildren ()`) [L2], and a motive that doesn't typecheck is
"motive is not type correct" [L1]. `simp` indexes lemmas by discrimination trees at reducible
transparency and rewrites under binders with `funext` [L5]. **[cited]**

`h ▸ e`: "The macro tries both orientations of `h`. If the context provides an expected type,
it rewrites the expected type, else it rewrites the type of `e`" [L6]; `elabSubst` abstracts
the expected type first, and if that fails, the type of `e` *as inferred, not reduced*, then
checks the result against the expected type [L7]. This is SW-1589's "rewrite a hypothesis by
its stated type". **[cited]**

`match h : e with` builds its motive by `kabstract result.matchType discr`, the same keyed
search, on the expected type as written [L8]; "We abort generalization if the new `matchType`
is type incorrect" [L8]. `generalize` uses `kabstract` at `.implicit` transparency "to avoid
excessive resource usage" [L9]. `split` looks for a `match` or `if` in the goal as written
[L10]. So in Lean, a proof that needs inside a definition says `unfold f` or `simp only [f]`
first. **[cited]**

**Rocq.** `rewrite` "finds the first matching subterm in depth-first search order. Only
subterms identical to that first matched subterm are rewritten" [R1]. With `Keyed
Unification`, "The subterms … must start with the same key as the left- or right-hand side of
the lemma … and the arguments are then unified up to full reduction" [R1]. `rewrite` "won't
find occurrences inside forall that refer to variables bound by the forall; use the more
advanced setoid_rewrite" [R1], which rewrites under binders with declared `Proper` morphisms
and "by default … unfold[s] global definitions during rewrite rule matching" [R2]. **[cited]**

**ssreflect** (now spelled `rw` on Rocq's master [R3]) "compares a pattern term with a subterm
of the goal by comparing their heads and then pairwise unifying their arguments (modulo
conversion)… If the head of term is a constant, then it should be syntactically equal to the
head symbol of the subterm" [R3]. It has occurrence switches and patterns (`rw {2}[_ + y +
0](…)`), unfolding by name ("`rw /my_def.` is analogous to: unfold my_def"), and change by
conversion ("`rw -[term1]/term2.` is equivalent to change term1 with term2") [R3]. **[cited]**

**Agda.** `rewrite eq` is sugar for `with lhs | eq … | refl` [A1], and "The generalisation step
of a with-abstraction needs to normalise the scrutinee and the goal and argument types to make
sure that all instances of the scrutinee are generalised" [A1]; the code normalises
(`normalise vtys`) and then abstracts syntactically (`absTerm`, `equalSy`) [A2]. Its known
failures are an ill-typed with-function ("… when checking that the type … of the generated with
function is well-formed") and that only "occurrences of the term that are visible at the time of
the abstraction are generalised over" [A1]; issues #343, #1420 ("Rewrite fails where
hand-translation to with succeeds") [A3]. This is today's Stitchwort `match`. **[cited]**

**Idris 2.** `rewrite … in` normalises the expected type (`expnf <- nf defs env expected`) and
replaces every subterm that `convert`s with the left side, with no key filter [I1]; "if the
rewritten expected type converts with the original, then the rewrite did nothing, which is an
error" (`RewriteNoChange`) [I1, I2]. **[cited]**

**Isabelle.** Matching is "higher-order unification of λ-terms modulo αβη-equivalence" [S1]; a
definition becomes a fact `c_def` and is unfolded only by rewriting with it, so `simp` and
`subst` see the term as written [S1]. **[cited; "only by rewriting with it" inferred from the
manual's description of definitions]**

**What to take.** Everyone who matches as written keys by the head *as written* and compares
candidates up to some conversion (Lean reducible, Rocq/ssreflect full). Nobody but Agda and
Idris normalises the goal first, and Agda's manual lists the failures that follow. Lean's
`▸` is precisely "try the stated type". Occurrence selection exists in all three as-written
systems. Nobody offers "as written, else normalised" automatically; that is Stitchwort's
choice to keep D484's no-regression promise.

## 4. The options

The kernel checks every `J` against the declared type up to conversion, and a folded and an
unfolded goal are convertible, so none of these can make an unsound proof pass: the risk is
only proofs that stop or start checking, and terms (so hashes) that change. **[inferred]**

### A. As written first, with a completeness check, else today's search

For `rewrite` (goal and `at h`) and for `match`/`cases`:

1. Read the goal (or `h`'s type, unforced) back folded; for `rewrite`, read the left side
   back folded too and key it by its head as written (`isSafe`, not `List.all`).
2. Search: same candidates and tests as today (keyed, then syntax, then unification), plus
   unification by arguments for a call of the same definition, which may solve the rule's own
   unknowns (folded-goals.md's C; `unify_solving_arguments` already exists for instances,
   `rewrite.rs:1075`).
3. **Completeness check:** with the found occurrences replaced by a fresh variable, read the
   result back unfolded and check no occurrence remains (one left was hidden in a call kept
   folded). For `match`, the hypotheses too.
4. Complete: use the folded motive, so the next goal and the arms keep their calls.
   Incomplete, or nothing found folded: today's search, unchanged. Today's search finds
   nothing: the folded result, even if found only folded (this is day 20 and 2024 day 2).

*Fixes:* (a) all three; (b) in so far as the goal stays folded after the step, which is most
of it (the arm's goal keeps `readSteps`, `Grid.at`, `sumBy`); (d) day 19 if the folded search
compares by unification (it does, step 2), and SW-1562 by the same change in the transport.
*Doesn't fix* (c): day 10's hidden copy inside `canFeed` and day 14's `/ 2` inside `% 2` make
the check fail, so today's behaviour runs. *Breaks:* nothing that checked, provided the folded result is the rewrite today's search would
make. Two things can differ: a later step that depended on the next goal being unfolded (the
prototype measures that, §5), and, for a rule with unknowns, the instance chosen (`comm _ _`
finds the visible `add a b` where today's first occurrence in the unfolded goal is
`add c (add a b)`). SW-1627 therefore also runs today's search and falls back when its instance
differs.

### B. Lean's rule: as written where found, else today's search

Steps 1, 2 and 4 of A without the check: a visible occurrence is used even if hidden copies
remain. *Fixes* (c) too. *Breaks* `Result.traverseCons` and `List.foldMaxMem` in std
(folded-goals.md, **[ran]** there) and, for `rewrite`, the proofs counted in §5 as "differs".
Each fix is an extra `rewrite` or `match` naming the hidden copy, or an unfold step (D).

### C. As written only, with an explicit unfold step

Lean exactly: no fallback; `rewrite f` (or `unfold f`) to see inside. *Fixes* everything A and
B do, plus the cost: nothing ever unfolds unasked (day 11's E-RESOURCE goes). *Breaks* every
proof that rewrites inside a definition without naming it: the "unfolded-only" rows of §5,
hundreds in AoC, and folded-goals.md's goal-readback count (55 AoC proofs). A sweep of that
size changes the language's feel: D484's "proofs rarely unfold by hand" was a deliberate
strength.

### D. `rewrite f`: one step of a definition, by name (D1433, still open)

A rule naming a definition means its one-step equation, as Lean's `rw [f]` and ssreflect's
`rw /f`. Needed by B and C; useful under A where the folded search finds nothing and the user
wants the inside of one call, not all of them.

### E. Occurrence selection

`rewrite (at := 2) p` or ssreflect's `{2}`: rewrite only some occurrences. Fixes day 14 by
hand (and day 10 for `rewrite`, not `match`). Small, orthogonal, and counted in the *folded*
goal it means what the reader counts. Not needed by A; worth it only if (c) recurs.

### F. For `match`: abstract the written form, and the hidden copies are refined only if asked

A variant of B for `match` alone: refine only visible occurrences, so day 10's facts keep
matching, but say so (a warning naming the call whose copy wasn't refined), and offer `match
(deep) e:` or a `cases` step to reach in. Same breakage as B for `match`.

## 5. Measurements

### 5.1 The prototype

`dev/patches/sw-706-folded-rewrite.patch`, about 80 lines in `rewrite.rs`, for `rewrite` only
(goal and `at h`; not inside binders, not `match`). Behind an environment variable `SW706`:

- After today's search, run the same search over the *unforced* goal read back folded, with
  the left side read back folded (and keyed by it), comparing candidates also by arguments
  (`unify_solving_arguments`).
- Classify each rule: **kept-same** (both found, same next goal, same folded read-back),
  **kept-folded** (same next goal by unification, but the folded one keeps calls), **differs**
  (both found, next goals don't unify: some occurrence was hidden), **unfolded-only** (folded
  found nothing), **rescued** (only the folded search found something), **folded-error** (the
  folded attempt failed, e.g. its motive didn't check).
- `SW706=measure`: today's result is always used (rescues aside); `check`: the folded one when
  kept-folded or rescued (option A, the completeness check done bluntly by comparing goals, as
  folded-goals.md did); `lean`: also when it differs (option B).

The blunt check runs both searches, so its *time* is not A's; its counts are.

### 5.2 Repros

Scratch files, `stitchwort check`:

| file | today | prototype, `check` |
|---|---|---|
| `isSafe.sw` (2024 day 2: `rewrite isSafeCorrect _`) | E-REWRITE-NOTHING, "found no `isSafe ?0`" | checks (rescued) |
| `member.sw` (2020 day 20: `rewrite flipEdges image at member`) | E-REWRITE-NOTHING, "in the type of `member`" | checks (rescued) |
| `eta.sw` (2020 day 19: `match found: xs.map f \|> .maximum`) | arm unrefined, silent | not covered (match) |

**[ran, proto]** A first prototype searched the *forced* type of `member` and still failed:
forcing `edge ∈ Spec.edges image.flip` unfolds `∈` and `Spec.edges`, so the folded read-back
of the forced value is already the disjunction. The search must start from the value as bound.

### 5.3 AoC

`stitchwort check --no-cache` over `aoc/` (std's prelude comes from its cache, so these are
AoC's own rewrites, plus retries: a postponed `rewrite` is searched again). Release build,
machine shared with other lanes. **[ran, proto]**

| | today | `measure` | `check` (A) | `lean` (B) |
|---|---|---|---|---|
| kept-same | – | 2,996 | 2,829 | 2,827 |
| kept-folded | – | 1,280 | 1,556 | 1,550 |
| unfolded-only | – | 867 | 759 | 757 |
| differs | – | 5 | 4 | 4 |
| folded-error | – | 4 | 4 | 4 |
| neither (speculative attempts) | – | 134 | 134 | 134 |
| declarations failing | 1 (2024 day 24, SW-1600's known regression) | the same 1 | that 1 + 1 | that 1 + 5 |
| user time | 67.8 s | 73.9 s | 74.8 s | 69.1 s |

The roguelike (`games/rogue`): today checks, 5.15 s; `check` checks, 5.22 s, with 160
kept-folded, 635 kept-same, 83 unfolded-only, none differing.

What it says:

- **Four in five rewrites find their left side as written** (4,276 of 5,282 in `measure`),
  and in 1,280 of them the next goal keeps calls today's loses. Keeping goals folded feeds on
  itself: with `check`, the later rules of the same proofs find 276 more folded (1,280 →
  1,556) and 108 fewer need the unfolded search (867 → 759).
- **The unfolded search is still needed** for one in six (759): rewriting inside a definition
  the goal doesn't show is how AoC proofs work, and option C would make every one of those an
  explicit unfold. That is the scale of C's sweep, and the reason not to take it.
- **Lean's rule (B) breaks five declarations**: 2020 day 17 `Neighbours.sw:41`, 2025 day 1
  `Part2.sw:82` and `:94`, 2025 day 8 `Labels.sw:107` and `:153`. Each needed a hidden copy
  rewritten (in day 8, inside `Map.Raw.fromListChecked`'s unfolding, where `rfl` then failed).
  With folded-goals.md's two std failures for `match`, that is B's cost.
- **The blunt check (A) breaks one**: 2025 day 1 `Part2.sw:82`, `_ = (Succ a + n) / d :=
  rewrite (omega: d = Succ a)`, "expected `x' ≠ 0`, but this has type `d ≠ 0`". Folded, `/`
  keeps its hidden proof argument `d ≠ 0`, which the folded motive must abstract too;
  unfolded, the proof is gone (`Nat.div` doesn't use it). So the next goals unify, yet the
  folded motive isn't type-correct where today's is. The real A must fall back when anything
  on the folded path fails, including the motive's check, and prefer a motive that doesn't
  abstract inside a proof argument's type. This is the one new risk the prototype found.
- **Time.** The prototype runs both searches, so +10% user time is its upper bound. The real
  A runs the folded search, then one unfolded read-back for the check, and the unfolded search
  only on fallback; most rewrites would cost about what they cost today. To measure in stage 1.

Not measured: `match` (folded-goals.md measured it on 28 Oct: 442 folded, std and AoC
unchanged; 2020's days have been added since), the examples' exit codes, and std on its own
(its proofs come from the prelude cache here).

## 6. Recommendation and staged plan

**Option A, for all three consumers, with the folded search solving a rule's unknowns.**
Not B, C or F now; D (`rewrite f`) as a later stage; E only if over-reaching recurs.

Why: A is the only option that fixes the hypothesis and unknown cases (day 20, 2024 day 2)
and keeps the names in every later goal without breaking a proof; the 2020 cases it doesn't
fix (days 10 and 14, a reach into a hidden copy) are two, and both had a quick workaround,
while the cases B and C break are in std and in five AoC declarations, each needing the hidden
copy. This is what D1431 already chose; the work was never done (§2).

The plan, one lane each, each with accept examples, the hash snapshots re-recorded, and AoC
and the roguelike checked before and after (results and time). Stages 1 and 2 generate kernel
terms (different motives), so they get an Opus review (D2364).

1. **`rewrite` as written first (goal and `at h`).** In `rewrite_once`: the folded search
   from the unforced goal (§5.2), keyed by the left side as written, comparing also by
   arguments so the rule's unknowns are solved (Q3); a real completeness check (the motive
   body read back unfolded must hold no occurrence); fallback to today's search on any
   failure of the folded path. Accept: `isSafe.sw`, `member.sw`; the `Part2.sw:82` shape
   (hidden proof argument) falls back; a rule whose only occurrence is inside a folded call
   still rewrites. Then day 20's `memEq` is removed as the check that it works. Update D484's
   text in folded-calls.md, and `docs/syntax.md` "rewrite" (what is searched). Sonnet with an
   Opus review; expected 120 min.
2. **`match` and `cases` as written first.** folded-goals.md's option B in `generalised_now`
   (its scratch patch was about 70 lines), with the occurrence test by keyed unification in
   the folded attempt, so a scrutinee written up to eta is found (day 19, `eta.sw`). Accept:
   folded-goals.md repro 1 (the arms keep `concatenate`), `Result.traverseCons`'s and
   `List.foldMaxMem`'s shapes (fall back), `eta.sw`. Opus (the motive and its copies);
   expected 120 min. `match` and `cases` face the same instance-choice question when the
   scrutinee has unknowns or several candidates: the folded search must pick the occurrence
   today's would, or fall back (SW-1627's `todays_instance`).

   *As built (SW-1628).* The targets (goal, variables' types) are read back folded from the
   values as bound; a subterm is an occurrence if it has the scrutinee's head as written and
   unifies with it **solving nothing** (no unknown solved, made or left waiting), so there is
   no instance to choose: the scrutinees are known before generalising (D2090's wait), and
   where both searches find something they find the same thing. The completeness check is
   stronger than "no copy left": each generalised target, read back unfolded, must *agree*
   with today's generalisation of it, the same term except where the folded one has the
   scrutinee's variable and today's has a subterm that unifies with the scrutinee (an
   occurrence written differently, day 19). That also catches a closed scrutinee that computes
   to a constructor (`match h: isBig 20` on `pick (isBig 20) = 1`: today's goal is `1 = 1`, the
   folded one would be `pick x = 1`), which "no copy left" would let through and which would
   change the arms. Every variable today copies must be copied too, and the folded motive must
   type-check now (also for `cases`), else today's generalisation, unchanged. Counts under
   `STITCHWORT_MATCH_METRICS`.
3. **SW-1538's transport on the folded forms** (SW-1562), after SW-1604's fixes to the same
   function: test the scrutinee as written against `found` and `expected` read back folded,
   then today's test. Sonnet, 45 min.
4. **A bounded completeness check (Q5).** When the check's unfolded read-back runs out, use the
   folded result, with a note, where today ends in E-RESOURCE (day 11's `settle … 1000`).
   After 2; 45 min.
5. **`rewrite f` (D1433, Q6).** As in folded-goals.md option D. Any time after 1.

### 6.1 Evidence still to collect

- The real completeness check's cost (stage 1, with `STITCHWORT_REWRITE_METRICS` counting
  folded, fallback and rescued).
- `match` over the 2020 days: how many generalisations keep the goal folded now.
- The examples' exit codes (`examples/accept`, `examples/reject`) under stages 1 and 2, and
  std on its own (`--no-cache` on the prelude).
- Which 2020 workarounds go: day 20's `memEq` (six uses), day 18's `Eq.trans` chain, day 5's
  hand-written `J`, day 16's `let` before the `match` (SW-1538 already removed the others).
- The hash churn: how many snapshots move (not a cost to weigh, but the lane must know).

## 7. What changes elsewhere

**Proof terms and the kernel.** The kernel is unchanged. Motives kept folded contain calls
where today's contain unfoldings, so the `J` terms of about 1,556 AoC rewrites (and the
`match` helpers' types, for stage 2) change, and their hashes with them; the kernel unfolds
the calls itself (it checks with gluing off, D483) and the terms are smaller. Existing
proofs don't need editing. **[inferred]**

**Checking time.** About the same per rewrite (§5.3); goals that stay folded are smaller to
read back and compare, which folded-calls.md found to dominate slow proofs. Where today runs
out of resources unfolding a goal to find something visible, A finds it without unfolding.

**Messages.** The goal in E-REWRITE-NOTHING and in a `match` arm's errors is the folded one
far more often, which is what the notes ask for. Per ticket:

- **SW-1485 / SW-1575** (warn when a `match` refines nothing): still needed (day 12's
  scrutinee isn't in the goal in any form). Stage 2 removes SW-1575's eta case, so its warning
  is about the remaining ones; the warning can show the goal folded.
- **SW-1478** (E-REFL after a `match`, suggest `match e:`): unchanged; that occurrence appears
  only later, which no search at the `match` sees. SW-1538's E-REFL note already covers part.
- **SW-1477** (E-RESOURCE names no definition): stage 4 removes the case where the
  scrutinee is visible; the message is still wanted for the rest.
- **SW-1570** (after a `match`, suggest `Eq.trans`/`Eq.cong`): much rarer once arms keep their
  calls; keep it as a note on E-REWRITE-NOTHING when the left side is found only in the
  folded goal and the motive failed.
- **SW-1511** (show the subterm, not `…`): unchanged, and easier: the folded goal is short.
- **SW-1546** (guide: `rewrite h at h in h`): the idiom is still valid; the guide should say,
  after stage 1, that `rewrite` looks at the type as printed first.

**Docs.** `docs/syntax.md` ("rewrite", "Generalised `match`"), the proving guide's section on
which form a goal is in, and the language guide's proofs chapter: "`rewrite` and `match` look
for the term as the goal shows it first, then inside the definitions it mentions". Stage 1
and 2 lanes update them.

## 8. Decisions

The orchestrator assigns D numbers.

- **Q1.** Make `rewrite` (on the goal and with `at h`) look for the left side in the goal as
  written first (calls kept, the form goals are printed in), keep that result only when no
  occurrence is left hidden inside a call, and otherwise do exactly what it does today
  (option A)? This is what D1431 chose; it was never built. [rec: yes]
- **Q2.** The same for `match` and `cases` (and so their arms' goals), comparing the
  scrutinee by unification in the as-written search so a scrutinee written up to eta is found
  (day 19), and for SW-1538's transport (SW-1562)? [rec: yes]
- **Q3.** When the rule has unknowns, may the as-written search solve them by the call's
  arguments (`rewrite isSafeCorrect _` finds `isSafe { levels = … }`)? This is D1432, still
  open; it turns failures into successes, but it can pick a different instance than today's
  search (SW-1627 falls back when it does). [rec: yes]
- **Q4.** Keep today's reach into hidden copies (days 10 and 14) when the as-written result is
  incomplete, rather than Lean's rule of rewriting only what is visible (option B), which
  breaks two std proofs and five AoC declarations? Occurrence selection (`rewrite (at := 2)`)
  stays unbuilt until a proof needs it. [rec: keep today's; no new form now]
- **Q5.** When the completeness check itself runs out of resources, use the as-written result
  (with a note saying hidden copies weren't looked at) instead of failing with E-RESOURCE? It
  changes only proofs that fail today. [rec: yes, as stage 4]
- **Q6.** Build `rewrite f` as one step of `f` (D1433, still open) after stage 1? [rec: yes]

## 9. Sources

Read on 6 November 2026.

- [L1] Lean 4, `src/Lean/Meta/Tactic/Rewrite.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean>
- [L2] Lean 4, `src/Lean/Meta/KAbstract.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean>
- [L3] Lean 4, `src/Init/Meta/Defs.lean` (`Rewrite.Config`) and `src/Init/MetaTypes.lean` (`Occurrences`): <https://github.com/leanprover/lean4/blob/master/src/Init/Meta/Defs.lean>, <https://github.com/leanprover/lean4/blob/master/src/Init/MetaTypes.lean>
- [L4] Lean reference manual, tactic reference (`rw`, `erw`, `occs`): <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- [L5] Lean 4, `src/Lean/Meta/Tactic/Simp/SimpTheorems.lean`, `Main.lean`, `Types.lean`: <https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Simp>
- [L6] Lean 4, `src/Lean/Parser/Term.lean` (`▸` docstring, `match (generalizing := …)`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean>
- [L7] Lean 4, `src/Lean/Elab/BuiltinNotation.lean` (`elabSubst`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/BuiltinNotation.lean>
- [L8] Lean 4, `src/Lean/Elab/Match.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Match.lean>
- [L9] Lean 4, `src/Lean/Meta/Tactic/Generalize.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Generalize.lean>
- [L10] Lean 4, `src/Lean/Meta/Tactic/Split.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Split.lean>
- [R1] Rocq reference manual, "Rewriting with Leibniz and setoid equality": <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html>
- [R2] Rocq reference manual, "Generalized rewriting": <https://rocq-prover.org/doc/master/refman/addendum/generalized-rewriting.html>
- [R3] Rocq reference manual, "The SSReflect proof language" (master, and V9.1.0): <https://rocq-prover.org/doc/master/refman/proof-engine/ssreflect-proof-language.html>, <https://rocq-prover.org/doc/V9.1.0/refman/proof-engine/ssreflect-proof-language.html>
- [A1] Agda manual, "With-Abstraction": <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [A2] Agda, `src/full/Agda/TypeChecking/With.hs` and `Abstract.hs`: <https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/With.hs>, <https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Abstract.hs>
- [A3] Agda issues #343, #1420, #5668: <https://github.com/agda/agda/issues/343>, <https://github.com/agda/agda/issues/1420>, <https://github.com/agda/agda/issues/5668>
- [I1] Idris 2, `src/TTImp/Elab/Rewrite.idr` and `src/Core/Normalise.idr`: <https://github.com/idris-lang/Idris2/blob/main/src/TTImp/Elab/Rewrite.idr>, <https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise.idr>
- [I2] Idris 2, `src/Idris/Error.idr`: <https://github.com/idris-lang/Idris2/blob/main/src/Idris/Error.idr>
- [S1] Isabelle/Isar reference manual: <https://isabelle.in.tum.de/doc/isar-ref.pdf>

Scratch files (not committed): `isSafe.sw`, `member.sw`, `afterMatch.sw`, `eta.sw`,
`transport.sw`, as quoted in §5.2.
