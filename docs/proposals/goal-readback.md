# Proposal: reading the goal back for `match` and `rewrite`

**Status:** draft 1, 26 October 2026. Design only; the scratch code is not committed (patch
kept in the worktree's `target/goal-readback/`). Lane 6 of the build plan in
[opaque-definitions.md](opaque-definitions.md) §9, which asked for a short design note first
(§8.2). Decisions D1280 and D1281 ([§8](#8-decisions)) are open. Written against commit
`9b2a7b2a`. Related: [folded-calls.md](folded-calls.md) (glued calls, D483, D484).

Labels as in the other notes: **[run]** a check I ran for this note (release CLI built from
`9b2a7b2a` plus the scratch patch, `stitchwort check --no-cache`, user CPU seconds on a
machine shared with other lanes); **[checked]** read in the source at the place given;
**[cited]** read in the linked source while writing this; **[inferred]** my reasoning.

## Contents

0. [Summary](#0-summary)
1. [The problem, and every place it happens](#1-the-problem-and-every-place-it-happens)
2. [A minimal repro](#2-a-minimal-repro)
3. [How other systems decide how far to unfold](#3-how-other-systems-decide-how-far-to-unfold)
4. [The options, tried](#4-the-options-tried)
5. [Recommendation: unfold every call, except one too big to write out](#5-recommendation-unfold-every-call-except-one-too-big-to-write-out)
6. [What this lane does not fix: the kernel](#6-what-this-lane-does-not-fix-the-kernel)
7. [Build plan (one lane) and tests](#7-build-plan-one-lane-and-tests)
8. [Decisions](#8-decisions)
- [Sources](#sources)

## 0. Summary

`match e: …` builds its motive, and `rewrite` searches for what to replace, in the goal read
back **fully unfolded** (D484). Inside an `if` that can't step, that read-back goes into both
branches and writes out whatever they compute, however large. Reading back folded instead
breaks real proofs (`std/Result/Result.sw`, 55 errors in AoC), because proofs rely on seeing
through calls.

I tried six ways of reading back the goal on `std`, the AoC project, the roguelike, a
stage-2 copy of the roguelike and a 25-line repro. The only one that changes nothing in the
three projects and fixes the repro and the stage-2 copy is **capped unfolding**: read back
unfolded as today, but **write a call as the call when its own unfolding would read back to
more than 100,000 nodes** (calls that step at once by matching are never kept). At that cap,
nothing in `std`, AoC or the roguelike is ever kept folded, and their check times don't move.
The approaches that cut by *position* (never inside a stuck `if`; only along the path to the
target) all break proofs, for one reason: the same expression then reads back differently in
different places, so a rule's left side or a `match`'s scrutinee, read on its own, is no
longer found in the goal.

Two findings change the plan around this lane:

1. **The elaborator has more unfolded read-backs than the two in §8.2**: the function-result
   check `written_result`, the motive check `check_motive`, `find_ready_dictionaries`, and the
   hypothesis types and scrutinee of `match`. All need the same treatment; the stage-2
   roguelike hits `written_result` once the first two are fixed. **[run]**
2. **The kernel then fails on the same terms** unless lane 5 lands too: besides comparing calls
   by their unfoldings (opaque-definitions.md §8.1), it reads values back unfolded in
   `check_case` and in `substitute` (entering a branch), and with gluing off it can't do
   otherwise. With a scratch stand-in for lane 5, the repro checks in 0.2 s; without it, it
   runs past 120 s in the kernel. **[run]**

Two decisions: that what `rewrite` and `match` can see depends on a size cap (D1280), and no
syntax to lift the cap for now (D1281).

## 1. The problem, and every place it happens

The read-back function is `quote_as` (`crates/core/src/value.rs`): unfolded, it forces every
glued call to its unfolding and then visits every part, including the bodies of functions; a
stuck `Bool.ifThenElse c (_ => a) (_ => b)` is a neutral whose arguments are those two
functions, so both branches are visited and every call in them unfolded **[checked]**.
Its only limit is the 10-million-node size budget, which raises `E-RESOURCE`.

I made the scratch build print a backtrace whenever a read-back ran over a million nodes, then
removed the sites one at a time, re-running on the repro and on the stage-2 roguelike. These
are the read-backs that went past the limit, in the order they were met **[run]**:

| Site | What it reads back | Fixed by the scratch modes? |
|---|---|---|
| `matching.rs:582` `generalised` | the goal, to build the motive | yes (all modes) |
| `rewrite.rs:654`, `:668`, `:715` `rewrite_once` | the goal, to search it | yes |
| `matching.rs:337`, `:435`, `:508`; `rewrite.rs:672`, `:819` | the scrutinee, the hypotheses' types, the rule's left side: the forms that must be *found* in the goal | yes, read the same way as the goal |
| `matching.rs:641` `check_motive` | the motive again, to check its type | yes |
| `interfaces.rs:1618` `find_ready_dictionaries` | the goal, called first by `check_rewrite` | yes |
| `check.rs:3372` `written_result` | a function's result type, while propagating the expected type into an application (the stage-2 roguelike's `descendOutOfWalls dice state inside`) | yes |
| `unify.rs` `rename` | a metavariable's solution: in the first repro (§2), `Void.exfalso`'s result type | **no**; see §2 |
| kernel `core/src/check.rs:892` `check_case`, `:1246` `substitute`, `value.rs:2314` `conv` | the kernel's own read-backs and comparison | no: lane 5 (§6) |

(`zonk`'s `both_forms` also reads back unfolded but under a 10,000-node budget whose failure is
caught, `unify.rs:1450`; harmless, as opaque-definitions.md §2.2 found. The counterexample note
after a failure, `search_counterexample` → `sort_of`, also hits the limit, but only once a proof
has already failed.)

## 2. A minimal repro

`target/goal-readback/repro2.sw`, no opacity, shaped like `resolve` in the roguelike: a stuck
`if` whose untaken branch makes a record holding one field that is cheap to compute and huge to
write out, and proofs that only look at another field.

```stitchwort
-- k steps to evaluate (both operands are one value), 2^k nodes to write out.
def grow (x: Nat): Nat → Nat
  | 0 => x
  | Succ k =>
    let y := grow x k
    y * y

type Out = { big: Nat, small: Nat }

-- Like `descend`: not a case tree, and its result holds the expensive part.
def expensive (x: Nat): Out := { big = grow x 40, small = 0 }

-- Like `resolve`'s `Descend` branch.
def step (n: Nat) (x: Nat): Out := if n == 0 then expensive x else { big = 0, small = 0 }

theorem stepSmall (n: Nat) (x: Nat): (step n x).small = 0 :=
  match e: n == 0 with
    | True => rfl
    | False => rfl

theorem stepSmallOff (n: Nat) (x: Nat) (off: (n == 0) = False): (step n x).small = 0 :=
  rewrite off in rfl
```

Today both theorems fail with `E-RESOURCE` ("a value was too large to show") in 4.7 s; with
`grow x 3` (`control2.sw`) they check in 0.15 s. **[run]** Which options fix it is in §4.

A first version (`repro.sw`) proved an impossible branch with
`Void.exfalso (Bool.falseNotTrue (Eq.sym off))`. With the goal read-back fixed it still runs
away, in the unifier this time: solving `Void.exfalso`'s result type, `rename` looks through
`grow x 40` because a call that steps at once by matching is always looked through, and walks
the 2^40-node tree **[run]** (sampled: `solve` → `rename` → `rename_spine` →
`matches_at_once`). Folded read-back has the same exposure: `quote_folded` of `grow x 40`
expands it. Neither occurs in the roguelike, which never solves an unknown with a level in it,
so I left it out of this lane's scope and note it here.

### The stage-2 roguelike

`target/goal-readback/make_rogue2.py` turns a copy of `games/rogue` into the
"generate on the stairs" version of opaque-definitions.md §2.1. Its three `descend…` lemmas
that need the kernel to compare two generated levels (§2.3 there, lane 5's problem) are left
as `?`, so that the run measures the elaborator; I call that copy **rogue2q**. Today its four
`resolve…` theorems fail with `E-RESOURCE`, 12 s. **[run]**

## 3. How other systems decide how far to unfold

There is little literature on *this* question; the useful sources are implementation docs and
code. Two families:

**Never unfold the goal; match the pattern by its head, up to cheap unfolding.**

- *Lean 4 `rw`.* `kabstract` ([L1]) is the whole search. It only instantiates metavariables in
  the goal (`let e ← instantiateMVars e`) and walks it as written; a subterm is tried only if
  its head matches: "We detect subterms equivalent to `p` using key-matching. That is, only
  perform `isDefEq` tests when the head symbol of subterm is equivalent to head symbol of `p`."
  `Lean.MVarId.rewrite` ([L2]) calls it under the rewrite configuration, whose default is
  `transparency := Lean.Meta.TransparencyMode.reducible` ([L3]), so even the comparison
  unfolds only definitions marked reducible. If nothing is found, the error is "Did not find
  an occurrence of the pattern … in the target expression"; the user unfolds first.
  **[cited]**
- *SSReflect `rewrite`* ([R2]): "The matching algorithm compares a pattern term with a subterm
  of the goal by comparing their heads and then pairwise unifying their arguments (modulo
  conversion)", and "If the head of term is a constant, then it should be syntactically equal
  to the head symbol of the subterm." Its example: with `Definition f := g` and
  `Axiom H : forall x, g x = 0`, rewriting `f 3 + f 3 = f 6` with `H` "is not possible in
  SSR, because there is no occurrence of the head symbol `f` of the rewrite rule in the goal";
  the standard `rewrite` does it. Rocq's standard `rewrite` can use the same discipline
  through the `Keyed Unification` flag ([R1]): "The subterms, considered as rewriting
  candidates, must start with the same key as the left- or right-hand side of the lemma given
  to rewrite, and the arguments are then unified up to full reduction." **[cited]**

Stitchwort's `rewrite` already matches by key and compares by computing (`rewrite.rs`
`key`, "occurrences are looked for by their outer function and compared by computing"); what
differs is the term it searches: the fully unfolded goal, not the goal as written
**[checked]**. Moving to the Lean/SSReflect discipline is D484's "only the folded goal"
alternative, which this note doesn't reopen: it is the `folded` row of §4, and it breaks 55
AoC proofs.

**Normalise the goal, then abstract.** Agda's `with` (and so its `rewrite`, which "expands to
a with-abstraction") does what Stitchwort does today, and its manual names the cost
([A1], "Performance considerations"): the generalisation step "needs to normalise the
scrutinee and the goal and argument types to make sure that all instances of the scrutinee
are generalised", which is expensive if "the normalised form of the goal and argument types
are big, making finding the instances of the scrutinee expensive". **[cited]** The manual
offers no bound; its advice is to use something other than `with` in those cases.

**Read back minimal terms, check up to full reduction.** smalltt's glued evaluation ([K1])
keeps both an unfolded and a folded view of each top-level call, and its meta-solution
quotation starts "rigid" and, "When we hit an unfolding, we recurse into the spine in flex
mode, if that returns a possibly invalid term, we check the unfolding in full mode", so that
"top definitions are *never* unfolded in any meta solution, but we check validity up to full
beta-reduction". **[cited]** That is the shape of option (a) below: folded by default, unfold
only where needed. It works for smalltt's question (is this solution well-scoped?) because the
check is a yes/no on one variable set; for a search whose target can sit several calls deep
it needs a lookahead, which is where (a) failed.

None of these bound the *size* of what is unfolded; capped unfolding (§5) is my own
combination: Stitchwort's unfolded search, with smalltt's "keep the call" applied only where
the unfolding is too large to be anyone's business. **[inferred]**

## 4. The options, tried

Each option is a read-back mode in the scratch patch (`STW_RB=…`), used at every elaborator
site in the table of §1. `std` is the whole library loaded eagerly (the driver test
`the_index_holds_exactly_the_names_an_eager_load_makes`, which stops at the first file that
fails); `aoc` and `rogue` are `stitchwort check --no-cache` on the projects. The repro and
rogue2q are run with **`STW_KGLUE`, a scratch stand-in for lane 5** (§6), since without it
every option that gets past the elaborator then fails in the kernel. Error counts in a failing
project are lower bounds (a failing namespace stops its dependants), and its time isn't
comparable. **[run]**, all of it.

| Option | `std` (eager) | AoC | roguelike | repro2, with `STW_KGLUE` | rogue2q, with `STW_KGLUE` |
|---|---|---|---|---|---|
| today: unfolded | checks, 1.8 s | checks, 5.5 s | checks, 2.9 s | 2 × `E-RESOURCE`, 4.7 s | 4 × `E-RESOURCE`, 12.0 s |
| folded | fails (`Nat/Iterate.sw`) | 55 errors | 5 errors (`std/Result/Result.sw`) | 3 errors | 5 errors (`std/Result`) |
| (c1) `branches` | fails (4 errors) | 16 errors | 35 errors | checks, 0.14 s | 14 errors (3 still `E-RESOURCE`) |
| (c2) `stuck` | fails (3 errors) | 42 errors | 38 errors | checks, 0.16 s | 17 errors |
| (a) `look` | fails (3 errors) | 50 errors | 5 errors (`std/List/Toolkit.sw`) | checks, 0.21 s | 5 errors (`std/List/Toolkit`) |
| (b) bounded at 1,000,000, then folded | checks, 2.1 s | checks, 6.7 s | checks, 3.5 s | 3 errors | 4 × `E-RESOURCE` |
| **(d) `capped` at 100,000** | **checks, 1.7–2.1 s** | **checks, 5.1–6.0 s** | **checks, 2.7–3.5 s** | **checks, 0.21 s** | **elaborates**, 18.7 s (only the three `?`s left open) |

Without `STW_KGLUE`, every option except today's runs the repro past 150 s, in the kernel
(§6). Times for the projects vary by about 1 s between runs on this shared machine; the
capped rows are the range over five runs.

What each one is, and why it broke:

- **Today (unfolded).** For comparison.
- **(folded) Read back folded everywhere** (`quote_folded`). Breaks `std/Result/Result.sw`
  with exactly the error the opaque note saw ("`rewrite` found no
  `Result.traverseLoop f [y] xs` in the goal"), `std/Nat/Iterate.sw` in the eager load, and
  55 AoC proofs. Proofs need to see through calls (D484 had a reason).
- **(c1) `branches`: unfolded, but the two branches of a stuck `if` (`Bool.ifThenElse`,
  `Decidable.elim`) read folded.** The narrowest version of (c). Breaks proofs in all three
  projects. A typical one, `goalOnFloor` in the roguelike: the goal is `isWall level
  level.goal = False`, `isWall` is `¬isFloor`, and `isFloor` is a chain of `∨`s, each an `if`;
  the rule `middleInside level.exit` is about the second disjunct, which now sits in an `else`
  branch and reads `Area.contains level.exit level.goal`, while the rule's left side, read on
  its own, unfolds. "`rewrite` found no `Rogue.Area.contains level.exit (Rogue.Area.middle
  level.exit)` in the goal". The same goes for `match` scrutinees and the hypotheses whose
  types mention them (most of the `E-TYPE-MISMATCH`es). This is the general flaw of cutting
  by position: an expression's read-back depends on where it sits. It does fix the repro,
  where nothing needs to be found inside a branch.
- **(c2) `stuck`: unfolded, but any function passed to a stuck call read folded** (the branches
  of an `if`, and also the function of a stuck `List.map`). Strictly more cutting than (c1),
  and worse.
- **(a) `look`: folded, but a call is unfolded when its unfolding, read back folded, contains
  the target** (the rule's head, or the scrutinee); the probe is capped at 100,000 nodes. A
  one-level lookahead misses targets two calls deep (`isWall` → `isFloor` → `Area.contains`),
  and a deeper one is a full unfolding again. It breaks `std/List/Toolkit.sw` ("`rewrite`
  found no `List.sumBy ys f` in the goal"), so the roguelike's own namespace never checks.
- **(b) unfolded, but a read-back of more than 1,000,000 nodes starts again folded** (for the
  whole goal). Changes nothing in the three projects (none reaches the bound), but in the
  repro the fallback is the folded goal, so `n == 0` isn't in it ("`rewrite` found no
  `Decidable.toBool (Nat.decEq n 0)`"), the same failures as `folded`, after paying for the
  million nodes; rogue2q still fails with `E-RESOURCE`.
- **(d) `capped`: unfolded, but a call whose unfolding reads back to more than 100,000 nodes
  is written as the call** (§5).

Two variants of (d) I measured to choose its parameters:

| Variant (rogue2q unless said) | Result |
|---|---|
| cap 100,000, first scratch version (each overflow's size counted again by walking the term) | elaborates, 28–33 s |
| cap 100,000, sizes counted while reading back (the row in the table above) | elaborates, 18.7–18.8 s |
| cap 100,000, plus remembering "too big" per call cell across read-backs | elaborates, 28 s (on the first version; 33 s without it): the kept calls are mostly fresh cells, so little is remembered |
| cap 10,000 | elaborates, 9.3 s; **but AoC fails**: `Aoc/Day08/Proofs/Part2.sw:287`, a `rewrite` whose target lies in an unfolding of more than 10,000 nodes (200 calls kept folded across AoC) |
| cap 1,000 | rogue2q fails (2 errors) |
| a call's overflow aborts the enclosing call's read-back too (shared budget) | rogue2q 7.5 s, but breaks the repro: which call is kept then depends on where the budget ran out |
| version that may keep a call that steps at once (`grow x 17`) | later *folded* read-backs re-expand it (`quote_folded` looks through such calls), and the repro hits the size limit again in `check_tree` |

## 5. Recommendation: unfold every call, except one too big to write out

**Rule.** The read-back for searches (call it `quote_search`) is today's unfolded read-back
with one change: when it meets a glued call that doesn't step at once by matching, it reads the
call's unfolding back, and if that would take more than **100,000 nodes** it writes the call
itself instead, with its arguments read back by the same rule. A call that steps at once is
never kept (the folded read-back would only expand it again elsewhere, §4).

**Why this one.**

- *It is a function of the call alone*, not of where the call sits, so the goal, a rule's left
  side, a scrutinee and a hypothesis are read back alike and are still found in each other.
  That is what (c) lacked.
- *It changes nothing that works today*: at the 100,000 cap, `std`, AoC and the roguelike keep
  no call folded (`cap-folded=0`) and check in the same time. A proof can only change if some
  call's unfolding is between 100,000 nodes and the whole-goal limit of 10 million, and such a
  proof was within a factor of 100 of failing already. The cap of 10,000 shows the margin is
  real: one AoC proof needs more than 10,000.
- *It fixes the cases at hand*: the repro (0.19 s) and rogue2q (the four `resolve…` theorems
  elaborate), each with lane 5's stand-in.
- *It is a safety net, not a modelling tool.* When a body really is none of the proof's
  business, `opaque def` (lanes 1–4) says so, costs nothing, and the kernel respects it. The
  cap stops the checker from writing out a gigabyte of term nobody asked for; it is not how a
  program should hide its generator.

**What it costs.** Each kept call costs up to 100,000 nodes of wasted read-back, once per
read-back that meets it. On rogue2q that is 9,917 kept calls and 18.7 s, against 2.9 s for
today's game. That is too slow to ship as measured, so the lane must cut it (§7, step 2);
the scratch code is the simplest thing that answered "does the rule work", not a fast one.
*Speculative:* most of the waste is the same call (the same definition on the same arguments)
met again in a fresh value, so a cache keyed by the call (its definition and its arguments
read back folded), within one declaration's elaboration, should remove most of it.

**Error message.** When `rewrite` finds nothing and the goal's read-back kept a call, the
`E-REWRITE-NOTHING` gets a note: "`f a b` was left as it is: its unfolding is larger than
100,000 nodes"; likewise for the scrutinee note of `match`. (Implementation choice; the
wording is the lane's.)

**Implementation choices I've made** (not decisions for Matt): one `quote_search` used at
every site of §1's table, including `written_result`, `check_motive`,
`find_ready_dictionaries`, the scrutinee, the hypotheses and the rule's left side (all must
read alike, and rogue2q needs `written_result`); `rewrite/under.rs`'s read-backs of function
bodies go through it too; the cap is a field of `Limits` (so tests can lower it), not an
environment variable; the kernel is untouched in this lane.

## 6. What this lane does not fix: the kernel

The kernel checks without gluing (D483, `kernel.rs:21`), so it has no calls to keep: a motive
that mentions `expensive x` is evaluated to its full value and then read back or compared
**[checked]**. With the elaborator fixed and the kernel as it is, the repro runs past 120 s;
samples are all in the kernel's `conv`, and on rogue2q `E-RESOURCE` comes from the kernel's
`check_case` (`core/src/check.rs:892`, `let goal_term = cx.quote(goal)?`) and from
`substitute` (`:1246`, which reads every context value back to substitute a variable when
entering a branch). **[run]**

My stand-in for lane 5 (`STW_KGLUE`): the kernel runs with gluing on, compares two calls of
the same definition by their arguments first, and reads back folded in `Ctx::quote` and
`substitute`. With it the repro checks in 0.19 s, and `std`, AoC and the roguelike are
unchanged (1.8 s, 5.1 s, 2.7 s with capped unfolding). It is a stand-in to measure with, not a
design: lane 5 has to decide how a glued kernel stays trustworthy.

**So, for lane 5:** opaque-definitions.md §8.1 describes only "compare two calls of the same
definition by their arguments first". It also needs the kernel's read-backs in `check_case`,
`substitute` and `sort_of` to keep calls, or the kernel writes out the same untaken branches
the elaborator no longer does. Lane 6 can merge on its own (it changes nothing in the
projects), but the stage-2 roguelike checks only with both, or with `opaque def`.

## 7. Build plan (one lane) and tests

1. **`quote_search` in `crates/core/src/value.rs`**: the capped mode of `quote_as`, with the
   cap from `Limits` (default 100,000). Sizes counted as the term is built; a kept call
   written as `Term::Def` applied to its arguments read back by the same rule; never keep a
   call for which `matches_at_once` holds. A worklist like `quote_as` (the scratch version
   recursed per call; deep call chains would overflow the stack).
2. **The cost.** A per-declaration cache of calls found too big, keyed by the definition and
   the arguments read back folded; then measure rogue2q (the target: within twice today's
   game, 6 s) and report if it isn't reached.
3. **Use it** at every elaborator site in §1's table (and `rewrite/under.rs`), replacing
   `quote` there. `zonk`, goal display and hidden-argument solutions keep `quote_folded`.
4. **The notes** on `E-REWRITE-NOTHING` and on `match`'s scrutinee message, naming a call
   that was kept.
5. **Docs**: docs/core.md "Evaluation and conversion" (the rule); folded-calls.md D484 gets a
   line ("unfolded, up to a cap per call"); opaque-definitions.md §8.2 points here, and §8.1
   gets the kernel read-backs of §6.

**Tests** (lane tier: `task test:lane AREA=elab`, plus the named ones):

- *Repro as a regression test*, in the style of `crates/bench/tests/check_work.rs`
  `checking_does_not_compute_unneeded_values`: `repro2.sw` with `grow x 30` and `grow x 40`
  checks, and the elaborator's work (steps and nodes) is the same for both. It needs lane 5 to
  pass the kernel; until then the test elaborates only (or carries the `?`s rogue2q uses), and
  becomes the full check when lane 5 lands.
- *Unit tests in `value.rs`*: a call with a small unfolding reads back unfolded, exactly as
  `quote`; a call over a lowered cap reads back as the call with its arguments read back; a
  call that steps at once is never kept even over the cap; the result is the same wherever the
  call sits (inside an `if` branch and at the top).
- *An accept example* (`examples/accept/goal-readback-cap.sw`): the two theorems of the repro,
  once lane 5 is in; and a `rewrite` inside a branch of a stuck `if` whose target needs a
  small unfolding (the `goalOnFloor` shape), so (c)-style regressions show.
- *A snapshot test* of the new `E-REWRITE-NOTHING` note, with the cap lowered through
  `Limits`.
- *At merge*: the merge tier, and the AoC check and the roguelike's check time against today
  (5.1 s and 2.9 s here).

## 8. Decisions

- **D1280. What `rewrite` and `match e:` see: the unfolded goal, except that a call whose
  unfolding would take more than 100,000 nodes to write out is left as the call.** Today
  they see the goal fully unfolded, up to the 10-million-node limit, after which the proof
  fails with `E-RESOURCE`. With the cap, the proof goes on and sees `f a b` as it is; a rule
  about something inside that unfolding is then not found (with a note saying why). The
  alternatives are reading back folded, as Lean does (breaks 55 AoC proofs and
  `std/Result`), or leaving it as it is and relying on `opaque def` alone. [Yes, with the cap
  at 100,000: no existing proof changes, the repro and the stage-2 roguelike get through
  the elaborator, and opacity remains the way to say "don't look".]
- **D1281. No syntax to lift the cap for one proof, for now.** If a proof ever needs to see
  inside a call whose unfolding is that large, it can rewrite by the call's own equation first
  (`f.unfold` where one exists), or state the step with `calc`. A per-proof setting would be
  new surface for a case nothing has hit yet. [Yes: add one only when a proof needs it.]

## Sources

Read on 25–26 October 2026.

- [L1] Lean 4, `src/Lean/Meta/KAbstract.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean>
- [L2] Lean 4, `src/Lean/Meta/Tactic/Rewrite.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean>
- [L3] Lean API docs for `Lean.MVarId.rewrite`, showing the default `Rewrite.Config`: <https://florisvandoorn.com/LeanCourse24/docs/Lean/Meta/Tactic/Rewrite.html>
- [R1] Rocq reference manual source, "Rewriting with Leibniz and setoid equality" (`rewrite`, `Keyed Unification`, `pattern`): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/writing-proofs/equality.rst>
- [R2] Rocq reference manual source, "The SSReflect proof language" (matching, rewrite redex selection): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proof-engine/ssreflect-proof-language.rst>
- [A1] Agda user manual source, "With-Abstraction" (generalisation, performance considerations, `rewrite`): <https://github.com/agda/agda/blob/master/doc/user-manual/language/with-abstraction.lagda.rst>; rendered: <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [K1] smalltt README (glued evaluation, rigid/flex/full quotation): <https://github.com/AndrasKovacs/smalltt>

Coq's `pattern` ([R1]) abstracts "free subterms" the user names, so it never decides how far
to unfold; it is listed for completeness. I didn't read Lean's `simp` or `match` elaboration
for this note.
