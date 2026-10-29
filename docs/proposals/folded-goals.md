# Proposal: keeping definitions folded in goals

**Status:** proposed, awaiting Matt's review (draft 1, 28 October 2026). Design only; the scratch patches used to measure are not
committed. Ticket SW-742. Written against commit `7a7dfd00`. Related:
[folded-calls.md](folded-calls.md) (glued calls, D483, D484),
[goal-readback.md](goal-readback.md) (the size cap, D1280, deferred),
[opaque-definitions.md](opaque-definitions.md) (`opaque def`, `f.unfold`).

Labels: **[run]** checked for this note with the release CLI (`stitchwort check`, files in a
scratch folder, outputs copied as printed); **[checked]** read in the source at the place
given; **[cited]** read in the linked source; **[inferred]** my reasoning.

## Contents

0. [Summary](#0-summary)
1. [How it works today](#1-how-it-works-today)
2. [The findings, reproduced](#2-the-findings-reproduced)
3. [How other systems do it](#3-how-other-systems-do-it)
4. [Options](#4-options)
5. [Recommendation and staged plan](#5-recommendation-and-staged-plan)
6. [Questions for the owner](#6-questions-for-the-owner)
- [Sources](#sources)

## 0. Summary

Goals are *printed* folded already: the goal display reads values back with calls kept as
calls. They come out unfolded for three other reasons:

1. **`match e:` and `rewrite` rebuild the goal from its fully unfolded form.** The new goal is
   evaluated from that term, so it holds no calls at all, and every later display, search
   and hidden-argument solution sees the unfolding. This is most of what AoC 2024 days 2, 3,
   6 and 7 hit.
2. **The folded read-back unfolds too far after a call that steps at once.** `if True then
   concatenate a b else 0` prints as `List.foldLeft (…)`: having taken the `if`'s step, it
   keeps going through `concatenate` and `Nat.fromDigits`. A small bug.
3. **A `match` in a statement prints as its lifted helper**, `applyBig.%match1 operator left
   right`.

And `rewrite` *searches* the unfolded goal for the rule's unfolded left side, so a left side
with an unknown under a definition (`isSafe ?0`) can be lost (`?0.levels` is never found),
and `rewrite f` (unfold `f` by name) isn't a form at all.

I prototyped the central option, **folded-first with a completeness check**: search the
folded goal first, keep the result only if nothing was missed inside a call kept folded, and
otherwise do exactly what is done today. For `match` (and so `cases`) it keeps the goal
folded in 442 of AoC's generalisations, and for `rewrite` in 1,355 of AoC's rules; neither
changes any result in `std`, AoC, the roguelike or the 893 example files, and the `match`
version costs no measurable time. Folded-first *without* the check (Lean's
rule) breaks `std/Result/Result.sw`, because a scrutinee inside a call kept folded is no longer
generalised.

**Recommendation:** fix the read-back bug and print lifted matches as `match`; make `match`,
`cases` and `rewrite` folded-first with the completeness check; let `rewrite` fall back to a
folded search to solve a rule's unknowns; add `rewrite f` for one step of a definition. No
transparency levels. Five lanes, in §5.

## 1. How it works today

### 1.1 Values, calls and the two read-backs

The elaborator evaluates terms to values and reads values back to terms (normalisation by
evaluation). Since SW-257, a definition applied to all its arguments evaluates to a **glued
call**, `Value::Call`, which means its unfolding, computed the first time something looks
inside (docs/core.md, "Glued calls"). There are two read-backs:

- `quote` (`crates/core/src/value.rs:1884`) writes every call as its unfolding: the full normal
  form.
- `quote_folded` (`value.rs:1900`) writes a call as the call, `concatenate a b`, unless it
  **steps at once**: its case tree starts with a case on an argument that is already a
  constructor or a number (`matches_at_once`, `value.rs:576`). Then it is written as what it
  computes to, so `List.length (Cons x xs)` reads `Succ (List.length xs)`.

In `visit` (`value.rs:2038`), the folded mode keeps a call that doesn't step at once
(`:2054`); anything else goes through `force` (`:2065`), and `force` doesn't stop after one
step: it forces "until neither is at the top" (doc comment above `value.rs:500`), so it runs
on through every call the step returns. **[checked]** That is finding 2 of §0.

### 1.2 Goal display

Goals (`?` holes, the LSP's goals) are printed by `goals.rs:302` → `pretty::value_for_goal`
(`crates/core/src/pretty.rs:263`) → `quote_folded` (`pretty.rs:288`). Error messages use the
same read-back (`Ctx::show`). So display keeps every call the value still holds. **[checked]**

A statement's `match` is lifted to a helper definition named `owner.%matchN`
(`crates/elab/src/lift.rs:489`). The helper's call is a glued call stuck on the scrutinee, so
the goal prints it by that name. Diagnostics rewrite such names to "(match …)"
(`lift.rs:1246`, `explain_lifted`), but the printed goal doesn't. **[checked, run]**

### 1.3 How `match e:` builds the goals of its arms

`generalised` (`crates/elab/src/matching.rs`) reads back the scrutinee (`:341`), every
variable's type (`:552`) and the goal (`:626`) with `quote`, fully unfolded, then replaces
each syntactic occurrence of the scrutinee by a new variable (`Generalise::apply`, `occurs`,
`:720`). The goal of each arm is that term evaluated with the constructor put in. It has to
unfold: in `(step n x).small = 0`, `match e: n == 0` must find `n == 0` inside `step`. The
cost is that the arms' goals are evaluated from a term with no calls in it. `cases` splits
through the same function (`cases.rs:1079` → `generalised_named`). A `match` on a plain
variable doesn't generalise; it substitutes, keeping calls (`substitute_folded`,
`lib.rs:4103`). **[checked]**

### 1.4 How `rewrite` searches and builds the next goal

`rewrite_once` (`crates/elab/src/rewrite.rs:656`) reads back the goal with `quote` (`:669`)
and the rule's left side the same way (`:687`, again `:834`), takes the left side's **key**
(its head and number of arguments, `key`, `:1199`), and visits every subterm of the goal with
that key, comparing it with the left side by unification. The motive is the goal term with
the occurrences replaced by a variable; the next goal is that motive evaluated and applied
to the right side (`:916`). This is D484: the search sees the unfolded goal, so that proofs
can rewrite inside definitions without saying so. Two consequences:

- The next goal holds no calls, except those that came in with the rule's right side.
- The left side is searched for in its unfolded form. If the rule leaves an argument to be
  found (`isSafeCorrect _`), its unfolding can mention the unknown in a form unification
  can't solve (`?0.levels`, a field of an unknown), and nothing is found.

`rewrite f`, for a definition `f`, is `E-REWRITE-RULE` (`rewrite.rs:459`): a rule must prove
an equation. Definitions by well-founded recursion, and opaque ones, have a generated
equation `f.unfold` (docs/syntax.md, "`f.unfold`"), so `rewrite f.unfold x in` works for
those, but nothing exists for an ordinary definition. **[checked]**

### 1.5 What already exists for restating a goal

A type annotation does what Lean's `show` and `change` do: `(? : concatenate a 0 = concatenate
a 0)` after a `rewrite` that unfolded the goal shows the goal as written, and the kernel
accepts it because the two are convertible. A `_` in the annotation is filled from the goal,
in its unfolded form. **[run]** (§2, repro 6).

## 2. The findings, reproduced

The AoC findings are in aoc/NOTES-2024.md: day 2 item 3 ("`rewrite` misses a lemma once the
goal has unfolded it"), day 3 item 8, day 6 items 3 and 4 ("Goals unfold too far"), day 7
item 5 ("Goals unfold too far, and a `match` in a statement is opaque"). Each is reduced here
to a few lines. All **[run]** on `7a7dfd00`; the outputs are trimmed to the goal or error
line.

All repros start with:

```stitchwort
import Std (List, Nat)

def concatenate (left: Nat) (right: Nat): Nat := Nat.fromDigits ((Nat.digits left).append (Nat.digits right))
```

| Finding | Where the unfolding happens | Repro |
|---|---|---|
| Day 7: `concatenate` shown as `List.foldLeft …` | a call that steps at once is forced through (`value.rs:2065`); and the arms of `match e:` (`matching.rs:626`) | 1, 2 |
| Day 3: `sumBy` shown as `foldLeft`, a lemma about `sumBy` then doesn't apply | `rewrite`'s next goal is built from the unfolded goal (`rewrite.rs:669`, `:916`) | 3 |
| Day 2: `rewrite isSafeCorrect _` finds nothing | the rule's left side is searched for unfolded (`rewrite.rs:687`) | 4 |
| Day 6: `match patrolled: lab.patrol` runs out of resources | `match` must unfold the goal to find the scrutinee (`matching.rs:626`) | 5 |
| Day 6: `rewrite onRoute` (unfold by name) | not a form (`rewrite.rs:459`) | 3 |
| Day 7: `%match1` in the goal | the lifted helper's call printed by name (`lift.rs:489`) | 7 |

**Repro 1: the arms of `match e:`.**

```stitchwort
theorem afterMatch (flag: Bool) (a: Nat) (b: Nat): (if flag then concatenate a b else 0) = concatenate a b :=
  match e: flag with
    | True => ?
    | False => ?
```

```text
⊢ List.foldLeft (List.append (Nat.digitsAcc a []) (Nat.digitsAcc b [])) 0 (acc digit => acc * 10 + digit) = List.foldLeft (List.append (Nat.digitsAcc a []) (Nat.digitsAcc b [])) 0 (acc digit => acc * 10 + digit)
⊢ 0 = List.foldLeft (List.append (Nat.digitsAcc a []) (Nat.digitsAcc b [])) 0 (acc digit => acc * 10 + digit)
```

The same statement with `?` instead of the `match` prints `concatenate a b = concatenate a b`.

**Repro 2: a call that steps at once.**

```stitchwort
theorem stepsAtOnce (a: Nat) (b: Nat): (if True then concatenate a b else 0) = concatenate a b := ?
```

```text
⊢ List.foldLeft (List.append (Nat.digits a) (Nat.digits b)) 0 (acc digit => acc * 10 + digit) = concatenate a b
```

The right side, not inside a step, stays folded; the left goes through `if True`, then
`concatenate`, then `Nat.fromDigits`, stopping only at `List.foldLeft` (whose list isn't a
constructor). Day 7's spec reaches `concatenate` through `combine Concatenate value last`,
which steps at once in the same way.

**Repro 3: after a `rewrite`, and `rewrite` by name.**

```stitchwort
def total (xs: List Nat): Nat := xs.sumBy (x => x * 2)

theorem totalEq (xs: List Nat): total xs = 2 * List.sum xs := ?

theorem useTotal (xs: List Nat) (ys: List Nat) (same: xs = ys): total xs + 0 = 2 * List.sum ys :=
  rewrite Nat.addZero (total xs), totalEq xs in ?

theorem byName (xs: List Nat): total xs = List.sumBy xs (x => x * 2) :=
  rewrite total in rfl
```

```text
⊢ List.sum xs + (List.sum xs + 0) = List.foldLeft ys 0 Nat.add + (List.foldLeft ys 0 Nat.add + 0)
[E-REWRITE-RULE] Error: `rewrite` needs a proof of an equation
  this has type `List Nat → Nat`, which isn't an equation
```

The left side came in with the rule's right side and kept `List.sum`; the right side, read
back from the goal, lost it. (`2 * x` printing as `x + (x + 0)` is the step-at-once rule
working as designed: `Nat.mul` cases on the literal.)

**Repro 4: a rule whose argument is left to `rewrite`.**

```stitchwort
type Report = { levels: List Nat }

def isSafe (report: Report): Bool := report.levels.all (level => level < 3)

def safe (report: Report): Bool := !(report.levels.any (level => 3 <= level))

theorem isSafeCorrect (report: Report): isSafe report = safe report := ?

theorem leftOpen (xs: List Nat): isSafe { levels = xs.reverse } = safe { levels = xs.reverse } :=
  rewrite isSafeCorrect _ in rfl
```

```text
[E-REWRITE-NOTHING] Error: `rewrite` found no `isSafe ?0` in the goal
  Note 1: goal: `isSafe { levels = List.reverse xs } = safe { levels = List.reverse xs }`
  Note 2: the search compares what terms compute to: it looked for `List.all ?0.levels (level => level <= 2)`, what `isSafe ?0` computes to, in what the goal computes to
```

The call `isSafe { levels = … }` is right there in the folded goal. With the argument given
(`isSafeCorrect { levels = xs.reverse }`) it checks.

**Repro 5: `match` must look inside a definition** (the shape of goal-readback.md §2).

```stitchwort
def grow (x: Nat): Nat → Nat
  | 0 => x
  | Succ k =>
    let y := grow x k
    y * y

type Out = { big: Nat, small: Nat }

def expensive (x: Nat): Out := { big = grow x 40, small = 0 }

def step (n: Nat) (x: Nat): Out := if n == 0 then expensive x else { big = 0, small = 0 }

theorem stepSmall (n: Nat) (x: Nat): (step n x).small = 0 :=
  match e: n == 0 with
    | True => rfl
    | False => rfl
```

```text
[E-RESOURCE] Error: ran out of resources: a value was too large to show
```

`n == 0` appears only inside `step`, so the goal must be unfolded to find it, and the unfolded
read-back writes out `grow x 40`. With `grow x 3` it checks. Keeping goals folded does not fix
this one; it is goal-readback.md's problem (its size cap, D1280, deferred) and `opaque def`'s.

**Repro 6: restating with an annotation** (what exists today).

```stitchwort
theorem restatedHoles (flag: Bool) (a: Nat) (b: Nat): (if flag then concatenate a b else 0) = concatenate a b :=
  match e: flag with
    | True => (?: concatenate a b = _)
    | False => ?
```

```text
⊢ concatenate a b = List.foldLeft (List.append (Nat.digitsAcc a []) (Nat.digitsAcc b [])) 0 (acc digit => acc * 10 + digit)
```

**Repro 7: a `match` in a statement.**

```stitchwort
type Operator = | Add | Multiply

def apply (operator: Operator) (left: Nat) (right: Nat): Nat :=
  match operator with
    | Add => left + right
    | Multiply => left * right

theorem applyBig (operator: Operator) (left: Nat) (right: Nat):
    (match operator with
      | Add => left + right
      | Multiply => left * right) = apply operator left right := ?
```

```text
⊢ applyBig.%match1 operator left right = apply operator left right
```

`rfl` proves it: two helpers with the same case tree are compared by their trees (docs/core.md,
"Conversion", D1091). So day 7's "nothing could be proved about it by name" is a display
problem, not a conversion one. Day 6's `(lab.withObstruction blocker).ahead guard = lab.ahead
guard` (two calls of one helper on different arguments) is a conversion question and isn't
covered here.

## 3. How other systems do it

**Lean 4** keeps goals as the expressions the user wrote and unfolds only on request.

- *Display.* The goal is printed after only instantiating metavariables:
  `ppExpr (← instantiateMVars mvarDecl.type)` (`Lean/Meta/PPGoal.lean`) [L1]. Nothing reduces
  it. Calls of `match` helpers (`List.map.match_1`) print as `match … with` again: the
  delaborator `delabAppMatch` "Delaborates applications of "matchers"", under option
  `pp.match`, "(pretty printer) disable/enable 'match' notation", on by default [L2].
- *`rw` and `simp` see through very little.* Transparency levels "form a linear order:
  `none < reducible < instances < implicit < default < all`"; `reducible` "Only unfolds
  `[reducible]` definitions. Used for speculative `isDefEq` checks (e.g., discrimination tree
  lookups in `simp`, type class resolution)"; `instances` "Also unfolds `[instance_reducible]`
  definitions (auto-applied to type class instances by the `instance` command)" [L3]. `rw`'s
  configuration has `transparency : TransparencyMode := .reducible` [L4]. Its search,
  `kabstract`, "detect[s] subterms equivalent to `p` using key-matching. That is, only perform
  `isDefEq` tests when the head symbol of subterm is equivalent to head symbol of `p`" [L5]. An
  ordinary `def` is semireducible: "not unfolded by potentially expensive automation such as
  type class instance synthesis or simp, but they are unfolded while checking definitional
  equality" [L6].
- *Unfolding on request.* `unfold`: "For non-recursive global definitions, this tactic is
  identical to `delta`. For recursive global definitions, it uses the "unfolding lemma"
  `id.eq_def` … Only one level of unfolding is performed, in contrast to `simp only [id]`,
  which unfolds definition `id` recursively." `rw [f]`: "If `e` is a defined constant, then
  the equational theorems associated with `e` are used. This provides a convenient way to
  unfold `e`." `delta` "is a low-level tactic, it will expose how recursive definitions have
  been compiled by Lean." `dsimp` "only applies theorems that hold by reflexivity" [L7].
- *Restating.* "`change tgt'` will change the goal from `tgt` to `tgt'`, assuming these are
  definitionally equal"; "`show t` finds the first goal whose target unifies with `t`" [L7],
  checked with `isDefEq` (`Lean/Elab/Tactic/Change.lean`).
- *`match`/`if` in a goal.* `split` "is useful for breaking nested if-then-else and `match`
  expressions into separate cases" [L7]. **[cited]**

So in Lean a proof that needs to see inside `isSafe` says `unfold isSafe` or `simp only
[isSafe]` first; a folded goal is the default and stays so.

**Agda** reduces some functions when displaying goals: "only those functions that match on a
constructor pattern or a projection copattern will be reduced, as well as primitive functions
of Agda. For example, (suc x) + y will be simplified to suc (x + y) but id 42 will be printed
as is"; with a prefix, "C-u to print the term without any simplification. C-u C-u to print
the full normal form" [A1]. That is the rule `quote_folded` already follows (`matches_at_once`),
taken one step. Its `with` abstraction (and so `rewrite`) normalises the goal first, at a cost
the manual warns about (goal-readback.md §3). **[cited]**

**Rocq** has reduction tactics that try to keep names. `simpl` "Reduces a term to something
still readable instead of fully normalizing it" and "unfolds constants only if they lead to an
ι-reduction"; `cbn` is "a more principled, faster and more predictable replacement for simpl"
that "may unfold constants even when they cannot be reused in recursive calls". `unfold`
"Applies delta-reduction to the constants specified … then reduced to βιζ-normal form", and
`change` "Replaces terms with other convertible terms" [R1]. Per constant, `Arguments f :
simpl never` stops `simpl`/`cbn` unfolding it [R2], and `Opaque`/`Transparent`/`Strategy`
"fine-tune the strategy for unfolding constants, both at the tactic level and at the kernel
level" [R1]. **[cited]**

The common thread: goals are kept as written; matching sees through a small, chosen set of
definitions; anything more is a request. Stitchwort's D484 chose the opposite for search
(see everything), which is why AoC proofs rarely unfold by hand; the options below keep that
power and change only what the user sees and what is kept.

## 4. Options

Everything here is elaboration. The kernel checks every proof term against the declared type
up to conversion, and a folded and an unfolded goal are convertible, so none of these can make
an unsound proof pass; the risk is only proofs that stop or start checking. **[inferred]**

### A. Fix the folded read-back, and print lifted matches as `match`

*What changes.* In `visit` (`value.rs:2065`), a call that steps at once takes **one** step and
the result is visited again in folded mode, instead of being forced through. The pretty
printer writes a call of a lifted helper `f.%matchN args` as the `match` it came from,
`match operator with | Add => left + right | Multiply => left * right`, shortened like any long
term.

*Risks.* `quote_folded` is also used for hidden-argument solutions, zonking, lifted helper
types and `cases`'s atoms (`cases.rs:1053`), so smaller terms there change hashes and possibly
which atoms `cases` sees. Display only for the `match` printing.

*Work.* Small: one lane for both, measured over `std`, AoC and the examples like the
folded-calls stages.

*Fixes:* repro 2 (day 7's `combine Concatenate`), repro 7.

### B. Folded-first with a completeness check (`match`, `cases`, `rewrite`)

*What changes.* Before today's unfolded search, try the folded one:

1. Read back the goal (and, for `match`, the scrutinee and the hypotheses' types) folded.
2. Find the occurrences there (for `rewrite`, the left side read back folded, keyed by its
   head as written, so `isSafe`, not `List.all`).
3. **Completeness check:** replace the visible occurrences by a fresh variable, read the result
   back *unfolded*, and check that no occurrence is left. One that is left was hidden inside a
   call kept folded.
4. If found and complete, the motive is the folded term: the arms' goals and the next goal keep
   their calls. Otherwise, do exactly what is done today.

The check is what keeps every existing proof as it is: if the folded motive is used, it
abstracts the same occurrences as today's (as values; the terms differ only in calls kept),
so the arms compute the same. **[inferred, and run below]**

*Why the check is needed.* Without it (Lean's rule), `std/Result/Result.sw` stops checking:
in `Result.traverseCons`, `match e: f x` against `Result.traverse (Cons x xs) f = Result.flatMap
(f x) …` finds the visible `f x` on the right but not the one inside `Result.traverse`, so the
left side no longer computes in the arms, and the next `rewrite` finds nothing
(`` `rewrite` found no `Result.traverseLoop f [y] xs` in the goal ``). A `match` also has to
check its hypotheses: without that, `List.foldMaxMem` in `std/List/Toolkit.sw` fails, because
`e: List.foldLeft ys (Nat.max start y) Nat.max = …` holds `Nat.leq start y` only inside
`Nat.max`, so `e` was not refined. **[run]**

*Measured* (scratch patch, `match` and so `cases`; release build; AoC timings on a machine
shared with other lanes):

| | today | folded-first, with the check |
|---|---|---|
| `std` (loaded by every check) | checks | checks |
| AoC, `check --no-cache` | checks, 16.1 s user | checks, 14.8 s user |
| AoC generalisations (std included) | all unfolded | 442 folded; 397 unfolded as today (356 not visible in the folded goal, 41 visible but incomplete) |
| roguelike, `check --no-cache` | checks | checks (158 folded) |
| `examples/accept` and `examples/reject` (893 files), exit codes | — | the same on every file |
| repro 1, `True` arm | `List.foldLeft … = List.foldLeft …` | `List.foldLeft … = concatenate a b`, then `concatenate a b = concatenate a b` with option A |

For `rewrite`, the scratch patch checks completeness more bluntly: it runs today's search and
the folded one, and keeps the folded result only if the two next goals unify (otherwise it
runs today's again). That keeps exactly the results a real check would, at more cost, so its
counts are the measure, not its time:

| `rewrite` rules | kept folded (same next goal) | found folded, but a different goal (unfolded used) | nothing found folded (unfolded used) |
|---|---|---|---|
| `std` (plus repro 3) | 184 | 0 | 7 |
| AoC (std included) | 1,355 | 8 (5 of them only because an unknown was still open) | 347 |
| roguelike (std included) | 639 | 0 | 55 |

With both patches, AoC and the roguelike check, and the 893 example files give the same exit codes as today.
Repro 3's `afterRewrite` now shows `concatenate a 0 = a`, and `useTotal` shows `List.sum ys`
where it showed `List.foldLeft ys 0 Nat.add`. **[run]** (A first version compared the goals
with the kernel's `conv` and reported hundreds of spurious differences; unification, which
compares two calls by their arguments first, doesn't. The lane should compare with the
elaborator's unification, or better, check completeness directly as `match` does.)

*Risks.* (1) Cost: the check is one unfolded read-back, which today's search does anyway, so a
folded result costs about two read-backs and a fallback three. AoC didn't move; a goal near the
size limit could, and the cap of goal-readback.md (D1280) would bound it. (2) Messages: a goal
that keeps its calls can show `rewrite`'s "found nothing" note in folded form, which is the
point. (3) Consumers that read the goal folded (`cases`'s atoms, `ring`'s atoms, `auto`) now
meet calls where they met unfoldings. None of the projects changed, but this is where a
regression would show.

*Work.* Two lanes: `match`/`cases` (the patch is about 70 lines in `generalised`), then
`rewrite` (the search, the open-rule path in `rewrite/under.rs`, and `rewrite … at h`).

*Fixes:* repro 1 and day 3 (the arms and the next goal keep `concatenate`, `sumBy`); day 2's
display. Not repro 5.

### C. A folded search to solve the rule's unknowns

*What changes.* When today's search finds nothing and the rule has unknowns, search the folded
goal for the folded left side (`isSafe ?0`, keyed `isSafe`) only to **solve the unknowns**,
then search again as usual with the solved rule. `replace_solving_instances` (`rewrite.rs:938`)
already does this for instances ("Searching by instances only solves the rule's unknowns: the
equation is then computed again and searched for as usual"), so this is one more attempt in
the same place.

*Not as simple as it looks.* The scratch `rewrite` patch of B searches the folded goal for
`isSafe ?0` and still finds nothing in repro 4 **[run]**: comparing two calls of the same
definition by their arguments never solves a metavariable (folded-calls.md, stage 2, kept so
hidden-argument solutions don't depend on folding). The by-instances attempt already compares
with `unify_solving_arguments`, which may solve the rule's own unknowns; C must use that
comparison in the folded attempt. Not prototyped.

*Risks.* None to existing proofs: it runs only where today's ends in `E-REWRITE-NOTHING`.

*Work.* Part of B's `rewrite` lane.

*Fixes:* repro 4 (day 2, `isSafeCorrect _`).

### D. `rewrite f`: one step of a definition, by name

*What changes.* A rule that names a definition `f` (with or without arguments) is read as
`f`'s one-step equation, `f x… = body`, as Lean's `rw [f]` uses equation lemmas. Where `f.unfold`
exists (well-founded and opaque definitions) it is that; otherwise the elaborator states the
equation from the body and proves it by `rfl`. A case-tree definition takes its step only where
the case can choose (its argument is a constructor), and otherwise `rewrite f` says which
argument it needs split first.

With B, this is what a proof uses when the folded search finds nothing and the user wants the
inside of `f` visible without unfolding everything. `show`/`change` need nothing new: an
annotation already restates the goal (repro 6).

*Risks.* For an opaque `f` without `unfolding f`, the body is hidden, so the rule must be
refused as `f.unfold`'s use is today. A case tree read back as a term needs printing (a `match`,
as in A).

*Work.* One lane, after A.

*Fixes:* day 6's `rewrite onRoute`; repro 3's `byName`.

### E. Transparency levels

*What changes.* Mark definitions (`@[reducible]` in Lean, `abbrev`) that the folded search
sees through, so a rule about `isFloor` matches a goal written with `isWall := !isFloor`
without unfolding the rest.

*Why not now.* With B's fallback, whatever isn't found folded is still found unfolded, as today;
levels would only matter if the fallback were removed. Stitchwort already has the two levels the
kernel needs (`opaque def` and the rest), plus the step-at-once rule, which is Agda's display
rule and plays the part of Lean's `reducible` for constructor-matching definitions. A new
attribute is surface with no proof that needs it.

*Work.* Attribute, search changes, docs: a design note of its own, if a trigger appears.

### F. Read back with both forms (a refolding read-back)

*What changes.* Today's unfolded search unchanged; the read-back also remembers, for each
subterm that came from a call, the call itself; after the occurrences are replaced, any call
whose unfolding holds no occurrence is written back folded. Finds exactly what today finds,
always, and keeps folded whatever wasn't touched, including where B falls back.

*Risks.* A call whose *arguments* hold an occurrence (`concatenate (f x) b`, matching on
`f x`) stays unfolded unless more work proves the folded form equal. A new term form for the
read-back, in `value.rs`.

*Work.* Larger than B (a read-back mode and a pass after replacement), and it doesn't reduce
cost. Worth it only if B's fallback rate turns out to matter in practice.

## 5. Recommendation and staged plan

A, B with C, and D. Not E or F now.

B keeps D484's promise (every proof that checks today still checks, and searches still see
through definitions) while the goals people and agents read keep the names they wrote. C and
D cover the two cases where today's search can't help: an unknown under a definition, and
asking for one step. A is a bug fix that makes all of it visible.

Each stage is one lane, with named tests, the merge tier at merge, and AoC and the roguelike
checked before and after (results and time).

1. **Folded read-back steps once (A, first half).** `visit` takes one step of a call that steps
   at once and visits the result folded. Unit tests in `value.rs` (repro 2's shape; `List.length
   (Cons x xs)` still reads `Succ (List.length xs)`); goal snapshots for repros 1 and 2;
   hash-stability snapshots re-recorded.
2. **Lifted matches print as `match` (A, second half).** The printer looks up a lifted helper's
   case tree and prints the `match`, shortened past the goal limit. Snapshot for repro 7.
3. **`match` and `cases` folded-first, with the check (B).** In `generalised`; the scratch
   patch's rule, made one function (the check over the goal and the copied hypotheses). Accept
   examples: repro 1's arms keep `concatenate`; `Result.traverseCons`'s shape (hidden
   occurrence, falls back); `List.foldMaxMem`'s shape (hidden in a hypothesis, falls back).
   A counter in `--timings`-style output of folded/fallback, for measuring.
4. **`rewrite` folded-first, with the check, and the folded search for unknowns (B, C).** In
   `rewrite_once` and `rewrite/under.rs`, for the goal and for `at h`. Accept examples: repro 3's
   next goal keeps `List.sum`; repro 4 checks; a rule whose only occurrence is inside a folded
   call still rewrites (fallback). Update D484's text in folded-calls.md.
5. **`rewrite f` (D).** Elaborating a definition name as a rule; `f.unfold` where it exists.
   Accept: repro 3's `byName`, an opaque `f` refused with the existing message, a case-tree `f`
   on a constructor. Reject snapshot: a case-tree `f` on a variable. docs/syntax.md section.

Stages 1 and 2 are independent of each other and of 3; 4 builds on 3's helper; 5 can go any
time after 2. Then rewrite the AoC 2024 workarounds named in the notes (day 3's `Eq.trans`
chain, day 6's `Eq.cong` with `onRoute`'s body) as a check that they're no longer needed.

## 6. Questions for the owner

- **Should `rewrite` and `match` keep the goal folded when nothing is lost by it, and fall back
  to today's fully unfolded behaviour otherwise?** The alternative is Lean's rule (search only
  the folded goal; unfold by hand), which breaks `std` and, per goal-readback.md, 55 AoC proofs.
  [Yes: folded-first with the completeness check. No proof changes, and goals keep their names.]
- **When a rewrite rule has an unknown argument and nothing is found, may `rewrite` look for
  the rule as written in the folded goal to fill it in?** It only turns today's "found nothing"
  into a success; it never changes a proof that works. [Yes.]
- **Should `rewrite f` with a definition's name mean "unfold `f` one step"?** This is Lean's
  `rw [f]`. The alternative is a new `unfold f in e` form, a second keyword next to `unfolding`.
  [Yes, `rewrite f`; no new keyword.]
- **Should a `match` written in a statement print in goals as the `match` itself rather than
  as `owner.%match1`?** Lean prints `match … with` for its helpers. [Yes, shortened like other
  long terms.]
- **Should Stitchwort add transparency levels (a "reducible" mark that searches see through)
  now?** [No: with the fallback nothing needs them; revisit if a proof does.]

## Sources

Read on 28 October 2026.

- [L1] Lean 4, `src/Lean/Meta/PPGoal.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/PPGoal.lean>
- [L2] Lean 4, `src/Lean/PrettyPrinter/Delaborator/Options.lean` (`pp.match`) and `Builtins.lean` (`delabAppMatch`): <https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Options.lean>, <https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Builtins.lean>
- [L3] Lean 4, `src/Init/MetaTypes.lean` (`TransparencyMode`): <https://github.com/leanprover/lean4/blob/master/src/Init/MetaTypes.lean>
- [L4] Lean 4, `src/Init/Meta/Defs.lean` (`Rewrite.Config`), and the tactic reference for `rw`: <https://github.com/leanprover/lean4/blob/master/src/Init/Meta/Defs.lean>, <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rw>
- [L5] Lean 4, `src/Lean/Meta/KAbstract.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean>
- [L6] Lean reference, "Reducibility": <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility>
- [L7] Lean 4, `src/Init/Tactics.lean` (`unfold`, `delta`, `rw`, `dsimp`, `change`, `show`, `split`), and `src/Lean/Elab/Tactic/Change.lean`: <https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean>, <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Change.lean>; tactic reference: <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- [A1] Agda manual, Emacs mode, "Keybindings": <https://agda.readthedocs.io/en/latest/tools/emacs-mode.html>
- [R1] Rocq reference manual, "Rewriting with Leibniz and setoid equality" (`simpl`, `cbn`, `unfold`, `change`, `Opaque`, `Transparent`, `Strategy`): <https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html>
- [R2] Rocq reference manual, "Setting properties of a function's arguments" (`simpl never`): <https://rocq-prover.org/doc/master/refman/language/extensions/arguments-command.html>
