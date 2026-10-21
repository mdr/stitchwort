# Proposal: equation lemmas, and lemmas about a `match` inside a definition

**Status:** draft 1, 21 October 2026. Design only: nothing here is built. Ticket SW-194,
decision D223 (Matt, 21 October 2026: write this note). Related: SW-193 (`match h:` doesn't
refine a `let`-bound proof, now fixed), SW-192 (AoC day 7). Decisions D226 to D233
([§9](#9-decisions)) accepted as recommended (Matt, 21 October 2026): D226 to D230 yes,
D231 to D233 not now. No external review (D235). Well-founded recursion, which may bring
D231 back, is in the backlog.

**The short answer.** The day 7 workaround (a copied helper `leftReach` and an equation
`reachStep`) is not needed today: I removed both and the proof checks with two small changes
to one step ([§3.4](#34-the-proof-without-the-workaround) **[run]**). The day 7 proof got
stuck for two other reasons: a `let`-bound hypothesis that `match e:` doesn't refine
(SW-193), and an argument written out in full where `_` was needed. What is genuinely
missing is smaller than the ticket assumed: **a lemma can't *state* anything about a
`match` written inside a definition**, because the generated function has no name source can
write. A local `def` already gives it one (`reach.left`), but its parameters come in an order
nobody would guess. So I recommend documenting the proof pattern, making local definitions'
parameters predictable, improving three messages, and **not** generating Lean-style equation
lemmas yet ([§8](#8-recommendation-and-build-plan)).

This note can be read without knowing the codebase ([§1](#1-stitchwort-in-brief)). Code
references were checked at commit `cc5df60`. Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given, or in a
  source listed at the end ([L1], [A1] and so on);
- **[run]**: a Stitchwort or Lean program run on 21 October 2026 (Stitchwort's release CLI
  at `cc5df60`; Lean 4.34.1 from nixpkgs). The programs are scratch files, not committed;
  each is quoted where it's used;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [0. Summary](#0-summary)
- [1. Stitchwort in brief](#1-stitchwort-in-brief)
- [2. How definitions are elaborated and unfolded today](#2-how-definitions-are-elaborated-and-unfolded-today)
- [3. Day 7, reproduced](#3-day-7-reproduced)
- [4. How other languages do it](#4-how-other-languages-do-it)
- [5. What is actually missing](#5-what-is-actually-missing)
- [6. Options](#6-options)
- [7. Costs and risks](#7-costs-and-risks)
- [8. Recommendation and build plan](#8-recommendation-and-build-plan)
- [9. Decisions](#9-decisions)
- [Sources](#sources)

## 0. Summary

- **The problem as reported** (`aoc/src/Aoc/Day07/Proofs/Part1.sw:61-70`,
  `docs/aoc-2025.md`, day 7 pain point 2): `reach` has a `match` inside one of its arms. The
  compiler turns that `match` into a generated function, `reach.%match1`, whose name source
  can't write. The proof copied the `match` into a named `leftReach` and proved an equation
  `reachStep` by `rfl` in each case (`Part1.sw:162-170`), then used it in `fallKeeps`
  (`Part1.sw:287-315`).
- **What I found** ([§3](#3-day-7-reproduced)), by running variations of the proof:
  1. Matching on the condition (`match e: charAt line c == '^' with`) *does* refine a
     hypothesis about `reach`, as long as the hypothesis is a parameter or a lambda's
     variable, not a `let` (§3.2, `r1` **[run]**).
  2. The day 7 step used a `let` (`let hr := …`), and `let`-bound proofs aren't refined
     (§3.3, `r8` and `V0` **[run]**; this is SW-193, already being fixed).
  3. Writing the hypothesis's arguments out in full inside a branch also fails, because
     what you write isn't refined, only the goal and the variables in scope are (`V1`
     **[run]**). With `_` for those arguments, the unnameable left branch is filled in by
     unification and never has to be written.
  4. With both fixed, the whole proof checks with `leftReach` and `reachStep` deleted, and
     its 17 tests pass (`V2`, §3.4 **[run]**).
  5. What can't be done: write a *statement* that mentions the inner `match`. Writing the
     same `match` again in a lemma makes a second generated function, which is a different
     definition and isn't equal to the first while `c` is unknown (`r3`, `r5`, `r6`
     **[run]**).
- **Prior art** ([§4](#4-how-other-languages-do-it)): Lean generates equation lemmas
  (`f.eq_1`, … one per leaf of the case tree, and `f.eq_def`) on demand, and its nested
  `match` becomes a *closed* "matcher" whose branches are passed in as functions, so the
  same `match` written in a lemma lines up with the definition's **[run]**. Rocq's Equations
  plugin generates one equation per leaf of the splitting tree, plus an elimination
  principle `funelim` **[checked: E1]**. Agda needs no equation lemmas, because clauses are
  reduction rules, but its `with` and pattern lambdas are generative, as Stitchwort's are
  **[checked: A1, A2]**.
- **Why Stitchwort needs less than Lean**: in Stitchwort every leaf of a definition's case
  tree holds by computation, since the checker unfolds a definition as soon as its case tree
  can take a step (`docs/core.md:183`). Lean's lemmas mainly serve definitions that don't
  compute in its kernel (well-founded recursion) and `rw`/`simp`, which work by rewriting,
  not by computing. Here, a per-leaf lemma is always provable by `rfl` and is a one-line
  theorem anyone can write; the hard part is only naming the inner `match` in it.
- **Recommendation** ([§8](#8-recommendation-and-build-plan)): stage 1, rewrite day 7's
  step without the workaround and document the pattern; stage 2, give local definitions'
  parameters a predictable order (the order the variables are written in), and make three
  messages say what to do. Don't generate equation lemmas, don't add an `unfold` step or a
  named-`match` syntax, and don't make matchers Lean-style, for now (D231 to D233).

## 1. Stitchwort in brief

Stitchwort is a strict, pure functional language with dependent types, implemented in Rust.
Functions are total by default (structural recursion, checked by size change); code that might
not terminate says so in its type (the `Partial` ability). Proofs are ordinary terms: there is
no tactic language (`DESIGN.md:390`, "No tactics") **[checked]**. A built-in equality `a = b`,
with `rfl` and the eliminator `J`, and an impredicative `Prop` whose proofs are erased at run
time. Exported, proven code is extracted to JavaScript, and the compiler also runs in the
browser as WebAssembly (the playground).

**Architecture.** An *elaborator* (`crates/elab`) turns surface syntax into core terms,
filling in implicit arguments, `if`, `match`, `rewrite` and so on. A small trusted *kernel*
(`crates/core`) re-checks every core term on its own, so anything the elaborator invents is
checked again. A design that needs no kernel change keeps the trusted part unchanged.

**Content hashes.** Every checked declaration has a hash of its type and body (with
references hashed as the referenced declaration's hash, and names left out); test results are
cached by hash (`docs/core.md:342-356`, `crates/core/src/hash.rs:1-33`) **[checked]**.

**Surface syntax used here** (`docs/syntax.md:104-189`) **[checked]**:

```
def length: List a -> Nat              -- arms match the arguments after the colon
  | Nil       => 0
  | Cons x xs => Succ (length xs)

theorem t (x: Nat) (h: x = 1): P x := …  -- `theorem` is a definition whose type is a Prop

x => e                                    -- a lambda
match e: cond with | True => … | False => …   -- case split, binding e: cond = True / False
rewrite p in t                            -- J with the motive found by searching the goal
(t: T)                                    -- a type ascription
_                                         -- a hole for the elaborator to fill
```

`a || b` on `Bool`s is `if a then True else b`, and `a && b` is `if a then b else False`
(`docs/syntax.md:457`); `if c then a else b` is `Bool.ifThenElse c (_ => a) (_ => b)`
(`crates/elab/src/check.rs:1487`, `docs/core.md:237`) **[checked]**.

## 2. How definitions are elaborated and unfolded today

### 2.1 Clauses become a case tree

A definition's arms are compiled by the usual matrix method into a **case tree**: split on the
first constructor pattern of the first remaining arm, and so on; the first arm whose patterns
are all variables wins (`docs/core.md:240`, `crates/elab/src/lib.rs:2121-2199`) **[checked]**.
A `Case` term may only appear at the top of a definition's body, after its parameters
(`crates/core/src/term.rs:115-122`) **[checked]**. So a source arm doesn't always correspond to
one leaf: with overlapping arms, a later arm holds only where the tree reaches it. For

```
def f: Nat -> Nat -> Nat
  | Zero,   n      => 0
  | m,      Zero   => 1
  | Succ m, Succ n => 2
```

`f (Succ m) Zero = 1` is `rfl`, but `f m Zero = 1` is `E-REFL` ("`Probe.f m 0` and `1`
aren't equal") **[run: overlap.sw]**. (It is false for `m = 0`.) Agda has the same
distinction ("clauses that don't hold definitionally", [A3]).

### 2.2 A `match` inside an arm becomes a generated function

A `match` is compiled *into the enclosing case tree* only when it is the whole right-hand side
of an arm, matches variables of the arm, and has no equation name. Any other `match` is
**lifted**: elaborated where it is, then turned into a generated top-level definition
`owner.%matchN` that takes the variables it uses ("captures") and the scrutinees as
parameters, called where the `match` was (`docs/syntax.md:529`,
`crates/elab/src/matching.rs:1-19`, `docs/proposals/syntax-conveniences.md` §4.2 to §4.4)
**[checked]**. The `%` makes the name unspellable on purpose, and the numbering is "display
and identity metadata, never something source can refer to" (`syntax-conveniences.md` §2.4;
`crates/elab/src/lift.rs:337-364`) **[checked]**. In messages a helper's name is replaced by
"this `match`" or `(match …)` (`lift.rs:1045-1049`) **[checked]**.

Day 7's `reach` (`Part1.sw:61-70`):

```
def reach: List Text -> Nat -> Nat -> Nat -> Bool
  | ls,             c, Zero,   d => c == d
  | Nil,            c, Succ k, d => False
  | Cons line rest, c, Succ k, d =>
    if charAt line c == '^' then
      (match c with
         | Zero   => False
         | Succ b => reach rest b k d)
        || reach rest (c + 1) k d
    else reach rest c k d
```

The inner `match` is an operand of `||`, so it is lifted. The result is, in effect
**[run: the messages in §3 print it as `(match …) c d k rest`]**:

```
def reach.%match1: Nat -> Nat -> Nat -> List Text -> Bool     -- c, d, k, rest
  | Zero,   d, k, rest => False
  | Succ b, d, k, rest => reach rest b k d

-- reach's third arm:  if charAt line c == '^' then reach.%match1 c d k rest || … else …
```

The helper's parameters are its captures "ordered by their types' dependencies, keeping
context order where the dependencies allow" (`lift.rs:849-850`) **[checked]**. The context at
the arm is the definition's own parameters first, then the pattern variables as the case
split binds them (`lib.rs:2195-2196`, "column `j` is replaced by the constructor's fields,
which are bound at levels `depth..depth + k`") **[checked]**, which is why `d` (a parameter)
comes before `k` and `rest` (fields) **[inferred; matches the run]**.

A **local definition** is the named version of the same machinery: `def left` inside an arm is
lifted to `reach.left`, which can be referred to from outside by that name
(`docs/syntax.md:164-189`) **[checked]**.

### 2.3 Unfolding: definitions compute when their case tree can take a step

The kernel decides equality by evaluating both sides (normalisation by evaluation). A
definition applied to all its arguments "unfolds only if its case tree can take a step,
meaning every case it reaches is on a constructor … Otherwise it stays folded"
(`docs/core.md:183`; `crates/core/src/value.rs:5-7`, `unfold` at `value.rs:1031-1063`,
`stuck_tree` at `value.rs:1022-1027`) **[checked]**. Folded definitions are equal only when
they are the same definition applied to equal arguments (`docs/core.md:186`) **[checked]**.
Instances (dictionaries) are an exception: folded by name until something takes them apart
(`docs/core.md:184`) **[checked]**.

Two consequences matter here:

1. **Every leaf of a case tree holds by computation.** `reach (Cons line rest) c (Succ k) d`
   computes, whatever `c` and `d` are, to `Bool.ifThenElse (charAt line c == '^') …`, since the
   tree splits only on the third and first arguments **[run: the messages in §3 show it]**. So
   any per-leaf equation is provable by `rfl`, and a goal mentioning such a call already
   contains its unfolding.
2. **Generated functions are generative.** `reach.%match1 c d k rest` and a textually
   identical `match` elsewhere (another generated function) are different definitions. While
   `c` is a variable neither unfolds, so they aren't equal. This is the documented behaviour
   (`syntax-conveniences.md` §4.4, "Equality of two `match`es"), and Agda's pattern lambdas
   behave the same ("pattern lambdas are *generative*", [A1]) **[checked]**.

### 2.4 Case splits in proofs: `match e:` and `rewrite`

- **`match e: cond with`** generalises the scrutinee: occurrences of it in the goal, and in
  the types of variables in scope, are replaced by the branch's pattern, and `e: cond =
  pattern` is bound (`docs/syntax.md:531-541`) **[checked]**. The occurrence test is
  syntactic, "no definitions are unfolded" (`matching.rs:533-537`), but it compares the
  *computed* forms: the scrutinee is evaluated and read back (`matching.rs:254`), and so is
  each variable's type (`matching.rs:348`) **[checked]**. So a hypothesis `h: reach (Cons line
  rest) c (Succ k) d = True` does contain the condition, after `reach` has unfolded, and is
  refined. Only variables whose value is themselves are copied (`matching.rs:350`,
  `unrefined = is_var(…)`), so a `let` isn't **[checked]**: that is SW-193.
- **`rewrite p in t`** (built, `docs/proposals/calc-rewrite.md`, "As built") searches the goal
  "as it computes" for `p`'s left side and builds the `J`. It needs a known goal
  (`E-REWRITE-NO-GOAL` otherwise), and it doesn't rewrite hypotheses ("Not included: rewriting
  a hypothesis … write `rewrite p in h` where `h`'s new type is expected") **[checked:
  calc-rewrite.md §6.4, §6.5, As built]**. Because goals are searched computed, a rule whose
  left side is a call that has already unfolded in the goal finds nothing (As built,
  difference 2) **[checked]**: so a left-to-right equation lemma about `reach` would rarely be
  useful to `rewrite` **[inferred]**.

## 3. Day 7, reproduced

All runs below are in a copy of `aoc/` with theorems appended to `Part1.sw` (or the step
edited), checked with `stitchwort check Aoc.Day07.Proofs`. Messages are abridged where marked.

### 3.1 The workaround as committed

```
def leftReach (rest: List Text) (k: Nat) (d: Nat): Nat -> Bool
  | Zero   => False
  | Succ b => reach rest b k d

theorem reachStep (line: Text) (rest: List Text) (k: Nat) (d: Nat): (c: Nat) ->
    reach (Cons line rest) c (Succ k) d = (if charAt line c == '^' then leftReach rest k d c || reach rest (c + 1) k d else reach rest c k d)
  | Zero   => rfl
  | Succ b => rfl
```

and in `fallKeeps` (`Part1.sw:287-291`, `315`):

```
let hr := Eq.trans (Eq.sym (reachStep line rest k d c)) (Bool.andRight (List.getOr False c beams) (reach (Cons line rest) c (Succ k) d) hc)
match e: charAt line c == '^' with
  | True  =>
    orCases (beamReach w fallen rest k d = True) (leftReach rest k d c) (reach rest (c + 1) k d)
      (Eq.trans (Eq.sym (rewrite e in rfl: (if … then leftReach rest k d c || … else …) = (leftReach rest k d c || …))) hr)
      …
  | False => … (Eq.trans (Eq.sym (rewrite e in rfl: (if … then … else reach rest c k d) = reach rest c k d)) hr) …
```

`reachStep` has to split on `c` because, with `c` a variable, `leftReach rest k d c` and
`reach.%match1 c d k rest` are two folded, different definitions (§2.3). Without the split:

```
theorem r5 …: reach (Cons line rest) c (Succ k) d = (if charAt line c == '^' then leftReach rest k d c || … else …) := rfl
```

```
[E-REFL] Error: `rfl` can't prove this
  Note 1: computing both sides gives
    `if Decidable.toBool (Char.decEqFrom (List.getOr … c …) '^' (Nat.decEq … 94)) then if (match …) c d k rest then True else … else …`
    and `if Decidable.toBool (…) then if Aoc.Day07.Proofs.leftReach rest k d c then True else … else …`
```

**[run: r5]**

### 3.2 What works without the workaround

Refining a hypothesis that is a parameter (`r1`) and rewriting the condition in a goal (`r2`)
both check **[run]**:

```
theorem r1 (line: Text) (rest: List Text) (c: Nat) (k: Nat) (d: Nat) (h: reach (Cons line rest) c (Succ k) d = True):
    Bool.not (charAt line c == '^') = True -> reach rest c k d = True :=
  match e: charAt line c == '^' with
    | True  => n => Void.exfalso (Bool.falseNotTrue n)
    | False => n => h                               -- h's type is refined: it computes to reach rest c k d = True

theorem r2 (…) (s: (charAt line c == '^') = False) (h: reach (Cons line rest) c (Succ k) d = True): reach rest c k d = True :=
  Eq.trans (Eq.sym (rewrite s in rfl: reach (Cons line rest) c (Succ k) d = reach rest c k d)) h
```

(A control, `r1x`, the same with `reach rest (c + 1) k d` as the goal of the `False` branch,
is rejected, so `r1` isn't passing vacuously **[run]**.) Splitting `c` first makes the helper
compute, so the `Succ` case can be stated without it **[run: r4]**:

```
theorem r4 (…) (b: Nat) (…) (s: (charAt line (Succ b) == '^') = True):
    reach (Cons line rest) (Succ b) (Succ k) d = (reach rest b k d || reach rest (Succ b + 1) k d) :=
  rewrite s
```

The first direction of `fallKeeps` already does this (`Part1.sw:268-277`, `match c with |
Succ b => … rewrite hF, Nat.addOne b, hr in Bool.orTrue _`) **[checked]**.

### 3.3 What fails, and why

**A `let`-bound hypothesis isn't refined** (SW-193). The same as `r1`, with the hypothesis
taken from a `let` **[run: r8]**:

```
  let hr := Bool.andRight True (reach (Cons line rest) c (Succ k) d) h
  match e: charAt line c == '^' with
    | True  => n => Void.exfalso (Bool.falseNotTrue n)
    | False => n => hr
```

```
[E-TYPE-MISMATCH] Error: type mismatch
 463 │     | False => n => hr
     │                    ╰── expected `Aoc.Day07.Proofs.reach rest c k d = True`, but this has type
         `(if Decidable.toBool (Char.decEqFrom (List.getOr … c …) '^' (Nat.decEq … 94)) then if (match …) c d k rest then True else
           Aoc.Day07.Proofs.reach rest (c + 1) k d else Aoc.Day07.Proofs.reach rest c k d) = True`
```

This is exactly the day 7 step with the workaround removed and nothing else changed (`V0`:
`let hr := Bool.andRight (List.getOr False c beams) (reach (Cons line rest) c (Succ k) d) hc`,
then `orCases … _ (reach rest (c + 1) k d) hr` and `hr` in the `False` branch): the same
error at the `False` branch's `hr` **[run: V0]**. I take this to be the failure behind
"matching on `charAt line c == '^'` didn't refine a hypothesis about `reach`"
(`docs/aoc-2025.md`, day 7 pain point 2) **[inferred: the committed step uses a `let`, and
the same step with a lambda-bound hypothesis works, §3.4]**.

**Arguments written out in a branch aren't refined.** Inlining the `let` but keeping the
arguments (`Bool.andRight (List.getOr False c beams) (reach (Cons line rest) c (Succ k) d)
hc`, `V1`) fails in the `False` branch the other way round **[run: V1]**:

```
[E-TYPE-MISMATCH] Error: type mismatch
     ╰── expected `(if List.getOr False c beams then if Decidable.toBool (Char.decEqFrom … … …) then if (match …) c d k rest then True
           else … else Aoc.Day07.Proofs.reach rest c k d else False) = True`,
         but this has type `(if List.getOr False c beams then Aoc.Day07.Proofs.reach rest c k d else False) = True`
```

`hc` (a lambda's variable) *was* refined; the explicit argument `reach (Cons line rest) c
(Succ k) d`, written inside the branch, is elaborated afresh and still contains the
unrefined condition. Generalising replaces occurrences in the goal and in variables' types,
never in what is written later (`docs/syntax.md:536-541`, "Nothing else changes")
**[checked]**. Lean behaves the same way, as far as I know **[unverified]**.

**A statement can't mention the inner `match`.** Writing the same `match` in a lemma makes
a *second* helper **[run: r3]**:

```
theorem r3 (…) (s: (charAt line c == '^') = True):
    reach (Cons line rest) c (Succ k) d = ((match c with | Zero => False | Succ b => reach rest b k d) || reach rest (c + 1) k d) :=
  rewrite s
```

```
[E-REFL] Error: `rfl` can't prove this
 425 │ … = ((match c with | Zero => False | Succ b => reach rest b k d) || …)   ← "this `match`"
  66 │ (match c with …)                                                              ← "this `match`"
 426 │   rewrite s
     │           ╰── `if (match …) c d k rest then True else …` and `if (match …) rest c k d then True else …` aren't equal
```

The two `(match …)` are `reach.%match1` and `r3.%match1` (note the different capture orders,
`c d k rest` and `rest c k d`). And `_` can't help in a *statement*: a hole in a theorem's
type must be solved by the type itself. Using `leftReach` against a hypothesis fails the same
way as `r5` **[run: r6]**.

### 3.4 The proof without the workaround

`leftReach` and `reachStep` deleted, and the second direction of `fallKeeps` changed in three
lines (the full diff):

```
-  let hr := Eq.trans (Eq.sym (reachStep line rest k d c)) (Bool.andRight (List.getOr False c beams) (reach (Cons line rest) c (Succ k) d) hc)
   match e: charAt line c == '^' with
     | True  =>
-      orCases (beamReach w fallen rest k d = True) (leftReach rest k d c) (reach rest (c + 1) k d)
-        (Eq.trans (Eq.sym (rewrite e in rfl: (if charAt line c == '^' then leftReach rest k d c || reach rest (c + 1) k d else reach rest c k d) = (leftReach rest k d c || reach rest (c + 1) k d))) hr)
+      orCases (beamReach w fallen rest k d = True) _ (reach rest (c + 1) k d) (Bool.andRight _ _ hc)
         (hl => match c with
                  | Zero   => Void.exfalso (Bool.falseNotTrue hl)     -- hl: reach.%match1 0 … = True computes to False = True
                  | Succ b => … hl …)                                 -- … and to reach rest b k d = True
         …
     | False =>
         … (Bool.andRight (List.getOr False c fallen) (reach rest c k d) (… ) …)
-          (Eq.trans (Eq.sym (rewrite e in rfl: (if … then leftReach rest k d c || … else reach rest c k d) = reach rest c k d)) hr))))
+          (Bool.andRight _ _ hc))))
```

`stitchwort check` of the whole `aoc` project passes, and `stitchwort test --no-cache
Aoc.Day07.Proofs` runs 17 tests, 17 passed **[run: V2]**. The first `_` is solved by
unification to `reach.%match1 c d k rest`, which the proof never writes. The file is 14 lines
shorter and the copy that could drift is gone. Checking `Aoc.Day07.Proofs` took 0.58 to
0.61 s against 0.64 to 0.66 s with the workaround (three runs each, release build, this
machine) **[run]**.

### 3.5 Naming the inner `match` with a local definition

A local `def` gives the branch a name source can use, today **[run: localdef.sw]**:

```
def reach: List Text -> Nat -> Nat -> Nat -> Bool
  | ls,             c, Zero,   d => c == d
  | Nil,            c, Succ k, d => False
  | Cons line rest, c, Succ k, d =>
    def left: Nat -> Bool
      | Zero   => False
      | Succ b => reach rest b k d
    if charAt line c == '^' then left c || reach rest (c + 1) k d else reach rest c k d

theorem leftZero (rest: List Text) (k: Nat) (d: Nat): reach.left d k rest Zero = False := rfl

theorem reachSplit (line: Text) (rest: List Text) (c: Nat) (k: Nat) (d: Nat) (s: (charAt line c == '^') = True):
    reach (Cons line rest) c (Succ k) d = (reach.left d k rest c || reach rest (c + 1) k d) :=
  rewrite s
```

Both check. But I first wrote `reach.left rest k d c`, the order the variables appear in
the arm, and got `E-TYPE-MISMATCH` ("expected `Nat`, but this has type `List Text`") at
`rest` **[run]**. The order is `d k rest`, for the reason in §2.2: parameters before pattern
fields. Nothing in the docs says so; `docs/syntax.md:179` only says the captures are "leading
parameters".

## 4. How other languages do it

### 4.1 Summary

| | per-clause equations | whole-definition unfolding | nested `match` | case split on a call |
|---|---|---|---|---|
| **Lean 4** | `f.eq_1`, `f.eq_2`, … one per case-tree leaf, generated on demand | `f.eq_def`, `f.eq_unfold`; `unfold f`, `rw [f]`, `simp [f]` | closed matcher `f.match_1`, branches passed as functions; `split` | `split`, `fun_cases`, `fun_induction` |
| **Rocq, Equations** | one per leaf of the splitting tree, in a rewrite database `f`; `simp f` | `f_unfold` for well-founded definitions | each `with` node is an auxiliary definition with its own equations | `funelim` via the generated `f_elim` |
| **Agda** | clauses are reduction rules (case tree) | none needed | `with` and pattern lambdas are generated functions, generative | `with … in eq`, `rewrite` |
| **Idris 2** | clauses are reduction rules | none | `case` lifted to a helper; `with` generalises | `with` |
| **F\*** | definitions are axioms for the SMT solver, with fuel | `[@@"opaque_to_smt"]`, `reveal_opaque` | encoded with the body | the solver |
| **Dafny** | function bodies are axioms, unrolled with fuel | `opaque` functions and `reveal f()` | part of the body | the solver |

### 4.2 Lean 4

- **Equation lemmas are generated on demand.** "We generate equations theorems on demand,
  and they are generated by more than one module"; `getUnfoldEqnFor?` "Returns an "unfold"
  theorem (`f.eq_def`)", by default not for non-recursive definitions; the suffixes are
  `eq_1` and `eq_def`, reserved names [L1] **[checked]**. `f.eq_unfold` (`f = fun … => …`,
  usable under binders) was added in 2024 [L2] **[checked]**.
- **One lemma per leaf, including the inner `match`.** For a Lean transcription of `reach`
  (in `Day7.lean`), Lean generated **four** equations: `eq_3` is the `c = 0` case and `eq_4`
  the `c = b + 1` case of the third clause, with the inner `match` already split
  **[run]**:

  ```
  reach.eq_3 : reach (line :: rest) 0 k.succ x = if (charAt line 0 == '^') = true then false || reach rest (0 + 1) k x else reach rest 0 k x
  reach.eq_4 : reach (line :: rest) b.succ k.succ x = if (charAt line b.succ == '^') = true then reach rest b k x || reach rest (b.succ + 1) k x else reach rest b.succ k x
  reach.eq_def : reach x x_1 x_2 x_3 = match x, x_1, x_2, x_3 with … | line :: rest, c, k.succ, d => if … then (match c with | 0 => false | b.succ => reach rest b k d) || … else …
  ```

  These are Stitchwort's `r4` (and its `Zero` twin): one-liners by `rfl` here.
- **`rw [f]` uses the equation lemmas** ("If `e` is a defined constant, then the equational
  theorems associated with `e` are used", [L3] `rewrite`) **[checked]**. With `c` a variable
  none applies: `rw [reach] at h` failed with "Failed to rewrite using equation theorems for
  `reach`. Hint: Try rewriting with `reach.eq_def`" **[run]**. `unfold f` uses `f.eq_def`,
  one level, where `simp only [f]` unfolds repeatedly [L3] **[checked]**.
- **Nested `match` is a closed matcher.** `#print reach.match_1` gives
  `(motive : Nat → Sort u_1) → (c : Nat) → (Unit → motive 0) → ((b : Nat) → motive b.succ) →
  motive c := fun motive c h_1 h_2 => Nat.casesOn c (h_1 ()) fun n => h_2 n` **[run]**: the
  branches are *arguments*, not part of the matcher. Matchers are cached by
  `mkMatcherAuxDefinition` ("uses the cache `matcherExt`", returning whether "a new matcher
  function was added") [L4] **[checked]**. So the same `match` written in a lemma lines up
  with the definition's: my `statedRfl`, with `match (generalizing := false) c with …` in the
  statement, closes after rewriting the condition **[run]**. Without `(generalizing := false)`
  Lean also generalised the hypothesis `s` (which mentions `c`) into the statement's `match`,
  making a different shape that `simp only [reach, s]` could not close **[run]**: the same
  trap in another form.
- **`split`** "is useful for breaking nested if-then-else and match expressions into separate
  cases … `split at h` will split the hypothesis `h`" [L3] **[checked]**. Day 7's step in
  Lean: `rw [reach.eq_def] at h; simp only at h; split at h` (the `if`), then `split at h`
  (the `match c`) **[run: split_demo, axioms: propext only]**.
- **`fun_cases` / `fun_induction`** do a case analysis (or induction) following the
  function's own splits ("`fun_cases f x … y …` is equivalent to `cases y, … using
  f.fun_cases_unfolding x …`", [L3]) **[checked]**.

What a day-7 author gets: the leaf equations for free, and a `match` in a statement that
agrees with the definition's. What they pay: a tactic language, an equation generator, and
definitional unfolding of matchers in the kernel.

### 4.3 Rocq: the Equations plugin

- "Each compiled clause of the program or one of its subprograms defined implicitely by
  `with` or explicitly by `where` nodes gives rise to an equation. Note that the clauses
  correspond to the program's splitting tree … so a single source clause catching multiple
  cases can correspond to multiple equations." They go into a rewrite database `f`, used by
  `simp f` (`autorewrite with f`), and "are named after the position they appear in in the
  program" [E1 §1.1.2] **[checked]**.
- "Each with node generates an auxiliary definition from the clauses in the curly brackets
  … The equation for the with node will simply be an indirection to the auxiliary
  definition" [E1 §2.3.3] **[checked]**: nested matches are named subprograms with their own
  equations.
- An elimination principle `f_elim` from the function's graph, used by `funelim t`
  [E1 §1.1.2, §1.5] **[checked]**. Definitions are opaque by default; `simp f` is how one
  unfolds (`Equations Transparent`, [E1 §1.1.5]) **[checked]**.

What a day-7 author gets: per-leaf equations including the `with` subprogram, and `funelim`.

### 4.4 Agda

- Function definitions are case trees, and a clause that the tree doesn't reach as written
  doesn't hold definitionally; `--exact-split` warns about such clauses [A3] **[checked]**.
  So there are no generated equation lemmas: clauses compute, as in Stitchwort.
- `with` is translated to an auxiliary function, mutually recursive with the outer one; a
  stuck `with` prints as `filter p (x ∷ xs) | p x`, a form "used for printing, but … not
  accepted as valid Agda code" [A2] **[checked]**. A proof matches on the same expression with
  `with … in eq` to make the goal reduce [A2] **[checked]**.
- Pattern lambdas are generative: "two pattern lambdas with the same body are not considered
  equal by Agda" [A1] **[checked]**.

What a day-7 author gets: what Stitchwort has today, with the same generativity. The
standard advice is to define the helper as a named function (`where`) when one needs to talk
about it [A2, "Helper functions"] **[checked]**.

### 4.5 Idris 2

A `case` "is extracted to a helper function" and "The core language can only have case trees
at the top of a top level function"; `with` generalises the scrutinee, `case` doesn't
[I1] **[checked]**. No equation lemmas: clauses compute. Same position as Agda.

### 4.6 F\* and Dafny

Both hand definitions to an SMT solver as axioms. F\* adds "a second "fuel-instrumented"
function symbol" so recursive definitions unfold a bounded number of times;
`[@@"opaque_to_smt"]` hides a definition and `reveal_opaque` brings it back locally [F1]
**[checked]**. Dafny's `{:opaque}` functions "behave like uninterpreted functions" until
`reveal foo()`, and `{:fuel}` sets the unrolling [D1] **[checked]**. Neither has an equation
lemma the user names; unfolding is the solver's business. Their lesson for Stitchwort is
about *control*: an explicit "hide this definition" / "reveal it here" pair, which
Stitchwort doesn't need while its unfolding policy keeps proofs fast (§7).

### 4.7 What to take

1. Equation lemmas, where they exist, are **per leaf of the case tree**, not per source
   clause (Lean's `eq_3`/`eq_4`, Equations' "splitting tree"). Any Stitchwort version should
   follow that, which also settles overlapping arms (§2.1).
2. They are **generated on demand** (Lean), which avoids paying for definitions nobody
   proves anything about.
3. The thing that makes Lean's nested `match` usable in statements is not the equation
   lemmas but the **closed, shared matcher** (§6, option f).
4. Languages whose clauses compute (Agda, Idris 2) don't generate equation lemmas; they
   name helpers by hand. Stitchwort is in this family.

## 5. What is actually missing

From §3, sorted by how much each would have helped day 7:

| | Gap | Evidence | Status |
|---|---|---|---|
| G1 | `match e:` doesn't refine a `let`-bound hypothesis | `r8`, `V0` | SW-193, in progress |
| G2 | Arguments written in full in a branch aren't refined; nothing hints at `_` | `V1` | new (D230) |
| G3 | A statement can't mention a lifted `match` | `r3`, `r5`, `r6` | this note |
| G4 | A local `def` can name it, but its parameter order is unguessable and undocumented | §3.5 | new (D228) |
| G5 | Messages show the helper as `(match …) c d k rest`: you can see it exists but not how to name it | §3 messages | new (D229) |
| G6 | An arm that overlaps an earlier one doesn't hold as written (`f m Zero = 1`) | `overlap.sw` | by design, as in Agda; equation lemmas would state the leaf form |

Day 7's proof needed G1 and G2 fixed, not G3. G3 matters when a lemma is *about* the inner
branch, for example a lemma "`reach`'s left branch is `False` past the left edge". Today that
lemma has to be stated after splitting the scrutinee (`r4`), or the branch made a local `def`
(§3.5).

## 6. Options

Each option is shown on day 7. They combine.

### (a) Generated per-leaf equation lemmas, `f.eq_N`

For each leaf of a definition's case tree, a theorem whose left side is the definition applied
to the leaf's patterns and whose right side is the leaf's body, proved by `rfl`. Named
`f.eq_1`, `f.eq_2`, … in tree order (Lean's naming). For `reach`:

```
reach.eq_1 (ls: List Text) (c: Nat) (d: Nat): reach ls c Zero d = (c == d)
reach.eq_2 (c: Nat) (k: Nat) (d: Nat): reach Nil c (Succ k) d = False
reach.eq_3 (line: Text) (rest: List Text) (c: Nat) (k: Nat) (d: Nat):
    reach (Cons line rest) c (Succ k) d = (if charAt line c == '^' then reach.%match1 c d k rest || reach rest (c + 1) k d else reach rest c k d)
```

Use in day 7: `Eq.trans (Eq.sym (reach.eq_3 line rest c k d)) h` restates a hypothesis
(what `reachStep` did), so the `let` problem disappears.

- **For:** the user never writes the inner `match`; the lemma's statement does. Overlapping
  arms get a correct statement (G6).
- **Against:** in Stitchwort each such lemma is `rfl` (§2.3), so it adds no power, only a
  name. A hypothesis can already be restated by ascription. `rewrite reach.eq_3` would
  usually find nothing, since goals are searched computed (§2.4). The statement contains
  `reach.%match1`, which the user still can't write, so a lemma *built on* `eq_3` can't
  mention it either (G3 stays). Lean's version splits the inner `match` too (`eq_3`/`eq_4`);
  Stitchwort's generator would have to look into the helper to do that.

### (b) One unfold lemma per definition, `f.eq_def`

`f x₁ … xₙ = ‹the body›`. In Stitchwort the body is a case tree, which source can only write
as a `match`, which is generative: the lemma's right side would be a new helper, equal to
nothing else. **Not viable** without (f).

### (c) A surface `unfold f in t` / `rewrite f` step

A term that rewrites the goal (or, new, a hypothesis) with `f`'s leaf equations, showing the
result with inner matches printed as named helpers. Day 7: `unfold reach in hr`.

- **For:** familiar to Lean users.
- **Against:** the checker already unfolds `reach (Cons line rest) c (Succ k) d` by itself;
  the step would be a new kind of term (a hypothesis rewrite, which `rewrite` deliberately
  left out, calc-rewrite.md §6.5) to do what an ascription does. It is a tactic in all but
  name (`DESIGN.md:390`). Same naming gap as (a).

### (d) Name the inner `match` in source

Two forms:

- **(d1) A local `def`**, which exists (§3.5). Day 7 writes `def left` in the arm and states
  lemmas about `reach.left`. Costs: the parameter order (G4), and a local `theorem` about it
  inside `reach` is `E-MUTUAL-SIGNATURE` because `left` calls its owner
  (`docs/syntax.md:181`), so the lemma has to be top-level. Fixing G4 means ordering a local
  definition's captures by where the variables are written (header parameters in order, then
  the arm's pattern variables left to right), keeping type dependencies.
- **(d2) A named `match`**, e.g. `match[left] c with …` or `left := match c with …`, giving
  the helper the key `reach.left`. Same machinery as (d1) with new syntax for something
  (d1) already does in three more characters per line.

### (e) Better case analysis on an exposed `match`

`match e:` already does Lean's `split` for an `if` condition (§2.4) and `match c with`
already splits the helper (§3.4). What's missing is around it: G1 (SW-193) and G2 (a hint to
use `_`). A `split`-like keyword would duplicate `match e:`.

### (f) Closed, shared matchers (Lean's design)

Lift a `match` to a generic function that takes its branches as arguments (`Nat.%match<hash>
(c) (_ => False) (b => reach rest b k d)`), shared by every `match` of the same shape (same
scrutinee types and patterns). Two textually identical matches are then the same matcher
applied to equal branch functions, so `r3` would check.

- **For:** the only option that closes G3 without a name: statements can repeat the
  definition's `match`.
- **Against:** the size-change termination check treats lambda-bound variables as of unknown
  size (`docs/core.md:152`), so `b` in `b => reach rest b k d` would no longer be smaller
  than `c`, and every recursive call inside a lifted `match` would be refused, unless the
  trusted termination checker learns about matchers (Lean's structural recursion does
  exactly that, with its own special handling **[unverified in detail]**). Branch closures
  cost allocation in the evaluator and in JS unless inlined. Generalisation must not grab
  extra variables or the shapes differ (Lean's own `s` trap, §4.2). And matchers would be
  shared across unrelated definitions, so hashing and error messages would need care.

## 7. Costs and risks

For the recommended pieces (D226 to D230) and, for completeness, for (a) if it is built
later (D231).

- **When generated.** Recommended pieces: nothing is generated. (a): on demand, when a name
  `f.eq_N` is looked up and not found, built from `f`'s stored case tree, admitted as a
  theorem by the kernel (one conversion check per lemma: unfold once and compare)
  **[inferred]**. Eager generation would add a kernel check per leaf of every definition at
  every load, including the prelude (365 `def`s and 639 `theorem`s across
  `crates/elab/src/std/**/*.sw` **[run: grep]**) and the playground's startup in WebAssembly.
  Lean generates on demand for the same reason [L1].
- **Check time and memory.** D226 makes day 7 slightly faster (§3.4). D228 changes only the
  order of parameters. D229/D230 run only when an error is reported. (a) on demand: a lemma
  per use, cached for the session **[inferred]**.
- **Hashing.** D228 changes the hashes of local definitions whose captures get reordered,
  and of everything using them. Hash stability isn't a goal while there are no users, and the
  hash-change test can use it as a migration oracle (every changed hash should be a local
  definition with reordered captures or a user of one) **[inferred]**. (a): a generated lemma
  is an ordinary theorem; its hash is its type and its `rfl` proof, and the type mentions
  `f` by hash, so it is derived from `f`'s hash and the same whichever file triggered it. Not
  generating a lemma changes no hash **[inferred from `hash.rs:1-33`]**.
- **Mutual recursion.** Local definitions in a cycle with their owner are already admitted
  with it as one group (`lift.rs:20-28`) **[checked]**; D228 doesn't change grouping. (a): a
  member's lemmas can be generated once the whole group is final (`docs/core.md:157`, "Install,
  all or nothing") **[inferred]**.
- **`Partial`.** A recursive local definition can't be `{Partial}` (`docs/syntax.md:182`), and
  a lifted `match` in a partial function is still a leftover (SW-20) **[checked]**. (a) would
  skip partial definitions: they go through `Effect.pfix`, which has no computation rules in
  the kernel (`docs/core.md:283-292`), so their leaves don't hold by `rfl` **[inferred]**.
- **Records.** Projections are one-branch cases (`docs/core.md:103`); nothing changes. Record
  patterns in local definitions are captured like other variables **[inferred]**.
- **Indexed families.** Capture order must still respect type dependencies (a variable whose
  type mentions an index variable after it), which D228 keeps ("dependencies permitting").
  (a): a leaf's statement lives in the leaf's refined context (indices unified and
  substituted), and impossible branches give no lemma **[inferred from
  `docs/core.md:226`]**.
- **Interfaces.** Instances are folded by name and unfold only when taken apart
  (`docs/core.md:184`); a `match` inside a method body is lifted like any other. (a) would
  skip dictionaries (their leaves are records of methods) **[inferred]**.
- **Playground (WASM) and JS backend.** None of the recommended pieces adds code paths to
  either; theorems are erased when running and extracting (`crates/core/src/erase.rs:11-13`)
  **[checked]**. D228's reordering changes the order of a local function's parameters in
  extracted JS, which is internal (helpers aren't exported) **[inferred]**.
- **Risk: users meet the trap anyway.** The pattern in §3.4 (no `let`, `_` for the hidden
  part) is not discoverable. That is what D227's documentation and D229/D230's messages are
  for; after SW-193 the `let` form works too.

## 8. Recommendation and build plan

Recommended: D226 to D230 as below; D231 to D233 not now.

**Stage 1: day 7 and documentation (small; mechanical edits).**

- Replace `leftReach`/`reachStep` in `aoc/src/Aoc/Day07/Proofs/Part1.sw` with the §3.4 shape.
- `docs/aoc-2025.md` day 7 pain point 2: correct it (the condition does refine a hypothesis
  that isn't a `let`; the workaround is gone), pointing here.
- `docs/syntax.md`, after "`match`": a short "Proving things about a definition with an inner
  `match`" paragraph: arms compute; match on the condition; leave the inner `match`'s part as
  `_`; split its scrutinee to make it compute; to *state* something about it, make it a local
  `def` and use `owner.name`.

Acceptance: `Part1.sw` has no `leftReach` or `reachStep`; `stitchwort check` of the `aoc`
project passes; `stitchwort test --no-cache Aoc.Day07.Proofs` passes 17 of 17.

**Stage 2: names and messages (small to medium; elaborator only).**

- D228: order a local definition's captures by where the variables are written (header
  parameters in order, then pattern variables left to right, then `let`s and earlier locals),
  moving one later only when a type dependency requires it; document it at
  `docs/syntax.md:179`. Lifted `match` helpers get the same order (nobody writes their
  names, but messages print their arguments).
- D229: when a message would print `(match …) c d k rest`, add a note: "`(match …)` is the
  `match` at Part1.sw:66, inside `reach`; to state a lemma about it, make it a local `def`
  and refer to it as `reach.name`".
- D230: when a type mismatch inside a branch of a generalised `match` involves a term that
  still contains the scrutinee, add a note: "this argument is written out, so it isn't
  refined by the `match`; write `_` to let it be inferred".
- When an application of a local definition has a wrong argument, show the definition's full
  signature in the message.

Acceptance:
- `examples/accept/`: the §3.5 `reach` with `def left`, and `theorem reachSplit` stated with
  `reach.left rest k d c` (the new order), checks.
- `examples/reject/` with snapshots: `r3` (a `match` repeated in a statement) shows the D229
  note; `V1` shows the D230 note; `reach.left d k rest c` (the old order) shows the
  signature.
- The hash-change test: every changed hash is a local definition with reordered captures, or
  depends on one.

**After SW-193 lands:** add `V0` (the day 7 step with `let hr := …` and `_`) as an accept
example.

**Not now:** generated equation lemmas (D231), an `unfold`/named-`match` syntax (D232),
Lean-style matchers (D233). Reopen D231 when a proof needs a leaf statement that is tedious to
write by hand (many leaves, or arms that overlap so the leaf form differs from the source),
or D233 if repeating a definition's `match` in statements becomes common.

## 9. Decisions

- **D226. Remove day 7's workaround without new features.** Rewrite `fallKeeps`'s step as in
  §3.4 and correct `docs/aoc-2025.md`. *Recommendation: yes* (stage 1).
- **D227. Document the proof pattern** for definitions with an inner `match` in
  `docs/syntax.md` (§8, stage 1). *Recommendation: yes.*
- **D228. Local definitions' captures in written order** (header parameters, then pattern
  variables left to right, dependencies permitting), for local `def`s and lifted `match`es,
  documented, accepting the hash changes. *Recommendation: yes* (stage 2).
- **D229. Say how to name a `match` when a message shows `(match …)`**, with its location
  and the local-`def` route. *Recommendation: yes.*
- **D230. Hint `_` for written-out arguments that a `match` didn't refine.**
  *Recommendation: yes*, if the check stays cheap (only when the error is already being
  reported).
- **D231. Generated per-leaf equation lemmas `f.eq_N`** (on demand, per leaf, Lean's names).
  *Recommendation: not now.* Each would be `rfl`, the inner `match` in it still unnameable,
  and `rewrite` searches computed goals; revisit on the trigger in §8.
- **D232. A surface `unfold` step, or a named-`match` syntax.** *Recommendation: no.* The
  checker unfolds case trees itself, and a local `def` names a `match`.
- **D233. Closed, shared matchers (Lean-style), so a `match` repeated in a statement agrees
  with the definition's.** *Recommendation: not now*; it needs the trusted termination
  checker to understand matchers. Record it as the route if D231's trigger fires for
  statements rather than proofs.

## Sources

- [L1] Lean 4 API docs, `Lean.Meta.Eqns` (`getEqnsFor?`, `getUnfoldEqnFor?`, "We generate
  equations theorems on demand", suffixes `eq_1`, `eq_def`):
  <https://lean-lang.org/doc/api/Lean/Meta/Eqns.html>
- [L2] Lean 4 issue #5110, "RFC: `f.eq_unfold` lemmas" (`eq_n`, `eq_def`, `eq_unfold`; closed
  by PR #5141): <https://github.com/leanprover/lean4/issues/5110>
- [L3] Lean Language Reference, Tactic Reference (`rewrite`: "If `e` is a defined constant,
  then the equational theorems associated with `e` are used"; `unfold` and `eq_def`; `split`;
  `fun_cases`; `simp [f]`):
  <https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/>
- [L4] Lean 4 API docs, `Lean.Meta.Match.Match` (`mkMatcherAuxDefinition` and the
  `matcherExt` cache): <https://lean-lang.org/doc/api/Lean/Meta/Match/Match.html>
- [L5] Lean Language Reference, "Recursive definitions" (the `half.match_1` walkthrough:
  "pattern matching has already been translated into the use of matcher functions"):
  <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- Lean runs: Lean 4.34.1 (`nix shell nixpkgs#lean4`), scratch files `Day7.lean` and
  `Day7b.lean`: `#check reach.eq_1 … eq_4`, `eq_def`, `#print reach.match_1`, `statedRfl`,
  `split_demo`.
- [E1] M. Sozeau, *Equations 1.3beta2 Reference Manual*, 21 June 2021 (§1.1.2 Generated
  definitions, §1.1.5 Global options, §1.4 `simp`, §1.5 Functional elimination, §2.3.3
  `with` clauses): <https://github.com/mattam82/Coq-Equations/raw/main/doc/equations.pdf>;
  introduction: <https://mattam82.github.io/Coq-Equations/assets/jsexamples/equations_intro.html>
- [A1] Agda documentation, "Lambda abstraction" ("pattern lambdas are *generative*"):
  <https://agda.readthedocs.io/en/latest/language/lambda-abstraction.html>
- [A2] Agda documentation, "With-abstraction" (translation to auxiliary functions, `with …
  in eq`, `rewrite`, printing of stuck `with`s, helper functions):
  <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [A3] Agda documentation, "Function definitions" (case trees, clauses that don't hold
  definitionally, `--exact-split`):
  <https://agda.readthedocs.io/en/latest/language/function-definitions.html>
- [I1] Idris 2 issue #3271 (`case` extracted to a helper; `with` generalises):
  <https://github.com/idris-lang/Idris2/issues/3271>; Idris 2 tutorial, "Views and the
  `with` rule": <https://idris2.readthedocs.io/en/latest/tutorial/views.html>
- [F1] *Proof-Oriented Programming in F\**, "Understanding how F\* uses Z3" (fuel,
  `opaque_to_smt`, `reveal_opaque`):
  <https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html>
- [D1] Dafny documentation, "Dafny compilation to Boogie" (`{:opaque}`, `reveal`, fuel):
  <https://dafny.org/dafny/Compilation/Boogie>; reference manual (Reveal statement, Opaque
  block): <https://dafny.org/dafny/DafnyRef/DafnyRef>
- Stitchwort (repository paths, for the owner; a reviewer doesn't need them):
  - `aoc/src/Aoc/Day07/Proofs/Part1.sw`, `docs/aoc-2025.md` (day 7)
  - `docs/core.md`, `docs/syntax.md`, `DESIGN.md`,
    `docs/proposals/syntax-conveniences.md` (§2, §4), `docs/proposals/calc-rewrite.md`
  - `crates/elab/src/{matching.rs, lift.rs, lib.rs, check.rs}`,
    `crates/core/src/{value.rs, term.rs, hash.rs, erase.rs}`
  - scratch runs, not committed: `r1` to `r8`, `r1x`, `V0` to `V2` (in a copy of `aoc/`),
    `localdef.sw`, `overlap.sw`
