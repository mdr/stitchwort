# Proposal: equations for each arm, and functional induction (`f.eq…`, `f.induct`)

**Status:** draft 2, 1 November 2026. Ticket SW-1028, decision D2163 (Matt, 1 November: one
design for SW-802, SW-199's `f.induct`, SW-809 and SW-980). A design note only: nothing in the
compiler changes. The questions are D2173 to D2187 in [§8](#8-decisions-for-matt). Draft 1 was
reviewed independently ("approve with changes"); every point is worked in, one row each, in
[Review 1 and how it was addressed](#review-1-and-how-it-was-addressed); the review is
[function-equations/review-1.md](function-equations/review-1.md).

**Decided (Matt, 1 November 2026):** build stage 1 on the design's recommendations: D2173 to
D2180 and D2183 to D2187 as recommended. **Stage 2 decided (2 November 2026, by Claude under Matt's
delegation of the function equations track):** D2181 and D2182 as recommended. **Stage 1a is built** (SW-1035): see [As built (stage 1a)](#as-built-stage-1a), which
records where the code differed from this note; **stage 1b** (SW-1049), [As built (stage 1b)](#as-built-stage-1b);
**stage 2a**, `f.induct` (SW-1057), [As built (stage 2a)](#as-built-stage-2a); **stage 2b**, `match induct` (SW-1058), [As built (stage 2b)](#as-built-stage-2b).

It revisits D231 ("generated per-leaf equation lemmas: not now",
[equation-lemmas.md §9](equation-lemmas.md#9-decisions)), whose trigger has fired (§1.3), and
takes up T4/D2001 of [research/proof-automation.md](../research/proof-automation.md) ("generated
case theorems, then `f.induct`").

Labels:

- **[checked: file:line]**: read in this repo at `470ef5ee` (main, 1 November);
- **[run]**: a program checked with `target/release/stitchwort` built from main on 1 November.
  The programs are in [function-equations/prototypes/](function-equations/prototypes/) (`p1.sw`
  … `p10.sw`, `day12-induct.sw`, and the reviewer's `review-r1.sw`, `review-r2.sw`); those
  expected to fail say so in a comment;
- **[measured]**: counted or timed by a script, named where used;
- **[cited]**: read in the source linked in [Sources](#sources) on 1 November; Lean outputs
  marked **[run: Lean]** come from Lean 4.34.1 on this machine;
- **[inferred]**: my reasoning, not tested;
- **[unconfirmed]**: believed, not checked.

## The short answer

- **What's missing.** A proof about a function can use `rfl` (when the arguments are known
  enough to compute) or `f.unfold` (the whole body, for `decreasing` and `opaque` definitions).
  Nothing states "this arm, or this branch of an `if` or `match` in it, gives this result when
  these conditions hold". Agents reshaped four programs to get such statements (2021 day 18,
  2024 days 12, 16 and 23; §1.1), all of which this design makes unnecessary, and in three of
  them (a named `match` on a `Bool` or `popMin`) every way of stepping through the definition by
  hand fails; I reproduced it (§1.2, **[run]**).
- **Stage 1: equations.** For each definition with arms or with an `if`/`match` in tail
  position, generate one theorem per **arm** (`explode.eq3`) and one per **branch** below it
  (`Garden.fill.eq2.ifFalse`, `explode.eq3.some`). The arm's left side is the arm's patterns;
  earlier arms that overlap it become hypotheses, in Lean's form (`(a: Nat) → (b: Nat) → left =
  Regular a → right = Regular b → Void`, `n ≠ 3`, `char ∉ ['k', 'j']`); a branch adds the
  condition it was taken under (`fresh: visited.contains position = False`, `isSome: split left
  = Some left2`), in the form a hand-written lemma would take (`notFresh: visited.contains
  position = True` for the `else`, not `Not (… = False)`). Every one is an ordinary theorem,
  built as a kernel term and checked by the kernel; nothing new is trusted (§4).
- **Stage 2: `f.induct`.** For each recursive definition, one induction principle with one case
  per branch, the branch's conditions as hypotheses and one induction hypothesis per recursive
  call, in Lean's "unfolding" form (the motive also gets `f`'s result, so no case needs to
  rewrite with an equation). Proved by the same recursion as `f` (structural, or the same
  `decreasing` measure with the same decrease proofs). Applied as `match induct (f x y) with |
  eq1 … => … | eq2IfTrue … ih => …`, with the motive worked out from the goal as `match`
  already does (§5).
- **Evidence it pays.** On 2024 day 12 the hand-written step lemmas (21 lines) go, and
  `fillCorrect` (67 lines) becomes 51 lines with no decrease proofs and no splitting on `Bool`s
  to convert back to `Prop`s: the prototype checks **[run]** (§6.1). On 2021 day 18, `explode` keeps the shape
  it was first written in, with no `explodeIn` helper and no 0.98 s → 1.1 s run-time cost
  (§6.2, **[run]**).
- **Cost.** A small equation checks in about 0.08 ms and one of `Garden.fill`'s size in about
  1 ms, both elaborated from source [measured]; std has about 1,250 arms in 497 definitions
  [measured], so on the order of 2,000 equations and a fraction of a second to a couple of
  seconds of cold check time, nothing warm (the check cache); a gate switches the library to
  on-demand generation if it costs more than 10%. Generated eagerly, with the definition, as
  the update lemmas already are; listed by `stitchwort doc` in a section of their own, so they
  don't crowd out written theorems (§7).
- **Recommended:** build stage 1 now (D2173), stage 2 after it (D2181, D2182).

## Contents

- [1. The problem](#1-the-problem)
- [2. How other systems do it](#2-how-other-systems-do-it)
- [3. What is generated](#3-what-is-generated)
- [4. How each is proved](#4-how-each-is-proved)
- [5. Functional induction, `f.induct`](#5-functional-induction-finduct)
- [6. Worked examples](#6-worked-examples)
- [7. When, and what it costs](#7-when-and-what-it-costs)
- [8. Decisions for Matt](#8-decisions-for-matt)
- [9. Stages](#9-stages)
- [10. Risks and what this doesn't do](#10-risks-and-what-this-doesnt-do)
- [As built (stage 1a)](#as-built-stage-1a)
- [As built (stage 1b)](#as-built-stage-1b)
- [As built (stage 1c)](#as-built-stage-1c)
- [As built (stage 1d)](#as-built-stage-1d)
- [As built (SW-1071, SW-1069)](#as-built-sw-1071-sw-1069)
- [As built (stage 2a)](#as-built-stage-2a)
- [As built (stage 2b)](#as-built-stage-2b)
- [Sources](#sources)
- [Review 1 and how it was addressed](#review-1-and-how-it-was-addressed)

## 1. The problem

### 1.1 What agents ran into

| Where | What happened | What it cost |
|---|---|---|
| 2021 day 18 (`aoc/NOTES-2021.md:4546-4560`, ranked 2nd at `:4644`; SW-980 item 3) | `explode`'s general arm `Pair left right` comes after `Pair (Regular a) (Regular b)`, so it doesn't hold as written for every pair. Writing its body again in a proof made a second hidden `match` function, not equal to the program's (`E-REFL`) | The program was reshaped around a helper `explodeIn` (`aoc/src/Aoc/Year2021/Day18/Day18.sw:57-70`), which walks the right part even when the left exploded (run time 0.98 s → 1.1 s), plus a hand-proved `explodeUnfold` (`Proofs/Explode.sw:19-29`) used 6 times |
| 2024 day 12 (`aoc/NOTES-2024.md:3517-3535`, ranked 1st at `:3627`) | `match taken: visited.contains position with` in a `decreasing` definition, its equation used in a decrease proof. `rewrite …, taken` gave `E-REWRITE-MOTIVE`, `match c: …` gave `E-MATCH-MOTIVE` | Program rewritten with `if fresh: … = False`; three step lemmas by hand (`aoc/src/Aoc/Year2024/Day12/Proofs/Fill.sw:98-118`) |
| 2024 day 16 (`aoc/NOTES-2024.md:5017-5034`, ranked 3rd at `:5185`) | `match popped: queue.min with`, the same wall | `Graph.searchFrom` takes the popped pair and its equation as extra arguments (`crates/elab/src/std/Graph/Search.sw:243-260`); three step lemmas `Graph.searchEmpty/Skip/Settle` (`:267-290`) |
| 2024 day 23 (`aoc/NOTES-2024.md:7573-7592`, SW-809) | `match found: candidates.popMin with`: `rewrite` gives `E-REWRITE-MOTIVE`, `match` gives `E-MATCH-MOTIVE` | Rewritten with a guard `if fewer: …` and a dead `else`; a step lemma `largestStep` by hand (`aoc/src/Aoc/Year2024/Day23/Proofs/Search.sw:23-34`) |
| D1439 / SW-802 | "A recursive function matching on a `Bool` or `queue.min` and keeping the equation can't be unfolded in proofs; days 12 and 16 got E-MATCH-MOTIVE" | the ticket |
| roguelike (`games/rogue/PROOFS.md:192`) | A literal match's catch-all couldn't be reached at all, so the game looked keys up in a table | Already fixed in the kernel by SW-533 ([literal-match-facts.md](literal-match-facts.md)); what is left is that a proof still needs "an arm per character" (`PROOFS.md:228`), which a catch-all equation states once |

So four programs were reshaped (days 12, 16, 18 and 23), all of which this design makes
unnecessary. [research/agentic-proving.md](../research/agentic-proving.md) counts the wider
problem as category F, "stepping through `match`/unfolding equations; hand-written case
tables", 9 cases (`:835`) **[checked]**; its category K, "program reshaped for the proof"
(`:840`), is mostly the roguelike's other reshapes, not these.

### 1.2 The wall, reproduced

A cut-down day 23 (`p2.sw`, **[run]**):

```
type Big = { value: Nat, isBig: Nat.leq 10 value = True }

def firstBig: List Nat → Option Big
  | Nil => None
  | Cons x rest =>
    match big: Nat.leq 10 x with
      | True => Some ({ value = x, isBig = big })
      | False => firstBig rest

theorem t (x: Nat) (rest: List Nat) (h: Nat.leq 10 x = True):
    firstBig (Cons x rest) = Some ({ value = x, isBig = h }) := …
```

All three ways an agent would try fail:

- `rewrite h in rfl`: `E-REWRITE-MOTIVE`, "replacing `10 <= x` everywhere in the goal doesn't give
  a valid proposition";
- `match e: Nat.leq 10 x with …`: `E-MATCH-MOTIVE`, "generalising this `match`'s scrutinee makes
  its type ill-formed", with the note "a top-level helper with a written signature can always do
  what this `match` would" (`crates/elab/src/matching.rs:125-128`), which doesn't apply;
- `cases`: `E-CASES`, the case `10 ≤ x` left as `Some ({ value = x, isBig = rfl }) = Some ({
  value = x, isBig = h })`.

The same three on a `decreasing` definition (`p6.sw`, `match small: Nat.leq n 0 with … down (n -
1) [decreasing := omega]`, after `rewrite down.unfold n`) fail too, with `E-REWRITE-MOTIVE`,
`E-MATCH-MOTIVE` and, from `cases`, `E-MATCH-MOTIVE` ("this `match` can't be given a type")
**[run]**. So
proof-automation.md's open assumption F2, "today's `cases` doesn't already prove the failing day
16 and day 23 statements" (`docs/research/proof-automation.md:897-899`), holds.

**Why.** The definition's `match big: e` is lifted to a helper `firstBig.%match1 x rest (b: Bool)
(big: Nat.leq 10 x = b)`, called with `(Nat.leq 10 x) rfl` (`crates/elab/src/matching.rs:10-19`)
**[checked]**. Replacing `Nat.leq 10 x` by a variable `y` leaves `rfl: Nat.leq 10 x = y`, which is
ill-typed. What works is to replace the scrutinee *and* its equation together: `J (y e => firstBig
(Cons x rest) = firstBig.%match1 x rest y e) rfl h`. That is one `J`, and it checks (`p2b.sw`,
with the `match` written as a local definition so source can name it) **[run]**. Neither
`rewrite` nor `match` chooses that motive, and source can't write it, because the helper has no
name source can spell. A generator can.

### 1.3 What exists, and why D231 said "not now"

- **Arms compute.** A definition unfolds once its case tree can take a step
  (`docs/core.md:232`), so for a definition without `decreasing` or `opaque`, every leaf of its
  case tree holds by `rfl`. That was D231's argument: a per-leaf lemma adds only a name
  ([equation-lemmas.md §6 (a)](equation-lemmas.md)). Its trigger to reopen: "when a proof needs a
  leaf statement that is tedious to write by hand (many leaves, or arms that overlap so the leaf
  form differs from the source)" (`equation-lemmas.md:765-767`) **[checked]**. Days 12, 16, 18
  and 23 are that trigger.
- **`f.unfold`**, the whole body, for `decreasing` definitions (`crates/elab/src/decreasing.rs:25`,
  `docs/syntax.md:986-989`) and `opaque` ones (`crates/elab/src/opaque.rs:20-21`,
  `docs/syntax.md:1094-1104`). Those definitions don't unfold by themselves on unknown arguments,
  so their arms don't hold by `rfl`: each step is `rewrite f.unfold …` and then a split by hand
  (`Fill.sw:98-118` does it three times).
- **`T.induct` and `T.inductMem`** for nested data types (`crates/elab/src/derive_induct.rs:1-50`),
  made as kernel terms, skipped ("`Stop::Unsupported`") for shapes they don't cover
  (`derive_induct.rs:63-69`) **[checked]**. The model for how this proposal's lemmas are made.
- **Update lemmas** `T.f.update.g`, generated with the type as source and elaborated like
  hand-written theorems (`crates/elab/src/update_lemmas.rs:23`), shown by hover, with names
  that can't be declared by hand (`E-PARSE`, `docs/syntax.md:394`), and indexed so the library
  loads their file when one is named (`crates/elab/src/library.rs:664-686`, as `candidate`s)
  **[checked]**. The model for when they are generated and how they are found; not for how they
  are built, since these statements name hidden helpers that source can't.
- **`match e:`** splits a goal on an expression and refines hypotheses (`docs/syntax.md:1605-1675`);
  **`cases`** splits what the goal is stuck on (`docs/syntax.md:1851-1883`). Neither gets past a
  named `match` in a definition (§1.2).
- **Literal catch-alls compute** in a proof that matches on the same literals
  ([literal-match-facts.md](literal-match-facts.md), `examples/accept/literal-match-facts.sw:43-52`),
  but nothing *states* "for any other `n`, `kind n = 0`".
- **Lifted `match`es** are hidden helpers `owner.%matchN` that source can't name, by design
  (`crates/elab/src/lift.rs:1-30`, [syntax-conveniences.md §2.4](syntax-conveniences.md)); a local
  `def` gives one a name (`docs/syntax.md:289`).
- **No definitional proof irrelevance** (`docs/core.md:143`): two proofs of the same proposition
  aren't equal by computation. This limits one case (§3.5).

## 2. How other systems do it

| | per-clause equations | overlap / catch-all | `if`/`match` inside | functional induction | when made |
|---|---|---|---|---|---|
| **Lean 4** | `f.eq_1 … f.eq_N`, one per alternative of the top-level match; `f.eq_def`, `f.eq_unfold` | earlier overlapping alternatives become `(x = p → False)` hypotheses, one each; a wildcard stays one equation | left on the right side | `f.induct`, `f.induct_unfolding`, `f.fun_cases`: one case per branch (tail `if`/`match` included), IH per recursive call; tactics `fun_induction`, `fun_cases` | on demand, reserved names |
| **Rocq, Equations** | one per leaf of the splitting tree, `f_clause_n_equation_k`, in a rewrite database | a wildcard clause becomes several equations | `with` nodes are auxiliary definitions with their own equations | graph `f_ind`, eliminator `f_elim`, tactic `funelim` | with the definition |
| **Rocq, `Function`** | `f_equation` (the fixpoint equation) | (pure match trees only) | | `f_ind`, `functional induction` | with the definition |
| **Isabelle `fun`** | `f.simps`, one per disjoint pattern; `psimps` for partial | patterns made disjoint by instantiating the later ones ("sequential"); documented downside: "less general", more cases | `if` stays; the induction rule gets a conditional IH | `f.induct`, `f.pinduct`, `f.cases`, `f.elims` | with the definition |
| **Agda** | none: clauses are case-tree reductions; a clause may not hold definitionally; `--exact-split` warns | `CATCHALL` | `with`/`rewrite`, `with … in eq` | none | |
| **Idris 2** | none (case trees) | | `with` | none | |
| **F\*, Dafny** | none: definitions are fuel-bounded axioms for the solver | | | Dafny's automatic induction on lemmas | |

All **[cited]**; details and quotes:

- **Lean.** For `def f : Nat → Nat → Nat | 0, _ => 0 | _, 0 => 1 | n+1, m+1 => 2`, Lean
  generates `f.eq_2 : ∀ (x : Nat), (x = 0 → False) → f x 0 = 1` and `f.eq_3 : ∀ (n m : Nat),
  f n.succ m.succ = 2` (no hypothesis: no earlier alternative overlaps it) **[run: Lean]**.
  The source: for each alternative, "for overlappedBy in matchInfo.overlaps.overlapping i … notAlt
  ← mkArrow (← mkEqHEq discr pattern) notAlt" [L1]. Literals the same way: `cmd.eq_3 : ∀ (x :
  Char), (x = 'k' → False) → (x = 'j' → False) → cmd x = none`, and for `String` literals
  likewise **[run: Lean]**. A wildcard over an enumeration stays one equation, `h.eq_2 : ∀ (x :
  C), (x = C.a → False) → h x = 2` **[run: Lean]**. An `if` or inner `match` stays on the right
  side: `halvings.eq_1 : halvings n count = if h : n / 2 < n then … else count` **[run: Lean]**.
  "We generate equations theorems on demand … each one of them corresponds to an alternative";
  `f.eq_<idx>`, `f.eq_def` are reserved names realized when first named [L2]. `rw [f]` uses
  them: "If `e` is a defined constant, then the equational theorems associated with `e` are used"
  [L3].
- **Lean's functional induction** [L4]: "For each branch of the original function, there is a
  case in the induction principle. Here 'branch' roughly corresponds to tail-call positions:
  branches of top-level `if`-`then`-`else` and of `match` expressions. For every recursive call
  in that branch, an induction hypothesis … the condition of an if-then-else; a let-binding …
  is provided as assumptions". For a `match` on an expression, "equalities connecting the
  discriminant to the instantiation are added (just as if the user wrote `match h : x with …`)".
  `halvings.induct : ∀ motive, (∀ n count, n / 2 < n → motive (n / 2) (count + 1) → motive n
  count) → (∀ n count, ¬n / 2 < n → motive n count) → ∀ n count, motive n count` **[run: Lean]**.
  The unfolding variant `f.induct_unfolding` (Lean 4.20) gives the motive the call's result:
  "should be more reliable, easier to use and more efficient than just case-splitting and then
  rewriting with equational theorems" [L5], and `fun_induction` uses it by default [L3].
  Parameters passed unchanged to every recursive call are taken first and not given to the
  motive (`w.induct` above keeps `n`) **[run: Lean]**.
- **Rocq Equations**: "the clauses correspond to the program's splitting tree … so a single
  source clause catching multiple cases can correspond to multiple equations"; the eliminator
  `f_elim` comes from the function's graph, used by `funelim` [E1].
- **Isabelle**: "Overlapping patterns are interpreted as 'increments' … Isabelle replaces it
  internally by the remaining cases, making the patterns disjoint"; "Since splitting makes the
  equations 'less general', they do not always match in rewriting … Instead of five premises
  it now has seven" [I1].
- **Agda**: "the clause `max m zero = m` does not hold definitionally … If you would try to prove
  that this equation holds, you would not be able to write `refl`"; `--exact-split` warns about
  such clauses [A1].
- **F\*, Dafny**: recursive functions are given to the SMT solver with fuel; no lemmas the user
  names [F1, D1].

**What to take.**

1. **Per arm, with hypotheses** (Lean), not per leaf (Isabelle, Equations). An agent reads arms;
   per-leaf statements multiply and are "less general", and a character catch-all has no finite
   set of leaves at all.
2. **Lean's hypothesis form**: one per earlier overlapping arm, `discriminant = pattern → False`.
3. **Branches** come from functional induction's granularity, not from Lean's equations, because
   the evidence here (§1.1) is about tail `match`es and `if`s, which `f.eq_N` leaves on the right
   side. Stitchwort gets both: an arm equation, and one per branch under it.
4. **The unfolding form** of `f.induct`, and a fixed prefix of unchanged parameters.
5. **On demand vs eager**: Lean generates on demand for Mathlib's size; Isabelle and Equations
   eagerly. Stitchwort's std is small and the check cache absorbs the cost (§7).

## 3. What is generated

### 3.1 Cases: arms and branches

A **case** is a path from the top of a definition to a result: the arm (or the whole body, for
a `:=` definition), then, for each `if`, `if h:` or `match` the body is in tail position of,
which way it went. Tail position goes through `let`s and through the branches of these
`if`s and `match`es, nowhere else: not into a function's arguments, not through `||` or `&&`
(which are `if`s once elaborated, `docs/syntax.md:1475-1490`, but aren't written as a split). A
`match` here is either part of the case tree (a `match` on variables, `matching.rs:3-6`) or a
lifted one, with or without an equation name; both count.

A `:=` body that is, as a whole, a `match` on the header's parameters (compiled into the case
tree) counts as arms: its alternatives are arms 1, 2, …, so `Garden.fill`'s `:= match stack
with | Nil => … | Cons position rest => …` (`aoc/src/Aoc/Year2024/Day12/Day12.sw:74-85`) and the
same definition written with arms get the same equations and names (D2187).

Each arm gets an **arm equation**. Each path below it through at least one split gets a
**branch equation**. A definition with neither arms nor a split gets nothing (it unfolds at
once, or has `f.unfold`). An arm with an **or-pattern** (`| A | B => e`, `Tree::Leaf`'s
`alternatives`, `crates/elab/src/lib.rs:797-812`) has no single left side: it gets one
equation per alternative, `f.eqK.or1`, `f.eqK.or2`, and its branches hang below each.

Every equation takes, in order: the definition's own implicit and `auto` parameters as it has
them (`[a: Type]`, `[auto ord: Ord s]`), the header's parameters, the arm's pattern variables in
written order (the order local definitions already use, `docs/syntax.md:289`), then the
hypotheses, each split's after the variables its pattern binds. A `_` in a pattern becomes a
variable named after the constructor's field it stands for (`Regular _` binds `value`), or `x1`,
`x2`, … where there is no field name, with a digit added on a clash;

```
f.eqK… [implicit] (params) (pattern variables) (hypotheses): f params patterns = right side
```

where the right side is the arm's body (for an arm equation) or the branch's (for a branch
equation), as elaborated, with `let`s substituted (as goals show them, and as the `Abort` step
lemmas already do, `docs/syntax.md:795`). A record pattern is a one-constructor pattern; its
fields are pattern variables like any other.

### 3.2 Shapes, by construct

**Plain constructor arms.** `addLeftmost` (`Day18.sw:47-49`):

```
addLeftmost.eq1 (amount: Nat) (value: Nat): addLeftmost amount (Regular value) = Regular (value + amount)
addLeftmost.eq2 (amount: Nat) (left: Number) (right: Number): addLeftmost amount (Pair left right) = Pair (addLeftmost amount left) right
```

These hold by `rfl` already; they are generated so that every function has its equations, the
same names in the same places, whether or not they are needed (D2177).

**Overlapping and wildcard arms.** For each earlier arm whose patterns unify with this arm's,
one hypothesis: the earlier arm's extra structure, as equations of this arm's variables, implies
`Void`. Arms that can't overlap (`Succ m` against `Zero`) give none. 2021 day 18's `explode`, in
the shape it was first written (§6.2):

```
def explode (depth: Nat): Number → Option Explosion
  | Regular _ => None
  | Pair (Regular a) (Regular b) => if 4 ≤ depth then Some (…) else None
  | Pair left right => match explode (depth + 1) left with …

explode.eq3 (depth: Nat) (left: Number) (right: Number)
    (notArm2: (a: Nat) → (b: Nat) → left = Regular a → right = Regular b → Void):
    explode depth (Pair left right) = (match …) …
```

Where the arguments are known constructors, `cases` proves the hypothesis: `explode.eq3 depth
(Pair x y) r cases` checks (`p7.sw` `leftFound`, `p1.sw` `exUse`) **[run]**. From a fact instead
(`isReg left = False`) it is one line, `a b el er => Bool.trueNotFalse (rewrite el at notReg in
notReg)` **[run: p1.sw]**.

**On an indexed family** this form is ill-typed when the earlier arm fixes an index: for `def
short: Vec Nat n → Nat | VNil => 0 | VCons x VNil => 1 | v => 2`, `notArm1: v = VNil → Void`
compares a `Vec Nat n` with a `Vec Nat 0` (`E-TYPE-MISMATCH`, `review-r1.sw` **[run]**). Lean
states it with a heterogeneous equation (`mkEqHEq` in [L1]); std has no `HEq` (`git grep`)
**[checked]**. Stage 1 skips such an arm, counts it, and `doc` gives the reason; its branches
below are skipped with it (D2185). The equations of arms that fix no index, and of every arm
with no earlier overlap, are made as usual.

**Literal patterns.** A literal is a pattern like any other, so an earlier arm `3` against a
later `n` gives `n = 3 → Void`, written **`n ≠ 3`** (the same proposition), which `omega` proves:
`kindEq3 n omega omega` from `10 ≤ n` checks **[run: p1.sw]**. For **characters**, the earlier
arms' literals on one variable are merged into one hypothesis **`char ∉ ['k', 'j']`**, so a
program's own key list (`char ∉ commandKeys`, which computes to the same) is passed as it is,
and a known character is decided by `byDecision` **[run: p3.sw]**. Only earlier arms that
differ from this one in that column alone are merged; one that also constrains another column
(`| 'k', Nil => …` before `| c, xs => …`) keeps Lean's form, `notArm1: char = 'k' → xs = Nil →
Void`:

```
kind.eq3 (n: Nat) (notArm1: n ≠ 3) (notArm2: n ≠ 7): kind n = 0
commandOf.eq3 (char: Char) (notListed: char ∉ ['k', 'j']): commandOf char = None
```

(Numbers stay one `≠` each: neither `omega` (`E-OMEGA`, with the model `n = 10`) nor `cases`
(`E-CASES`) proves `n ∉ [3, 7]` from `10 ≤ n` **[run: p3.sw]**.) `Int` literals are split by
sign first and `Fin` literals are `FZero`/`FSucc` patterns (`crates/elab/src/lib.rs:3512-3524`);
they give `x ≠ k` for `Int` and the constructor form for `Fin`, as the pattern compiler sees them
[inferred]. Stitchwort has no `Text` literal patterns (`crates/syntax/src/ast.rs:704-745`), so
there is nothing to generate for them.

**Nested patterns** need nothing new: `explode.eq2`'s left side is `explode depth (Pair (Regular
a) (Regular b))`, and `notArm2` above quantifies arm 2's nested variables.

**`if` in tail position.** A `Bool` `if c` gives `c = True` / `c = False`; a decided `if p`
gives `p` / `Not p`; `if h: p` gives `h: p` / `notH: Not p`. Suffixes `.ifTrue` and `.ifFalse`.
**One normalisation** (D2186): when `p` is an equation between a `Bool` and `True` or `False`,
the `else` hypothesis is the other equation, not its negation: `if fresh: b = False` gives
`notFresh: b = True`, the form both hand-written versions chose (`fillSkip`, `Fill.sw:100`;
`Graph.searchSkip`, `Search.sw:276`) **[checked]**. The proof converts with one step
(`Bool.trueNotFalse`), `p10.sw` **[run]**. Which form an `if` on a comparison has depends on how
it was elaborated (`if 4 ≤ depth` is a `Bool` `if` in one place and `Decidable.elim` in another,
SW-980 item 5); the hypothesis follows the elaborated form, which `doc` shows. `gcd`
(`examples/accept/decreasing.sw:45-48`):

```
gcd.eq.ifTrue (a: Nat) (b: Nat) (h: b = 0): gcd a b = a
gcd.eq.ifFalse (a: Nat) (b: Nat) (notH: Not (b = 0)): gcd a b = gcd b (a % b)
```

Both check, by `rewrite gcd.unfold a b in cases` **[run: p4.sw]**.

**`match` in tail position.** Each alternative is a branch. Its suffix is the constructor's name
in lower case (`.some`, `.none`, `.cons`, `.true`), as `T.induct`'s cases are named
(`docs/syntax.md:198`), when the alternative is one constructor applied to variables or `_`;
otherwise `.alt1`, `.alt2`, … in written order (literals, nested patterns, several scrutinees, a
catch-all). On a **variable** of the arm (compiled into the case tree), the alternative's pattern
goes into the left side, like an arm's. On an **expression**, the hypothesis is `e = pattern`,
named after the `match`'s equation name if it has one (`match found: …`), else `is` and the
constructor (`isSome`, `isNone`, `isAlt2`), with a digit on a clash; earlier overlapping
alternatives add `notAlt…` hypotheses as arms do:

```
explode.eq3.some (depth) (left) (right) (inLeft: Explosion) (notArm2: …) (isSome: explode (depth + 1) left = Some inLeft):
    explode depth (Pair left right) = Some ({ toLeft = inLeft.toLeft, number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 })
```

**A named `match` on an expression** (`match taken: visited.contains position with`), the case
of §1.2: the same, and the branch's body has the hypothesis for `taken`. `firstBig.eq2.true (x)
(rest) (big: Nat.leq 10 x = True): firstBig (Cons x rest) = Some ({ value = x, isBig = big })`,
proved by the one `J` of §1.2 **[run: p2b.sw]**.

**Lifted `match` not in tail position** (day 7's `(match c with …) || reach rest (c + 1) k d`,
[equation-lemmas.md §2.2](equation-lemmas.md)): it stays in the right side, shown as `(match …)`
as goals show it; a proof splits it as today. Source can't write it, but can use an equation
that contains it, by name, in `rewrite` or `Eq.trans`. A local `def` in its place gets equations
of its own (below).

**`let`** is substituted (above). One whose value is used many times makes a long statement;
§10 bounds the size. A destructuring `let` is a `let` here too: a tuple or record pattern binds
projections (`patlet.rs`), so a tail `match` or `if` below it gets its branches (SW-1081). One
whose pattern compiles into the case tree instead (a data constructor, `_`, `()`) isn't stated,
and `doc` says so.

**Mutual groups.** Each member gets its equations once the group is final; a call of another
member is just a call.

**Local definitions** are definitions: `reach.left` gets `reach.left.eq1`, `reach.left.eq2`.
Except in a `decreasing` definition: its local definitions and lifted `match`es that call it
take `%rec` (`crates/elab/src/decreasing.rs:19-21`), which a statement can't use, so they get
none in stage 1. The owner's own branch equations already cover those in tail position.

**Not generated** (each listed by `stitchwort doc` with the reason, D2177):

- theorems (nothing unfolds them, `docs/core.md:234`, and nobody rewrites with a proof's arms);
- instances and interface methods: an instance is a record, folded by name until taken apart
  (`docs/core.md:233`); a method written with arms is better as a named `def` the instance points
  to, which gets equations;
- definitions that perform abilities (`{Fail}`, `{State s}`): their arms are computations, whose
  type has no spelling in a statement (`docs/syntax.md:871`, the same reason `match h: reify t`
  is refused); `match reify` is the tool there. **Effect-polymorphic** ones (`List.filter: … {e}
  List a`) get their equations at the empty row, as the hand-written std lemmas about them are
  stated (`List.filterFilter` with a pure `p`). `List.filter (Cons x xs) p = List.filterStep x
  (List.filter xs p) (p x)` with `p: Nat → Bool` is `rfl` **[run: p8.sw]**; stage 1 checks each
  such definition the same way and skips one whose arm doesn't compute at the empty row;
- `Partial` definitions: `Effect.pfix` has no computation rule (`docs/core.md:349-362`: "no computation rules");
- an `opaque` definition with an `unfolding` clause: it has no `f.unfold` either
  (`docs/syntax.md:1100-1104`);
- an arm the case tree never reaches; an indexed family's impossible branches; an arm whose
  overlap hypothesis would compare different indices (above, D2185);
- the cases §3.5 and §4 skip, and a statement over the size bound of §10.

Naming one of these (the index lists every name the source implies, §3.3) is `E-NO-EQUATION`
with the reason, as naming the missing `f.unfold` of an `opaque` definition with an `unfolding`
clause is `E-NO-UNFOLD-EQUATION` (`crates/elab/src/opaque.rs:544-546`).

### 3.3 Names

| Case | Name |
|---|---|
| arm K (1-based, written order; also the alternatives of a whole-body `match` on parameters) | `f.eqK` |
| an or-pattern's alternatives | `f.eqK.or1`, `f.eqK.or2`, … |
| a branch below it | `f.eqK` + one suffix per split: `.ifTrue`, `.ifFalse`, `.some`, `.none`, `.true`, `.alt3`, … |
| a branch of any other `:=` body | `f.eq` + the suffixes: `gcd.eq.ifFalse` |
| hypotheses | the source's names (`fresh`, `found`), `notFresh` for an `else`; `isSome`, `isNone`, … for an unnamed `match`; `notArmJ` for an earlier arm J, `notAltJ` for an earlier alternative, `notListed` for merged characters; `h1`, `h2`, … for an unnamed `if` |

- Names are worked out from the **source alone** (arm count, tail `if`s and `match`es,
  constructor names), so the library index can list them before the file is elaborated, as it
  does `T.f.update.g` (`library.rs:664-686`, marked `candidate`), and naming one loads its file.
  A name the source implies but that elaboration skips (§3.2, "Not generated") is
  `E-NO-EQUATION` with the reason.
- They are **reserved**: declaring `theorem f.eq2` is `E-DUPLICATE` with a note, and a local
  definition can't be named `eq`, `eqK` or `induct` (it would be `f.eq…`). Nothing in std, AoC,
  the roguelike or the examples has such a name today (`git grep` for `\.eq[0-9]` and `.induct`
  declarations, and local `def eq`/`def induct`: none) **[checked]**.
- **Why paths and not Lean's flat numbers** (D2176): `rewrite Garden.fill.eq2.ifFalse` says
  which branch it is, a reviewer can check it against the source, and adding an `if` to one arm
  renames only that arm's branches. Arms keep numbers because overlapping arms have no other
  unique name. Counting a whole-body `match` on parameters as arms (D2187) keeps the names when
  a definition is rewritten from one spelling to the other.

### 3.4 How agents find them

- **`stitchwort doc f`** gets an **Equations** section, before Theorems: every generated
  equation with its statement and the line of the arm or branch it came from (at most 16, then a
  count and the `search` command). Generated equations are left out of the Theorems groups, whose
  `rewrite` group they would otherwise fill (`docs/syntax.md:61`). JSON: `equations`, each with
  `name`, `statement`, `line`.
- **`stitchwort search`** lists them like any theorem, with `"generated": true` in JSON, and
  ranks a generated equation after a written theorem with the same score, so std's 20 or so
  hand-written arm lemmas (`List.allCons`, `List.countNil`, … [measured: `git grep` for `^theorem
  … := rfl` over a constructor]) stay first and `search_bench`'s self-retrieval keeps its top-1.
- **Hover** on a definition shows the count and the first few, as it shows update lemmas.
- **Messages.** `E-MATCH-MOTIVE` and `E-REWRITE-MOTIVE` on a scrutinee that is a named `match`'s
  in a definition `f`, and `E-REFL` between two lifted `match`es (the D229 note, `equation-lemmas.md`
  As built), add a note naming the equation: "`firstBig.eq2.true` states this step; `stitchwort
  doc firstBig` lists them". The current note (`matching.rs:128`) tells agents to define a helper,
  which is how the reshapes of §1.1 happened.
- **[proving-guide.md](../proving-guide.md)** gets a short section: arms and branches have
  equations; `doc` lists them; prefer them to `f.unfold` and a hand split.
- `search --at` finds them as rewrites with no change.

### 3.5 One limit: `if h: p` whose branch uses `h`

For `if h: p then A h else B`, the branch equation is `(h: p) → f … = A h`. The definition's own
`A` gets the proof the decision found, `h'`; so the proof needs `A h' = A h`. That holds:

- by computation when `h` doesn't occur in the right side after unfolding (it is only in a
  `[decreasing := …]`, which `f.unfold` drops: every AoC example, and `gcd` **[run: p4.sw]**);
- by one `J` along `h' = h` when `p` computes to an equation in a type with `DecEq`, which
  includes `<` and `≤` on `Nat` and `Int` (they are `Bool` equations underneath): the proof
  of `h' = h` is `Bool.uniqueEq` (`crates/elab/src/std/core/Decidable.sw:137`) or
  `DecEq.uniqueEq`. The reviewer's `review-r2.sw` proves `Fin.ofNatCheck`'s shape, `if h: i < n
  then Some (Fin.ofNatLt n i h) else None`, this way **[run]**; doing the step with `rewrite`
  instead gave `E-UNIVERSE` (review 1, finding 3), so the generator builds the `J` itself.

Such branches are common in std, not rare: `Fin.ofNatCheck` (`std/Fin/Fin.sw:81`),
`SafeNat`/`SafeInt` construction (`std/Int/Safe.sw:20`, `:24`), `Mod` (`std/Mod/Mod.sw:36`), the
`DecEq` instances (`Fin.sw:53`, `Safe.sw:58`, `Mod.sw:173`), all equations or comparisons
covered by the second rule **[checked]**. Any other `p` isn't provable without proof irrelevance
(`docs/core.md:143`); that branch gets no equation, with the reason in `doc` (D2180).
[proof-irrelevance.md](proof-irrelevance.md) stage 1 would lift this. A `match` on a `Bool` with
an equation name has no such limit: `J` transports the given `h` itself (§1.2).

## 4. How each is proved

Every equation is a theorem built as a kernel term, as `T.induct` is (`derive_induct.rs:40-41`,
"made as kernel terms … their types need the fields' types, which source can't always name"),
because its statement may name `f.%matchN` and its proof `f.%step` or `f.%body`. The kernel
checks it like any declaration; a generator bug gives a refused declaration, never a false
theorem. Proofs, by kind:

1. **Arm, no overlap, transparent `f`:** `rfl`.
2. **Arm with overlap hypotheses:** the definition's own case tree, restricted to the arm's
   patterns: at a leaf of this arm, `rfl`; at a leaf of an earlier arm J, `Void.exfalso (notArmJ
   fields… rfl rfl)`; at a number case, the same literals with the hypotheses ruling them out and
   the default computing by the apart rule ([literal-match-facts.md](literal-match-facts.md)), not
   a `Zero`/`Succ` expansion (which `f.unfold` for `opaque` uses, and which stops at 64 levels,
   `MAX_NUMBER_SPLIT`, `opaque.rs:298-300`). `exEq3`, `kindEq3` and `commandOfEq3` are this proof
   written by hand; they check **[run: p1.sw, p3.sw]**.
3. **`decreasing` `f`:** `Eq.trans (f.unfold …)` and then the above on `f.%step` (with `%rec`
   applied to `y … => f y …`, so recursive calls show as `f`). **`opaque` `f`:** the generated
   theorem is checked with `unfolding f`, as `f.unfold` itself is (`opaque.rs:20-21`), so `f`'s
   case tree computes in it and the proofs are those of 1 and 2. It doesn't go through
   `f.unfold`, so an `opaque` definition with a number pattern past 64, which has no `f.unfold`,
   still gets equations.
4. **Branch:** the arm equation, then one step per split: for an `if`, `Bool.ifThenElse`'s case
   on the hypothesis; for `if h:`, `Decidable.elimEq` (`crates/elab/src/std/core/Decidable.sw:53`,
   the lemma the hand proofs use), §3.5, and the one step of D2186 for a normalised `else`; for a
   `match` on an expression, `Eq.cong` of the helper along the hypothesis (`p7.sw`'s equations do
   this by `rewrite` and check **[run]**); for a
   **named** `match`, one `J` with the motive over the scrutinee and its equation (§1.2,
   **[run: p2b.sw, p6b.sw]**). A helper with copies of variables whose types mention the
   scrutinee (`matching.rs:13-17`) needs them transported too; stage 1 skips those branches
   (`Unsupported`, as `derive_induct.rs` does) and counts them.

Soundness needs nothing beyond the kernel: the statements are ordinary propositions about `f`,
and each proof is a term the kernel re-checks. The hash of each is its type and proof, with `f`
by hash (`crates/core/src/hash.rs:1-6`), so it is the same whichever run made it.

## 5. Functional induction, `f.induct`

### 5.1 Shape

For each recursive definition (structural or `decreasing`), one theorem:

```
f.induct (fixed parameters)
    (motive: (other parameters) → (result: R) → Prop)
    (one case per branch, named after its equation: eq1, eq2IfTrue, eq2IfFalse, …:
       (variables) → (hypotheses) → (one IH per recursive call: motive args (f args)) →
       motive patterns rightSide)
    : (other parameters) → motive params (f params)
```

- **Cases are the equations' cases** (§3.1), so case `eq2IfTrue` goes with `f.eq2.ifTrue`, with
  the same hypotheses in the same order.
- **Unfolding form** (Lean's `induct_unfolding`): the motive gets `f`'s result, and each case
  proves it for the branch's right side, so no case rewrites with an equation. A statement that
  doesn't mention `f` ignores the result (`(a b result => P a b)`).
- **Fixed prefix**: leading parameters passed unchanged to every recursive call (`garden`,
  `plant` in `Garden.fill`) come first and aren't the motive's, as in Lean (`w.induct`,
  **[run: Lean]**).
- **Several recursive calls** give several IHs, in written order; a **nested call** (`ack k (ack
  (Succ k) j)`) gives the inner one's IH and then the outer one's, whose argument is the inner
  call.
- **Calls under a binder** (inside a lambda passed to `List.map`, with a congruence lemma,
  `docs/syntax.md:991-1013`) get no IH in stage 2: `f.induct` isn't generated for such a
  definition, and `doc` says why. Lean quantifies such IHs; that is later work.
- **Mutual groups**: none in stage 2 (Lean has `mutual_induct`; later).
- **Not recursive**: no `f.induct`; the equations and a `match` do the same.

`Garden.fill` (`aoc/src/Aoc/Year2024/Day12/Day12.sw:74-85`) gets, written in the plain form as
the prototype has it (`day12-induct.sw`, §6.1, **[run]**):

```
Garden.fill.induct (garden: Garden) (plant: Char) (motive: List Position → Set Position → List Position → Prop)
    (eq1: (visited) → (members) → motive Nil visited members)
    (eq2IfTrueIfTrue: (position) → (rest) → (visited) → (members) →
      (fresh: visited.contains position = False) → (grows: garden.plantAt position = Some plant) →
      motive (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members) →
      motive (Cons position rest) visited members)
    (eq2IfTrueIfFalse: … (fresh: … = False) → (grows: Not (…)) → motive rest visited members → motive (Cons position rest) visited members)
    (eq2IfFalse: … (notFresh: visited.contains position = True) → motive rest visited members → motive (Cons position rest) visited members):
    (stack: List Position) → (visited: Set Position) → (members: List Position) → motive stack visited members
```

### 5.2 How it is proved

- **Structural `f`:** a recursive theorem with `f`'s own case tree and splits, each case's
  argument applied to the recursive calls of the theorem itself at `f`'s call arguments. The
  calls are `f`'s calls with the same arguments, so the termination check that accepted `f`
  accepts it [inferred; stage 2 checks it on std and AoC].
- **`decreasing` `f`:** a theorem with the same `decreasing` measure, built through
  `decreasing.rs`'s pipeline (a theorem gets `%step`, `%go` and the wrapper,
  `decreasing.rs:28-29`), whose IH calls carry **the same decrease proofs `f`'s calls carry**:
  they were elaborated in the branch's context (the guard `h`, the equation `taken`), and the
  case has the same variables. The prototype's `fillInduct` is this proof by hand **[run]**.
- **Unfolding form** from the plain one and the equations: each case's `motive pats rhs` becomes
  `motive pats (f pats)` by `rewrite f.eqK…`.

### 5.3 Applying it

Explicit, as `Packet.induct` is today (`examples/accept/nested-data-induction.sw:82`):
`Garden.fill.induct garden plant (stack visited members result => …) (cases…) stack visited
members`. The motive is one long line and the hypotheses that mention the targets (`state:
FillState … stack visited members`) must be folded into it by hand (§6.1 does).

So stage 2b adds **`match induct (f args) with`**, by analogy with `match reify t with`
(`docs/syntax.md:848-871`), where `induct` is a keyword only after `match`:

```
theorem fillCorrect … (state: FillState garden plant start stack visited members):
    FillResult garden plant start stack members (Garden.fill garden plant stack visited members) :=
  match induct (Garden.fill garden plant stack visited members) with
    | eq1 visited members => …                                   -- state: FillState … Nil visited members
    | eq2IfTrueIfTrue position rest visited members fresh grows ih => …
    | eq2IfTrueIfFalse position rest visited members fresh grows ih => …
    | eq2IfFalse position rest visited members notFresh ih => …
```

The motive is the goal with the call replaced by `result` and the targets by the motive's
parameters; variables in scope whose types mention a target (`state`) are generalised, as a
`match` on an expression already does (`matching.rs:10-19`), so each arm sees them refined and
each `ih` takes them as premises. The arguments in the motive's places must be distinct
variables (the fixed prefix may be any terms); otherwise it is an error that says to generalise
them first. Arms are named by case, in any order, all required (`E-NONEXHAUSTIVE`). The proof
it writes is `Garden.fill.induct` applied, and the kernel checks it.

## 6. Worked examples

### 6.1 2024 day 12: the flood fill

**Before.** `Garden.fill` (`Day12.sw:74-85`) is `decreasing (garden.unvisited visited,
stack.length)`, a `match stack` and two nested `if h:`s. The proof has three step lemmas by
`f.unfold` and `Decidable.elimEq` (`Fill.sw:98-118`, 21 lines) and `fillCorrect` (`:121-187`, 67
lines), which recurses on the same measure, re-proves the three decreases
(`Nat.LexLess.First (garden.unvisitedInsert …)`, `Nat.LexLess.Second rfl (omega)` twice), and
converts `garden.plantAt position == Some plant` back to a `Prop` (`DecEq.sound`, and a two-line
`other`) because it splits with `match taken:`/`match growing:` on `Bool`s.

**After stage 1.** The three step lemmas are `Garden.fill.eq2.ifFalse`,
`.eq2.ifTrue.ifTrue` and `.eq2.ifTrue.ifFalse`: delete `Fill.sw:98-118` and use those at
the three call sites (`:145`, `:164`, `:179`). With D2186 the skip step takes `notFresh:
visited.contains position = True`, the `taken` the proof has. One is less general than the
lemma it replaces: `fillOther` (`Fill.sw:114-116`) needs only `other`, because both `else`s give
the same result, while the generated `.eq2.ifTrue.ifFalse` follows the program and needs `fresh`
too; it is in scope at `:179`. A generator states what each branch does, not facts that merge
branches.

**After stage 2.** `fillCorrect` by `Garden.fill.induct`: the prototype
(`function-equations/prototypes/day12-induct.sw`, dropped into a copy of the AoC project, with
`fillInduct` and the four equations written by hand as the generator would make them, in the
normalised form) checks with `stitchwort check --no-cache Aoc.Year2024.Day12.Proofs` in 3.9 to
4.8 s user **[run]**. `fillCorrectByInduct` is 51 lines against 67, with no decrease proof, no
`match taken:`/`match growing:` on `Bool`s and none of the conversions they needed (`DecEq.sound`,
the two-line `other`); one case:

```
    (position rest visited members fresh grows ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := ih (takeKeeps garden plant start position rest visited members state fresh grows)
      rewrite fillEq2IfTrueIfTrue garden plant position rest visited members fresh grows in
        Both distinct (…as before…))
```

The `Bool` conversion the `else` needs (`Not (b = False)` to `b = True`) is inside
`fillInduct`'s proof, which the generator writes, not in the user's (`trueOfNotFalse`, used once
in the prototype's `fillInduct`). With the unfolding form the `rewrite` lines go too (4 lines),
and with `match induct` the explicit motive (2 lines). In all, 88 lines become about 45.

Two small findings on the way: std has `Bool.falseOfNotTrue` but not `Bool.trueOfNotFalse`
(`crates/elab/src/std/Bool/Bool.sw:57`) **[checked]**; and `cases`, given `Not (b = False)` with
`b` split to `False`, derived `%fact1: Void` and still reported `E-CASES` **[run]**. Both are
backlog tickets, not part of this design.

### 6.2 2021 day 18: `explode` without the reshape

**Before.** `explode`'s general arm became `explodeIn left right (explode (depth + 1) left)
(explode (depth + 1) right)` (`Day18.sw:60`, `explodeIn` at `:66-70`), and `explodeUnfold`
(`Proofs/Explode.sw:19-29`) states it for every pair under a hypothesis `depth < 4 ∨ height left
+ height right ≠ 0`, used 6 times (`git grep`) **[checked]**.

**After stage 1.** `explode` as first written, with the `match`es in its last arm
(`p7.sw`, §3.2). Its generated equations (generated since SW-1071; stages 1a to 1d skipped
them, "As built (stage 1d)", because the arm is elaborated once per case of arm 2's patterns,
"As built (SW-1071, SW-1069)"):

```
explode.eq3.some      (depth) (left) (right) (notArm2) (inLeft: Explosion) (isSome: explode (depth + 1) left = Some inLeft): explode depth (Pair left right) = Some ({ inLeft | number = Pair inLeft.number (addLeftmost inLeft.toRight right), toRight = 0 })
explode.eq3.none.some (depth) (left) (right) (notArm2) (isNone: explode (depth + 1) left = None) (inRight: Explosion) (isSome: explode (depth + 1) right = Some inRight): … = Some ({ inRight | toLeft = 0, … })
explode.eq3.none.none (depth) (left) (right) (notArm2) (isNone: … = None) (isNone2: … = None): explode depth (Pair left right) = None
```

(the printer shows `{ toLeft = inLeft.toLeft, … }` as an update of `inLeft`; `explode.eq3`
itself isn't generated, as its right side has the lifted `match`), all three kernel-checked,
and used where the left part is a pair with `cases` for `notArm2` **[run: p7.sw; built:
`aoc/src/Aoc/Year2021/Day18/Proofs/Explode.sw`]**. `notArm2` is a stronger premise than
`explodeUnfold`'s (`Explode.sw:21`, `depth < 4 ∨ height left + height right ≠ 0`, which also
covers two regular numbers above depth 4, where arm 2's `else` happens to agree), so
`explode.eq3` is less general; all six uses are at `Regular a, Pair x y` or `Pair x y, _`
(`Explode.sw:43, 46, 125, 128`, `Height.sw:32, 35`), where `cases` proves `notArm2`. `explodeInFound` (`Explode.sw:74`) then splits on
`explode (depth + 1) left` as it does now and rewrites with `explode.eq3.some` or
`.eq3.none.some` instead of `explodeUnfold` and `explodeIn`'s arms. The run time is back to
0.98 s (`aoc/NOTES-2021.md:4558-4560`, the author's measurement). That is what SW-1071 did
(below, "As built (SW-1071, SW-1069)"), with `explodeInFound` restated as `pairFound` (its
premise was `explodeIn … = Some exploded`).

### 6.3 std's `Graph.searchFrom`

`Graph.searchEmpty`, `searchSkip` and `searchSettle` (`crates/elab/src/std/Graph/Search.sw:267-290`,
21 lines) state what `Graph.searchFrom.eq1`, `.eq2.ifFalse` and `.eq2.ifTrue` would: the same
variables, and with D2186 the same hypotheses (`searchSkip`'s `taken: settled.contains state =
True` is `.eq2.ifFalse`'s `notFresh`). They are public std lemmas, so removing them renames their
uses; D2184 asks whether to. Its signature, which takes `queue.popMin` and its equation as
arguments because `match popped: queue.popMin with` couldn't be stepped through
(`aoc/NOTES-2024.md:5017-5030`), could go back to the `match`; that changes a std signature and
its callers for nothing more proved, so D2184 recommends leaving it.

## 7. When, and what it costs

### 7.1 Eagerly, with the definition

Options: **(a) eager**, when the definition is final, as `f.unfold` and update lemmas are;
**(b) on demand**, when a name is first looked up, as Lean does; (c) statements eager, proofs on
demand, which would need the kernel to hold unchecked theorems: refused.

(a) is recommended (D2178), because:

- **Discovery needs them to exist.** `doc` and `search` read the elaborated library; on-demand
  lemmas wouldn't be listed unless those commands generated them, which is (a) again.
- **The cost is small for small bodies.** A file of 1,000 definitions of 5 arms each checks in
  0.22 to 0.24 s user; with one equation per arm written as source (5,000 theorems: per
  definition, four by `rfl` and one with two overlap hypotheses proved by a case split) 0.61 to
  0.66 s: about **0.08 ms an equation**, elaboration from source included, which generated kernel
  terms skip [measured: `prototypes/gen_cost.py`, three runs each, `check --no-cache`].
- **And about 1 ms for a realistic one.** 100 copies of `Garden.fill`'s four equations (400
  theorems, each `rewrite Garden.fill.unfold` and nested `Decidable.elimEq`s on a lexicographic
  `decreasing` definition) added about 0.5 s to `check --no-cache Aoc.Year2024.Day12.Proofs`:
  4.4 to 5.3 s user over four runs with them, 3.9 to 4.7 s over three without, on a loaded
  machine, so noisy [measured: a scratch script copying `day12-induct.sw`'s equations]. So std's
  2,000 or so would cost between about 0.2 s (if all were small) and 2.5 s (if all were like
  these); most std arms are short (346 of the 497 definitions with arms have two), so nearer the
  first. The claim that an equation costs about as much as checking its arm again is inferred,
  not measured; the gate below is what bounds it.
- **std's size.** 1,108 definitions, 497 with arms, 1,253 arms; 117 with an `if` and 69 with a
  `match` somewhere in their body; 11 `decreasing`; 2,496 theorems [measured:
  `prototypes/count.py`, which reads source with regular expressions, so the counts are close,
  not exact]. So about 1,250 arm equations and a few hundred branch equations.
- **The check cache** stores them in the file's entry and replays them (stage 3 admits them
  without checking again, `docs/proposals/check-cache.md` "As built (stage 3)"), so a warm run
  pays nothing.
- **The gate.** If stage 1 adds more than 10% to std's cold check, or to the playground's start,
  generation for the library switches to (b), behind the same names (the index already knows
  them, §3.3). Assumption, in full: that std's cold check is dominated by its 2,496 theorems
  rather than its 1,108 definitions, so that equations of the definitions' size stay under 10%;
  stage 1a measures it, with one data point at `Garden.fill`'s or `Graph.searchFrom`'s size, before
  it merges.

### 7.2 Hashes, cache, search

- **Hashes.** A generated theorem's hash is its type and proof; adding one changes no other
  declaration's hash (`hash.rs:1-6`). Snapshots that list every declaration of a file gain
  entries and are regenerated.
- **Cache entries** grow by the statements, roughly the size of the definitions' bodies again.
- **`search_bench`** (`docs/testing.md:89`): the self-retrieval queries are std's written
  theorems; the tie-break of §3.4 keeps a written theorem first when a generated one has the same
  statement. The bench's numbers (top-1 87.7% of conclusions, 81.2% of left sides,
  `docs/proposals/search.md:999-1000`) are stage 1's acceptance bound.

### 7.3 With what exists

- **`f.unfold`** stays: the whole body in one step, and what the equations are proved from for
  `decreasing` and `opaque` definitions.
- **`T.induct`** is induction on a type; `f.induct` on a function's recursion. A function whose
  recursion is plain structural recursion on a list gets an `f.induct` whose cases are `T.induct`'s
  split further by the arms' conditions.
- **`rewrite`** with an arm equation of a transparent `f` whose left side is constructors has
  nothing to do: the goal has already computed the call, and the rule's left side is read
  computed too (`docs/syntax.md:1748`), so it is `E-REWRITE-NOTHING`, with the note "the goal
  already holds by computing, so `rfl` proves it without a `rewrite`" (`p9.sw`, `exReg`)
  **[run]**. The useful ones are those whose left side is stuck: overlap hypotheses (`f x` with
  `x` a variable: `rewrite exEq3 depth left right h in omega` checks, `p9.sw` `exAtLeast`
  **[run]**), `decreasing` and `opaque` definitions, and branches (stuck on the condition). The
  hypotheses are the equation's arguments, like any lemma's.
- **`match e:`** and **`cases`** keep working; the equations are what to use where they fail
  (§1.2).

## 8. Decisions for Matt

Each with my recommendation in [brackets] and its assumptions in full.

- **D2173. Build stage 1, generated equations for arms and branches?** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** Assumes the
  evidence of §1.1 (four reshaped programs, three hand step-lemma sets) is typical of what
  agents will meet, and that the per-equation cost measured in §7.1 (0.08 ms small, about 1 ms
  realistic, from source) holds or improves for generated terms.
- **D2174. Granularity: an equation per source arm, with earlier overlapping arms as
  hypotheses (Lean), plus one per branch of each tail `if`/`match` (Lean's functional-induction
  granularity)?** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** The alternative is per leaf of the case tree (Isabelle, Rocq
  Equations): unconditional, but more and less general, and impossible for a character
  catch-all. Assumes agents think in arms and branches as written, which is how every note in
  §1.1 describes the problem.
- **D2175. Hypothesis forms: one per earlier overlapping arm, `(vars) → x = C vars → … → Void`;
  `n ≠ k` for a number literal; earlier character literals on one variable merged into
  `c ∉ ['k', 'j', …]` when they constrain that column alone; the condition as tested for a
  split.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** Assumes `omega` keeps not reading `n ∉ [3, 7]` (if it learns to, numbers could
  merge too), that a program's key lists are written as literal lists or definitions that
  compute to them, and that the definition isn't on an indexed family whose earlier arm fixes
  an index (D2185).
- **D2176. Names: `f.eqK` for arm K, a suffix per split (`.ifTrue`, `.ifFalse`, the constructor
  in lower case, `.altN`, `.orN`), `f.eq` + suffixes for any other `:=` body; reserved, local
  definitions named `eq`/`eqK`/`induct` refused; a name the source implies but elaboration skips
  is `E-NO-EQUATION` with the reason.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** The alternative is Lean's flat `f.eq1 … f.eqN`
  over all cases: shorter, but a name doesn't say which branch, and adding an `if` renumbers
  later arms. Assumes names a few segments long are acceptable in proofs
  (`Garden.fill.eq2.ifTrue.ifFalse` is the longest in §6).
- **D2177. Which definitions: every `def` (top-level or local) with arms or a tail split,
  transparent, `decreasing` or `opaque` (without an `unfolding` clause, but whatever its number
  patterns); effect-polymorphic ones at the empty row; not theorems, instances,
  ability-performing or `Partial` definitions, nor a `decreasing` definition's local definitions
  and lifted `match`es.** [Yes, including
  the equations that hold by `rfl`.] **Decided (Matt, 1 November 2026): as recommended.** Generating only the "useful" ones (stuck left sides) would
  save over a thousand std lemmas, and the `rfl` ones can't be used by `rewrite` (§7.3); but
  they are what `doc` shows for each arm and what `f.induct`'s cases are named after, and
  without them agents must guess which functions have equations. Assumes the
  `rfl` ones are cheap (§7.1) and that `doc`'s separate section keeps them from crowding search.
- **D2178. Generate eagerly with the definition, with the 10% gate of §7.1; on demand (Lean)
  only if the gate trips.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** Assumes std's cold check is dominated by its theorems rather
  than its definitions, so that equations of the definitions' size stay under the gate; stage 1a
  measures it before merging.
- **D2179. Discovery: an Equations section in `doc`, a `generated` flag and a tie-break in
  `search`, notes on `E-MATCH-MOTIVE`/`E-REWRITE-MOTIVE`/`E-REFL` naming the equation, a section in
  the proving guide.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.**
- **D2180. A branch of `if h: p` whose right side still uses `h` gets an equation when `h` is
  gone after unfolding, or when `p` computes to an equation in a type with `DecEq` (`<`, `≤` on
  `Nat` and `Int` included), proved by one `J` along `Bool.uniqueEq`/`DecEq.uniqueEq`; any other
  such branch gets none until proof irrelevance lands.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** Such branches are common in std
  (`Fin.ofNatCheck`, `SafeNat`/`SafeInt`, `Mod`, the `DecEq` instances, §3.5), and every one
  found is an equation or a comparison, so covered. Assumes the rest (a `p` that is neither) is
  rare; stage 1b counts them.
- **D2181. Stage 2, `f.induct` for recursive definitions: unfolding form only, a fixed prefix,
  cases named after the equations, no IH for calls under a binder, no mutual groups.** [Yes,
  after stage 1.] **Decided (2 November 2026, Claude under Matt's delegation): as recommended.** The alternatives: also the plain form (`f.inductPlain`; a statement not about
  `f` ignores one argument instead), or Lean's both. Assumes most theorems that need it are about
  `f`'s result, as `fillCorrect` is.
- **D2182. Stage 2b, `match induct (f args) with | eqK … => …`, the motive worked out from the
  goal and hypotheses generalised as a `match` on an expression does.** [Yes.] **Decided (2 November
  2026, Claude under Matt's delegation): as recommended.** Assumes the
  generalisation `match` already does (`matching.rs:10-19`) is what the motive needs; if a goal
  mentions a target inside a proof (as §1.2's did), it can hit `E-MATCH-MOTIVE` like `match`, and
  the explicit `f.induct` stays the fallback.
- **D2183. Equations for lifted `match` helpers not in tail position (`reach.match1.eq2`)?**
  [No.] **Decided (Matt, 1 November 2026): as recommended.** Their numbering is identity metadata, not a name (`syntax-conveniences.md` §2.4); a local
  `def` names one and then gets its own equations.
- **D2184. After stage 1, delete std's `Graph.searchEmpty/Skip/Settle` and rename their uses to
  the generated equations (the same statements, with D2186), rather than keep them as one-line
  corollaries; leave `Graph.searchFrom`'s signature and AoC's programs as they are (day 12 and
  day 18 as acceptance tests only)?** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** There are no outside users, so a name kept for
  compatibility only doubles what search lists ("best end state over churn"); changing
  `searchFrom` back to a `match` changes a std signature and every caller for no gain in what is
  proved.
- **D2185. On an indexed family, an arm whose overlap hypothesis would compare values of
  different indices (`v = VNil` with `v: Vec a n`) gets no equation in stage 1 (counted; `doc`
  says why), rather than a heterogeneous equation (Lean's `HEq`, which std lacks), an index
  equation with a transport, or a generated `Bool` predicate (`isVNil v = False`).** [Yes, skip
  for now.] **Decided (Matt, 1 November 2026): as recommended.** Assumes such definitions are rare among those proofs need equations for: std has few
  functions on indexed families with overlapping arms (`Vec`'s are mostly one arm per
  constructor) [inferred; stage 1a counts them]. If they aren't, the predicate form is the
  likeliest next step.
- **D2186. A split on `b = True` or `b = False` (`b` a `Bool`) states its `else` as the other
  equation (`notFresh: b = True`), not as `Not (b = False)`.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** Both hand-written
  versions chose that form (`Fill.sw:100`, `Search.sw:276`), and the proof converts in one step
  (`p10.sw`). Assumes agents' facts come as `b = True`/`b = False` (what `match e: b` and `cases`
  give), which every proof in §1.1 shows.
- **D2187. A `:=` body that is, as a whole, a `match` on the header's parameters counts as arms
  (`Garden.fill.eq1`, `.eq2.ifFalse`), so the two spellings of a definition have the same
  equation names.** [Yes.] **Decided (Matt, 1 November 2026): as recommended.** The alternative keeps it a split of a `:=` body (`Garden.fill.eq.nil`,
  `.eq.cons.ifFalse`): names that say the constructor, but that change when the definition is
  rewritten with arms. Assumes that rewriting between the two spellings is more common than
  wanting the constructor in the name.

## 9. Stages

| Stage | What | Size | Model |
|---|---|---|---|
| **1a** | `crates/elab/src/equations.rs`: arm equations for transparent, `decreasing` and `opaque` definitions, or-patterns, implicit and `auto` parameters, `_` names; overlap and literal hypotheses (pattern unification against earlier arms), skipping indexed overlaps (D2185); proofs by the case tree (§4, 1–3); the arm↔leaf map recorded by `check_tree` (`Tree::Leaf` has the arm's span, `crates/elab/src/lib.rs:802-813`, the core term doesn't); reserved names, `E-NO-EQUATION`; library index. Before merging: std's cold check and one data point at `Garden.fill`'s size against the 10% gate (§7.1) | medium-large (in the order of `derive_induct.rs`, 2,560 lines, but simpler: no containers) | **Opus** (kernel terms, the overlap computation) |
| **1b** | Branch equations: tail `if` with D2186's normalisation, `if h:` (§3.5, with the `uniqueEq` `J`), `match` on variables and expressions, named `match` (`J`), skipping helpers with copies | medium | **Opus** (dependent motives) |
| **1c** | `doc` Equations section, `search` flag and tie-break, hover, the three messages, `docs/syntax.md` and proving-guide sections | small-medium | **Sonnet** |
| **1d** | Acceptance: `examples/accept/function-equations*.sw` (every construct of §3.2, from the prototypes); 2021 day 18 back to `explode` as first written with its proofs on the equations; 2024 day 12's step lemmas deleted; std's `Graph.search*` deleted and their uses renamed (D2184); `search_bench` and std cold check against §7's bounds | small-medium | **Sonnet** (proofs: Opus review) |
| **2a** | `f.induct` (§5.1, 5.2), through `decreasing.rs` for measures | medium | **Opus** |
| **2b** | `match induct` (§5.3) | small-medium | **Sonnet**, Opus review |
| later | IH under binders, mutual `f.induct`, the `if h:` limit once proof irrelevance lands, equations for instance methods | | |

Each stage is a lane with its tier (`docs/workflow.md`); 1a to 1c change no existing hash; 1d's
std change does.

## 10. Risks and what this doesn't do

- **Statement size.** A long body with a `let` used several times makes a long equation. Bound:
  an equation whose statement is more than ten times its arm's elaborated size isn't generated,
  and `doc` says so [the factor is a guess; stage 1 measures it].
- **Helpers with copies** (§4, 4) and **calls under binders** (§5.1) are skipped, counted, and
  reported by `doc`.
- **Names change with the program.** Adding an arm renumbers the arms after it; proofs naming
  them break, as they would break on the changed behaviour anyway, with `E-UNKNOWN-NAME` and the
  `doc` command in the note.
- **`rewrite` with a transparent constructor arm** finds nothing (§7.3); the existing note
  says why, and the doc section marks which equations have stuck left sides.
- **Not here:** Lean's `simp`-style automatic use of equations (Stitchwort has no simp set;
  `search --at` suggests them); equations for `Partial` or ability-performing definitions;
  closed, shared matchers (D233 stays "not now": equations make the inner `match` statable
  without them).

## As built (stage 1a)

SW-1035, 1 November 2026: `crates/elab/src/equations.rs`. Every definition with arms gets
`f.eqK` for arm K (`f.eqK.orN` for each alternative of an arm with or-patterns), stated and
proved as designed in §3.1, §3.2 and §4, with the hypotheses of D2175. In std that is **1,221
equations** when all are made, all checked by the kernel; a program's own are made with it (the
AoC project's check made 1,859 when std's were eager, the roguelike's 1,166) **[measured]**.
Each is an ordinary theorem: nothing new is trusted, and no existing declaration's hash changed:
the hash snapshots of every example and project only gained lines, each a generated `f.eqK`, and
the prelude's is unchanged **[measured]**. The library's and the core's are made on demand (the
cost gate, below).

```
List.filter.eq2 [a: Type] (p: a → Bool) (x: a) (xs: List a):
    List.filter (Cons x xs) p = List.filterStep x (List.filter xs p) (p x)
Option.map2.eq2 [a b c: Type] (f: a → b → c) (x1: Option a) (x2: Option b)
    (notArm1: (x: a) → (y: b) → x1 = Some x → x2 = Some y → Void): Option.map2 f x1 x2 = None
Char.isLineFeedCode.eq2 (x1: Nat) (notArm1: x1 ≠ 10): Char.isLineFeedCode x1 = False
commandOf.eq3 (char: Char) (notListed: char ∉ ['k', 'j']): commandOf char = None
keyed.eq2 (c: Char) (xs: List Char) (notArm1: c = 'k' → xs = [] → Void): keyed c xs = 2
```

**How.**

- **The statement.** The arm's left side and variables come from compiling the arm alone, as
  the definition's own `match` does (so number, character, `Int`, `Fin`, record, tuple and
  indexed-family patterns are read as the compiler reads them), with a probe for its body that
  records the context there. The right side is the body of one of the definition's leaves for
  the arm, read in the arm's variables: `check_tree` records each leaf's place in the case tree
  (its path of choices), which the kernel term has too (§9's "arm↔leaf map").
- **The hypotheses.** The arm's left side unified with each earlier arm's: disjoint gives
  nothing; an overlap gives `notArmJ: (J's variables) → x = p → … → Void` (`x ≠ p` with no
  variables and one equation); single-character overlaps on one variable merge into
  `notListed: c ∉ […]`. An earlier alternative of the same arm is `notOrM`; when several
  alternatives of arm J overlap, `notArmJorM`.
- **The proof.** A kernel case tree on the equation's variables, made by walking the
  definition's own tree with the arm's arguments and splitting a variable wherever the tree does:
  `rfl` at the arm's leaves, `Void.exfalso` of the hypothesis at an earlier arm's (the equations
  the hypothesis takes are `rfl`, or, for a character whose proof field differs from the
  literal's, one `J` along `Bool.uniqueEq`). A `decreasing` definition's tree is its `f.%step`'s,
  `%rec` read as `(y… => f y…)`, each leaf proved by `f.unfold`; an `opaque` definition's
  equations are checked with `unfolding f`.
- **Effect-polymorphic definitions** (`List.map`, `List.filter`, `List.find`, …) are stated at
  the empty row: their implicit rows are `Empty` and their implicit divergences `Total`, and the
  effect library's plumbing (`bindDv Total Empty c next`, `CompIn Empty a`, …) is computed away,
  so the statement reads as pure code (§3.2). Those whose types are still computations at the
  empty row (`Parse.*`, `Terminal.*`, the effect library's own) are skipped.
- **A budget per equation** (5,000,000 steps, terms of 1,000,000 nodes, 100,000 frames):
  running out skips the equation with the reason instead of failing the definition. An arm
  whose `rfl` the kernel can only check by computing far took, without it, over 18 GB to check
  `def go | Succ n => digits 40 1234567 0 + digits 40 (k + n) 0 + go n` (the native test
  `s6::division_stops_where_the_machine_does`); with it, 0.4 s **[measured]**.
- **`let`s** in the right side are substituted (§3.1); a right side more than ten times the
  arm's elaborated body (and over 256 nodes) isn't generated (§10).
- **At most 64 number hypotheses** (D2189, SW-1053): an equation that would take more than 64
  `notArmJ: n ≠ k` (in practice a catch-all after 65 or more number arms) isn't generated,
  decided before any kernel work, and `E-NO-EQUATION` says how many and the cap. Its proof
  splits on the number with every hypothesis in context, and the kernel refines the whole
  context at each number of a number case (`check_num_case` → `substitute_in`), so checking it
  costs their count squared: on a table `t 0 = 0 … t 255 = 255; t _ = 0` the catch-all was
  1.3 million of the check's steps and 0.49 s; at 1,000 arms it ran out of the budget after
  6.9 s and was skipped anyway **[measured]**. At 64 it costs about 10 ms **[measured: `check
  --no-cache`, 64 arms against 65]**. With the cap, the bench's `check-number-table` is 20,748
  steps and 5 ms, `check-number-wide` 81,012 steps and 24 ms. **Merging the numbers into one
  `notListed: n ∉ [0, 1, …]`**, as characters are, **was tried and rejected**: it cut the time
  (table 74 ms, wide 0.28 s) but not the steps, which stayed quadratic (table 1.75 million,
  +34%; the 1,000-arm catch-all still over the budget), since the one hypothesis holds the
  whole list, which each number's refinement copies again, and refuting arm i proves
  `kᵢ ∈ [k₁, …]` by walking the list to position i; and `omega` reads `n ≠ k` but not
  `n ∉ […]` (D2175). Characters keep their merge. Refining a context type only when it's
  looked up would make the per-arm `≠` form linear; that's a kernel change, left to its own
  ticket.
- **What isn't generated** is recorded with the reason (kept in the check cache), and naming it
  is `E-NO-EQUATION` with that reason; a theorem's or instance's arms are said from the
  definition. `doc f` lists the equations with the other theorems about `f` until stage 1c gives
  them a section; `doc f.eq2` itself isn't found, as `doc f.unfold` isn't (1c).
- **Names** are reserved: `theorem Kind.eq2` beside a definition `Kind` is `E-DUPLICATE` with a
  note, and a local definition called `eq`, `eqK` or `induct` is `E-LOCAL-DEFINITION`. The
  library index lists `f.eqK` and `f.eqK.orN` for every definition with arms, as candidates.
- **Search** lists them like any theorem, after the written theorems of the same relation and
  place (below; **accepted**, Matt, 1 November 2026). `search_bench`'s self-retrieval queries are
  the written theorems; the equations are candidates.
- **On demand** (D2178's fallback, below): a top-level definition of the core or a library file
  gets its equations when they're first named, not when it's checked. A reference to `f.eq2`
  (as a name, or `f`'s field) is one of the module's needs, as a library file is: the
  equations are made after the files load and before the module's check-cache entry starts, so
  never part of it, and the entry lists them so a replay makes them first. They're made (since
  SW-1068, in the defining file's scope, below) from
  the definition's source in the library index, its leaves found by compiling its arms again (a
  definition with a `()` arm can't be, and says so). A library file's own proofs that name its
  equations get them once the definition is final. `search` (and `doc`, which lists through it)
  makes every put-off equation before it lists. Local definitions' stay eager.

**Where the code differed from this note.**

1. **An overlapped arm whose body lifts a `match` has no one right side.** §3.1 says the right
   side is "the arm's body … as elaborated", assuming one elaboration per arm. But an arm the
   case tree splits further, because an earlier arm overlaps it, is elaborated once for each of
   its leaves, and a `match` (or local definition) lifted from it is lifted once per leaf, each
   copy capturing the variables that leaf refined. For 2021 day 18's `explode` as first written
   (`p7.sw`), arm 3 becomes `explode.%match1 depth a x y s` at the leaf `left = Regular a,
   right = Pair x y` and `explode.%match2 depth right x y s` at `left = Pair x y` (two helpers of
   different types), so no term states `explode depth (Pair left right) = …` in the arm's own
   variables **[run: the core terms of `p7.sw`'s `explode`, printed]**. Such arms are skipped
   with `E-NO-EQUATION` (`examples/reject/function-equations-overlap-capture.sw`): none in std,
   none in AoC, three in the examples (`termination-list-patterns.sw`'s `firstSome.eq3`,
   `sumSmall.eq4`, `doubledSmall.eq3`) **[measured]**. The hypothesis form is as designed:
   `ex.eq3`, the same arm without the `match` (`p1.sw`), is generated exactly as §3.2 states
   `explode.eq3` (`crates/driver/tests/function_equations.rs`). Branch equations (stage 1b)
   aren't affected: `explode.eq3.some` states only the branch's result, and each leaf is proved
   on its own (stage 1b skipped them all the same, stage 1d; SW-1071 makes them). Options for the arm equation: leave it skipped (recommended: its branches are what
   proofs use); state it with a fresh helper elaborated once in the arm's variables (a new hidden
   declaration per such arm, proved equal to each leaf's helper by a case split on the scrutinee);
   or elaborate such arms once, in the arm's variables, for the definition itself (changes
   existing hashes).
2. **`kind.eq3`'s variable.** §3.2 shows `kind.eq3 (n: Nat)`, but with the prototype's `| _ =>
   0` the rule of §3.1 names it `x1` (`kind.eq3 (x1: Nat) (notArm1: x1 ≠ 3) (notArm2: x1 ≠
   7)`); `| n => 0` gives `n`. Both are tested.
3. **The search tie-break** of §3.4 ("after a written theorem with the same score") wasn't
   enough: a generated equation with a closer fit still took first place from one written
   theorem in each self-retrieval sample (`Std.Ring.mul.eq1` before
   `Std.Ring.polySubSelfExample`). A generated equation now ranks after the written theorems of
   the same relation and place, before specificity, and the benchmark is unchanged: conclusions
   87.9% strict top-1 (MRR 0.914) and left sides 83.2% (MRR 0.893) on the lane sample, with or
   without the equations as candidates **[measured]**. Accepted (Matt, 1 November 2026).
4. **The 1a/1b split** is practical. An arm whose right side is a `match` on its own variables
   is compiled into the case tree, so has no arm equation; its alternatives are branches (1b).
   In 1a it is skipped with that reason: `List.chunksOf.eq1`, `Ansi.stripChars.eq1`/`.eq2`, AoC
   2021 day 10's `scan.eq3`, 2024 day 6's `Spec.route.eq2`, and `takeFirst.eq2` in the examples.
5. **The printer** shows `x = p → Void` as `x ≠ p`, so `notArm2: … → left = Reg a → right ≠
   Reg b` is the term §3.2 writes with `→ Void`.

**What std skips** (79 names, besides theorems and instances): 70 that perform abilities at
the empty row (`Parse.*`, `Terminal.*`, `Abort.need`, `Fail.need`, the effect library's own), 6
arms with `()`, 3 whose right side is a `match` on the arm's variables **[measured]**. An arm
that an earlier arm covers, or that the case tree never reaches, is skipped too (the examples'
`redundant-arms.sw`, `int-patterns.sw`). None was refused by the kernel, in std, AoC, the
roguelike or the examples (AoC: 1,859 made, 5 skipped, all a `match` on the arm's variables;
the roguelike: 1,166 and 3) **[measured]**.

**The cost gate (D2178) tripped, so the library's and the core's are on demand.** Made eagerly,
std's cold check (every library file loaded, no cache) was within noise (6,746 ms before, 6,670
ms after, one run each), and `check --no-cache Aoc.Year2024.Day12.Proofs` about +2% (3.73, 3.82,
3.73 s user against 3.72, 3.67, 3.66). But a small program's start was not: the benchmark
`check-closed-*` (the core, and the library files `List.range` needs, checked without the cache,
as the playground does) took 1,236,425 steps (+14.9% over the recorded baseline, against main's
+3.6%), +25% allocations, +29% peak heap and 88 ms. With the library's and the core's equations
on demand it takes 1,114,756 steps, 1,171,710 allocations and 3.1 MB, main's numbers, and 77 ms
**[measured: `stitchwort-bench check-closed-rfl`, once before and once after]**. The cost was
the library files', not the core's: putting off only the core's left it unchanged. A program's
own equations stay eager (its namespace is cached).

## As built (stage 1b)

SW-1049, 2 November 2026: branch equations, in `crates/elab/src/equations.rs`
(`Elaborator::branch_equation`). Below every arm (and below a `:=` body that isn't a `match` on
its parameters, as `f.eq`), each way through the `if`s and `match`es in tail position gets an
equation, named and stated as §3.2 and §3.3 say; the names come from the source alone
(`branch_paths`), so the library index lists them as candidates and naming a skipped one is
`E-NO-EQUATION`. Every one is a kernel-checked theorem within its own budget, as in 1a; no
existing declaration's hash changed (the hash snapshots of the examples and projects only gained
lines) **[measured: `task snap:hashes`]**.

```
firstBig.eq2.true (x: Nat) (rest: List Nat) (big: 10 ≤ x): firstBig (Cons x rest) = Some ({ value = x, isBig = big })
countFresh.eq2.ifFalse (b: Bool) (rest: List Bool) (notFresh: b = True): countFresh (Cons b rest) = countFresh rest
check.eq.ifTrue (n: Nat) (i: Nat) (h: i < n): check n i = Some (Fin.ofNatLt n i h)
takeFirst.eq2.cons [a: Type] (k: Nat) (x: a) (rest: List a): takeFirst (Cons x rest) (Succ k) = Cons x (takeFirst rest k)
headOr.eq.some (d: Nat) (xs: List Nat) (x: Nat) (isSome: List.head xs = Some x): headOr d xs = x
both.eq.alt2 (a: Option Nat) (b: Option Nat) (notAlt1: (x: Nat) → (y: Nat) → (a, b) ≠ (Some x, Some y)): both a b = 0
```

(The printer shows `Nat.leq 10 x = True` as `10 ≤ x`; `crates/driver/tests/function_equations.rs`,
`branch_equations`, checks these and the rest of §3.2's constructs.)

**How.**

- **A `match` on the arm's variables** compiled into the case tree (the 1a leftover) makes rows
  of its own, one per alternative, whose patterns are probed below the arm's: their left sides
  have the patterns, their hypotheses are the earlier arms and the earlier alternatives
  (`notAltJ`) they overlap, and they are proved as arms are, walking the tree past the arm's leaf.
  The arm itself keeps no equation (`E-NO-EQUATION` says its alternatives have them).
- **Below a row**, each split adds its hypothesis and the proof goes on, at the row's leaf (case
  splits may only be at the top of a declaration), from the row's proof along a proof that the
  row's right side is the branch's: for a `Bool` `if`, one `J` on `c = True`; for `if h: p`,
  `Decidable.elimEq`, with a `J` along `Bool.uniqueEq` (an equation of `Bool`s: `<` and `≤`) or
  `DecEq.uniqueEq` (its instance read off the decision) where the branch uses `h` (§3.5), and
  D2186's `else` refuted from the other `Bool` equation; for a lifted `match`, the helper's own
  equation for the alternative (made by 1a's machinery on the helper, with its alternatives as
  arms, so earlier alternatives give `notAltJ`), carried along `e = pattern` by one `J` whose
  motive replaces the scrutinee *and* its equation argument (§1.2's `J`).
- **A `match` on the alternative's variables inside a lifted `match`** is compiled into the
  helper's tree, so the helper's rows go below the alternative as an arm's do.
- **The notes** of §3.4: `E-MATCH-MOTIVE`, `E-REWRITE-MOTIVE` and `E-REFL` whose terms mention a
  lifted `match`'s helper list the owner's equations whose proofs go through it ("the `match`
  inside `firstBig` has generated equations …: `firstBig.eq2.true`, `firstBig.eq2.false`"),
  all three reproduced from `p2.sw` (`the_walls_errors_name_the_branch_equations`). `doc` marks a
  branch `[stuck]` (a parameter its left side doesn't mention is a hypothesis or a lifted
  pattern's variable) and lists `f.eq.*`.

**Counts** **[measured]**. AoC (eager): 1,061 equations, 382 of them branches (379 through
splits: 229 `Bool` `if`s, 35 `if h:`, 238 lifted `match` alternatives, 10 of them catch-alls,
counting each split on the way; 3 alternatives of a `match` on the arm's variables), and 40
branches skipped: 20 a `match` on a definition's variable below a lifted alternative (2021 day
16's `readPackets`, 2024 day 24's `repair` and `Wire.ofName`), 9 a branch using `h` of a
condition that isn't an equation or comparison (D2180), 9 a `match` on several expressions,
and 2 arm equations whose alternatives replace them (`scan.eq3`, `Spec.route.eq2`, whose
`.nil`/`.cons.ifTrue`/… and `.none`/`.some` are made). AoC was reshaped around the wall, so it
has no named `match` and no branch using `h`. std (every equation `search` makes, all files
loaded: the ignored test `the_librarys_equations`): 306 branches (373 `Bool` `if` steps, 26 `if
h:` of which 6 normalised by D2186 and 5 using `h`, 73 lifted alternatives, 12 of them catch-alls and 2 of a named
`match`es), among them `Graph.searchFrom.eq2.ifTrue/ifFalse` (§6.3's) and `List.chunksOf.eq1.nil/.cons`;
skipped branches: `Mod.ofNat.eq.ifFalse` (below), one over the size bound, 10 whose helper's
alternatives can't be compiled again from the caller's scope, and the branches of definitions
skipped whole. None was refused by the kernel in std, AoC or the examples.

**Cost** **[measured, one run each, `/usr/bin/time -l`, main at `03fb0bf3` against the lane]**:
`check --no-cache` of the AoC project 655.3 G → 656.7 G instructions (+0.2%), 47.9 → 47.5 s,
peak 1,569 → 1,573 MB; `search List.length` with no cache (every library file and every
equation made) 78.4 G → 79.4 G instructions (+1.2%), 6.18 → 6.26 s, peak 223 → 234 MB (+5%).
Within the 10% gate. std's and the core's stay on demand, so a program's start pays nothing
until it names one.

**Where the code differed from this note.**

1. **`gcd.eq.ifFalse` isn't generated.** §3.2 and §3.5 assumed `gcd`'s `else` uses `h` only in
   `[decreasing := …]`; but `a % b` takes an `auto` proof that `b ≠ 0`, found from `h`, so the
   `else` branch uses its refutation `Not (b = 0)`, and two refutations aren't known to be equal
   (they are functions into `Void`; without proof irrelevance or function extensionality).
   D2180's limit covers it: skipped with that reason, as is `Mod.ofNat.eq.ifFalse` in std; none
   in AoC. (`p4.sw`'s hand proof works because `cases` on `b` computes the proof away; a
   generator could split the variables a condition mentions, but that is definition-specific.)
2. **Hidden lemmas.** A lifted `match`'s alternative whose proof needs a case split (an earlier
   alternative overlaps it) can't be inlined into the branch's proof, since a case tree may only
   be at the top of a declaration; it is declared once as a hidden theorem `f.%match1.eqK` and
   used. The hash snapshots gain these lines too (`Main.pick.%match1.eq2`). They are left out of
   `doc`'s Equations.
3. **A pair's hypothesis is typed.** `isAlt1: (a, b) = (Some x, Some y)` (and the `notAlt`
   hypotheses after a catch-all, where the scrutinee replaces its variable) carry the
   scrutinee's type, since the kernel can't infer a constructor of a type with parameters.
4. **Not stated in stage 1b** (each skipped, counted above, with its reason): a `match` on
   several expressions (`match a, b with`; `match (a, b)` on one pair is stated); a lifted
   `match` whose helper copies variables whose types mention the scrutinee (§4, item 4; none met);
   an alternative with an or-pattern; and a `match` on a variable of the definition below a
   lifted `match`'s alternative (it refines the definition's own left side, which the helper's
   equation can't say; stated since SW-1069, "As built (SW-1071, SW-1069)").
5. **Line in `doc`.** A branch shows its arm's line, not the branch's.
6. **On-demand generation from a caller's scope** (a 1a limit, met again): `search` and `doc`
   make the library's put-off equations by compiling arms again in the caller's scope, where a
   library file's own constructors (`Map.Tree`'s `Tip`, `Vec`'s `VNil`, `Omega`'s) aren't
   visible unless imported, so those definitions' equations (and branches) are skipped there
   ("its arms couldn't be compiled again: unknown name `Tip`"); naming one from a program that
   imports the type makes it. **Fixed by SW-1068** (below, "On-demand equations in the defining
   file's scope").

### On-demand equations in the defining file's scope (SW-1068)

SW-1068, 2 November 2026. The cause of item 6 above: `ensure_equations_of`
(`crates/elab/src/equations.rs`) set only the full names' module (`Std`) and compiled the arms
again (`recompute_leaves`) in whatever scope was current: the program's, `search`'s, or the
library file loading at the time. A library file's own imports (`import Map.Tree (Tip, Bin)` in
std/Map/Raw.sw) weren't there, so its definitions were skipped wherever the caller didn't
import the same names. The result depended on who asked.

Now `Elaborator::in_library_file` (`crates/elab/src/library.rs`) runs the generation in the
defining file's scope, as it had while loading: the library's names (`loading_prelude`), no
namespace root, no file mode, a module of that one file with the file's own imports, and the
caller's module, imports and warnings put back afterwards. The file that's loading (its own
proofs naming its equations) is in its own scope already and is left as it is. **The core** loaded
before the library's names were installed, so while its equations are made the names it didn't
declare are hidden (`Scope::core_only`, a `CoreExtent` of the core's definitions, data types and
abilities taken at `install_library`, plus the equations being made). Without this,
`Effect.rowOp`'s `| Empty =>` read std/Abort/Abort.sw's `Std.Empty` ("`Empty` isn't a
constructor").

`a_library_equation_is_the_same_however_it_is_made`
(`crates/driver/tests/function_equations.rs`) builds a test library whose file imports its own
type's constructors, and checks that `Box.Tree.count.eq1`, `.eq2.ifTrue` and `.eq2.ifFalse`
have the same statement and the same hash made while the file loads (its own proof names
one), by `search`, and by a program that names one without importing the constructors.
`search_makes_the_equations_of_a_file_with_its_own_constructors` makes `Map.Tree.size.eq1` and
`Map.Tree.singleL.eq2` from `search`. Both failed before.

**Counts** **[measured: `the_librarys_equations`, every library file loaded]**: 1,221 equations
made (306 branches) before, **1,575 (344 branches)** after. The 359 names skipped as "couldn't be
compiled again" (30 different unknown names: `Tip` 54, `Printable` 41, `FLe` 30, `VNil` 24,
…) are now 0; the ignored test asserts it. What std still skips (131): 117 that perform
abilities, 6 with a `()` arm (`Void.absurd`, `Empty.absurd`, …: a `()` arm can't be compiled
again), 3 whose right side is a `match` on the arm's variables, 3 branches of
`Terminal.decode` (a `match` below an alternative that splits a definition variable; before,
the whole definition was skipped), `Mod.ofNat.eq.ifFalse` (D2180) and one over the size bound.

**Cost** **[measured, one run each, `/usr/bin/time -l`, `search List.length --no-cache`]**: 76.46 G
→ 76.82 G instructions (+0.5%), 6.13 → 6.25 s user, peak 210 → 212 MB.


## As built (stage 1c)

SW-1067: `doc`, `search`, hover and two of the messages; the docs.

- **`doc f`** has an Equations section before Theorems (`Session::equations_of`,
  `crates/driver/src/doc.rs`): each generated equation with its statement and the line of its
  arm, at most 16 and then a count and the `search` command; `[stuck]` marks an equation whose
  left side doesn't compute (§7.3), decided from the statement: it takes an overlap hypothesis
  (`notArm…`, `notAlt…`, `notOr…`, `notListed`) or `f` is `decreasing` or `opaque`; then "Not
  generated:" with the recorded `E-NO-EQUATION` reasons. JSON: `equations` with `total`, `shown`
  (`name`, `statement`, `line`, `file`, `stuck`), `skipped` (`name`, `reason`), `command`.
  Generated equations are left out of the Theorems groups. `doc` makes the put-off equations
  of std and the core first, as `search` does.
- **`search`** gets `"generated": true` (absent for written theorems) and `· generated` in the
  text. The tie-break was already in (SW-1035, SW-1055): a generated equation ranks after the
  written theorems of the same relation and place in plain `search` and `search --at` alike.
- **Hover** on a definition adds "Equations (N)" and the first four, for those made: a
  program's, and a library definition's only once something has made them (hover doesn't force
  the on-demand ones).
- **Messages.** `E-UNKNOWN-NAME` for `f.eqK` that doesn't exist (`crates/elab/src/equation_notes.rs`),
  noting which equations `f` has and pointing at `doc f`; and `E-REWRITE-NOTHING` with an
  arm equation as the rule gets a note that a call that computes needs no equation and that
  `doc` marks the stuck ones (`examples/reject/function-equations-renumbered.sw`,
  `-computed-rewrite.sw`).
- **Not done here:** the notes on `E-MATCH-MOTIVE`, `E-REWRITE-MOTIVE` and `E-REFL` that name
  `firstBig.eq2.true`: they name branch equations, so stage 1b added them (below, "As built
  (stage 1b)").

## As built (stage 1d)

SW-1070, 2 November 2026: acceptance. Three of the four items moved onto the generated
equations; 2021 day 18 did not, and says why.

- **`examples/accept/function-equations-branches.sw`** (new; `function-equations.sw` from 1a
  already has the arm constructs): every branch construct of §3.2, each used in a small proof by
  naming the equation or by `rewrite`: a `Bool` `if` (`big.eq2.ifTrue/ifFalse`, `rewrite … in
  omega`), `if h:` with D2186's complement (`countFresh.eq2.ifFalse`), `if h:` using `h`
  (`check.eq.ifTrue`), a `decreasing` definition (`gcd.eq.ifTrue`), `match` on an expression
  (`headOr.eq.some/none`), on a variable of the arm (`takeFirst.eq2.cons`), a catch-all after an
  overlapping alternative (`both.eq.alt1/alt2`, `cases` for `notAlt1`), nested `match`
  (`firstTwo.eq.some.succ`), and §1.2's named `match` (`firstBig.eq2.true/false`). It checks and
  audits (43 theorems, 0 failed, 0 warnings); its hash snapshot is new.
- **2024 day 12.** `fillSkip`, `fillTake` and `fillOther` (`Proofs/Fill.sw`, 21 lines with docs)
  deleted; `fillCorrect`'s three `rewrite`s name `Garden.fill.eq2.ifFalse`,
  `.eq2.ifTrue.ifTrue` and `.eq2.ifTrue.ifFalse` (the last takes `fresh` and `other`, as §6.1
  said). No theorem statement changed (the three lemmas had no other use). The equations'
  argument order is `garden plant visited members position rest` (the header's parameters, then
  the arm's variables), not the lemmas' order. `check --no-cache Aoc.Year2024.Day12.Proofs`:
  3.69 s user before, 3.60 s after; audit 0 failed (its one warning, `chainSnoc`, is older and
  untouched).
- **std.** `Graph.searchEmpty`, `searchSkip` and `searchSettle` (26 lines) deleted; their three
  uses in `Graph.searchFromCorrect` name `Graph.searchFrom.eq1`, `.eq2.ifFalse` and
  `.eq2.ifTrue` with the same arguments. No other statement changed; the hashes of
  `searchFromCorrect` and `distancesCorrect` (their proofs) did, and the prelude snapshot lost 3
  lines and gained 4 `Graph.searchFrom.eq*` (the proof now makes them). `audit Std.Graph`: 47
  theorems, 0 failed, 0 warnings.
- **Numbers against §7** **[measured]**. `search_bench` (daily sample): conclusions 2,535
  queries, 0 not found, strict top-1 87.4%, recall@10 98.1%; left sides 1,655, 80.9%,
  recall@10 99.2%; 0 internal errors. The tree without this lane's std change gives 2,538
  queries, 87.4% and 80.9% (the same), so the lane moves neither. Both are 0.3 points under
  §7.2's 87.7% and 81.2%, which predate the generated equations; the test's own floors (86%,
  78%) hold. Std cold check (`search List.length --no-cache`, every library file): 5.93 and
  6.01 s user before, 5.85 and 5.85 s after, far inside the 10% gate.

**2021 day 18 stays as reshaped.** `explode` as first written was restored and `stitchwort doc`
run on it: `explode.eq1`, `eq2` and its two branches are made, but **`explode.eq3` and its
`.some`, `.none.some`, `.none.none` are not** ("an earlier arm overlaps it, so its body was
elaborated once for each case of that arm's patterns, each with the variables refined (a lifted
`match` or local definition captures them): no one right side states it"). That is the limit
stage 1a recorded (`an_overlapped_arm_with_a_lifted_match_is_skipped_with_its_reason`), and it
is exactly day 18's case, so §6.2's claim that the three branch equations are generated was
wrong: `p7.sw` writes them by hand, which checks, but the generator doesn't make them. The
`explodeIn` version and `explodeUnfold` (used 6 times) are left. Unblocking it needs the
generator to state an overlapped arm whose body has a lifted `match`: either elaborating the
body once, unrefined by the earlier arm's patterns, or recognising the per-case copies of the
`match` helper as one function. (SW-1071 did neither; see the next section.)

## As built (SW-1071, SW-1069)

SW-1071 and SW-1069, 2 November 2026, in `crates/elab/src/equations.rs`: the branches of an
overlapped arm whose body captures what the overlap refined, and a `match` below a lifted
alternative on a variable bound further up. Every new equation is a kernel-checked theorem in
its own budget; no existing declaration's hash changed (the hash snapshots only gained the
seven new equations of `termination-list-patterns.sw`) **[measured: `task snap:hashes`]**.

**An overlapped arm's branches (SW-1071).** Of the two options stage 1d named, neither was
needed: the per-case copies of the `match` helper stay as they are, and the definition is
elaborated as before. The branch is read from **each** of the arm's leaves instead, and stated
once in the arm's variables:

- **Reading each leaf.** A walk of the definition's tree with the arm's left side, as the proof
  walks it, records each of the arm's leaves: its context (the arm's variables, then the fields
  the walk split off: `a`, or `x` and `y`), its body read there, and what the walk refined each
  variable to (`left` is `Regular a`) (`Elaborator::refined_leaves`).
- **Going down the splits there.** The branch's splits are gone down from each leaf's body as
  from a right side (the same code, `branch_run`): there the lifted `match` is a call of that
  leaf's own helper (`explode.%match1 depth a x y …` at `Regular a, Pair x y`,
  `explode.%match2 depth right x y …` at `Pair x y, right`), so each step has the helper's own
  equation for the alternative.
- **Stating it in the arm's variables.** In each leaf's hypotheses and right side, every term
  the leaf refined a variable to is that variable again (`explode (depth + 1) (Regular a)` is
  `explode (depth + 1) left`), and no field may be left over; every leaf must give the same
  statement (compared as terms, names and locations aside). The overlap hypotheses are the
  arm's, as for any equation of the arm.
- **The proof** walks the definition's tree as an arm's does, refuting arm 2's leaf by
  `notArm2`, and at each of the arm's leaves goes on along **that leaf's** proof that its body
  is the branch's right side, moved into the walk's context there (the same fields, in the same
  order, since both walks split the same variables). Substituting what the leaf refined back
  into the statement gives the leaf's own terms exactly, so the kernel's check is the leaf's.

So `explode.eq3.some`, `.eq3.none.some` and `.eq3.none.none` are generated as §3.2 and §6.2
state them. The arm equation `explode.eq3` still isn't (its right side is the helper call,
whose captured `a` no term of the arm's variables says), with `E-NO-EQUATION` saying that its
branches have equations; nor is one whose leaves state the branch differently, or leave a field
over (a lifted `match` captured it into the branch's own right side).

**A `match` on a variable bound further up (SW-1069).** Below a lifted `match`'s alternative,
a `match` on a variable the helper captured (the definition's `budget` in 2024 day 24's
`repair`, `bits` and then `rest` in 2021 day 16's `readPackets`, the outer alternative's
`first` in `Wire.ofName`) is compiled into the helper's tree, so the helper's equation for the
alternative takes that variable as the pattern: `explode`-style `J` along `e = pattern` can't
say it. It is stated where the variable is bound, as stage 1b suggested:

- **Finding it.** Going down the splits, the helper's equation's argument for a captured
  variable is matched with the call's; where the call has only the variable, that variable is a
  binder of the statement: one of the row's variables (bound by the left side), or a pattern
  variable of an earlier lifted `match` (`Site`). The `match` that refined it is the one below
  the alternative on that name. The attempt stops and asks for the refinement (`Refine`), and the
  equation is made again with it; each is asked for once.
- **Stating it.** The `match`'s scrutinee and the alternative's patterns are compiled below
  that row, as stage 1b's rows below an arm are: below the definition's row, so the pattern is
  in the left side, `repair.eq.some.succ (bits) (fewer) (b) (isSome: List.head [bits] = Some b):
  repair (Succ fewer) bits = Some (fewer + b)`; below the earlier helper's alternative, so it is
  in that alternative's hypothesis, `Wire.ofName.eq.alt1.alt1.alt1: Text.toList name = ['x',
  tens, units] → (high: Nat) → (low: Nat) → (Char.digitValue tens, Char.digitValue units) =
  (Some high, Some low) → Wire.ofName name = X (10 * high + low)` (the catch-all `.alt4` was
  already made, with `first ∉ ['x', 'y', 'z']`). The variables come in the left side's order
  (the header's parameters, the arm's, then the refining patterns'), then each split's.
- **Proved** as before: the walk with the refined left side reaches the arm's leaf with the
  variable already the pattern, and the helper's equation (a hidden lemma
  `f.%match1.eqK.<segment>` where its proof splits) applies with the pattern's variables solved
  by the match.

**Counts** **[measured: the ignored tests `a_projects_equations` (new) and
`the_librarys_equations`]**. AoC: 1,080 equations, 405 of them branches (before: 1,061 and
382): the 20 of SW-1069 (`readPackets` 15, `Wire.ofName` 3, `repair` 2) are made (1,081 and
402 with day 18 untouched), and 2021 day 18's `explode.eq3.some`, `.none.some`, `.none.none`
once `explode` is back as first written (below; they replace `explodeIn.eq1`–`eq3` and the
reshaped `explode.eq3`). Still skipped: 59 that
perform abilities, 9 branches using `h` of a condition that isn't an equation or comparison
(D2180), **9 `match`es on several expressions** (`transmissionBits`, `sumMagnitudes`,
`letterAlong`, `isCorner`), and 2 arm equations whose alternatives replace them (`scan.eq3`,
`Spec.route.eq2`), and the new `explode.eq3`. std is unchanged by this: 1,221 equations, 306
branches, the same skips as stage 1b (none was an overlapped arm or a refining `match`); 1,578
and 347 once rebased onto SW-1068's equations in the defining file's scope. The examples:
`termination-list-patterns.sw`'s `firstSome.eq3`, `sumSmall.eq4`, `doubledSmall.eq3` stay
skipped, and their seven branches are made. None refused by the kernel.

**`f.induct` (stage 2a, rebased onto SW-1057).** A case of `f.induct` is a branch stated from
the arm's own statement and right side, so it doesn't follow either change: an overlapped arm
whose branches are read from each leaf, or a branch whose left side (or earlier alternative)
is refined. Those definitions get no `f.induct`, each with its reason in `doc`: in AoC,
`explode.induct` (made from the reshaped `explode` before; 99 → 98 `f.induct`),
`readPackets.induct` and `repair.induct` (skipped before too, as their branches had no
equations). std's 208 are unchanged. Making them would mean a case per leaf (for SW-1071) and
cases with refined left sides (for SW-1069); left for a follow-up.

**Cost** **[measured, one run each, `/usr/bin/time -l`, main at `bf6619de` against the
lane]**: `check --no-cache` of the AoC project 649.78 G → 649.87 G instructions (+0.01%), peak
1,541 → 1,545 MB; `search List.length --no-cache` (every library file and every equation)
75.90 G → 76.25 G instructions (+0.5%), peak 211 MB both. The wall-clock times (54.0 → 58.6 s
user, 6.2 → 8.2 s) were taken on a machine running other lanes and say nothing; the instruction
counts are within §7.1's 10% gate.

**2021 day 18 back as first written.** `explode`'s last arm is the two `match`es again and
`explodeIn` is gone. `explodeUnfold` and `explodeInNone` (16 lines) became `pairNoneParts` (9),
which splits on `explode (depth + 1) left` and `right` and rewrites with `explode.eq3.some`
and `.eq3.none.some`; `explodeInFound` and `explodeInHeight`, whose premises were `explodeIn …
= Some exploded`, became `pairFound` and `pairHeight`, taking `notArm2` and `explode depth
(Pair left right) = Some exploded` instead; their callers pass `cases` for `notArm2`, as §6.2
said. Every other theorem's statement is unchanged (`pairNone`, `explodeNoneShallow`,
`explodeFound`, `explodeSome`, `explodeNone`, `explodeHeight`); the three files are 49 lines
added and 47 removed. `audit Aoc.Year2021.Day18`: 0 failed; the warnings are main's (15 or 16:
`solvePart2.eq.none` warns on some runs of the search and not others, on main too).

**Not done: a `match` on several expressions.** `match a, b with` lifts one helper taking both
scrutinees, so the branch needs a hypothesis for both and a `J` along each. It doesn't fall out
of either change; the natural statement is the one `match (a, b)` already has, `isAlt1: (a, b)
= (p, q)`, proved by one `J` whose motive takes the pair apart with its projections. Left for
its own ticket.

## As built (stage 2a)

SW-1057, 2 November 2026: `f.induct`, in `crates/elab/src/equations/induct.rs` (with a
`decreasing` definition's through `Elaborator::decreasing_theorem` in `decreasing.rs`). D2181 as
decided: the unfolding form only, a fixed prefix, cases named after the equations, no mutual
groups. Every one is a kernel-checked theorem; no existing declaration's hash changed (the hash
snapshots only gained lines: each `f.induct` and its hidden helpers) **[measured: `task
snap:hashes`]**.

```
countAbove.induct (k: Nat) (motive: List Nat → Nat → Prop) (eq1: motive [] 0)
    (eq2IfTrue: (x: Nat) → (xs: List Nat) → (h1: k ≤ x) → (ih: motive xs (countAbove k xs)) →
      motive (Cons x xs) (Succ (countAbove k xs)))
    (eq2IfFalse: (x: Nat) → (xs: List Nat) → (h1: (k <= x) = False) → (ih: motive xs (countAbove k xs)) →
      motive (Cons x xs) (countAbove k xs)):
    (x: List Nat) → motive x (countAbove k x)
Garden.fill.induct (garden: Garden) (plant: Char)
    (motive: List Position → Set Position → List Position → List Position → Prop)
    (eq1: (visited: Set Position) → (members: List Position) → motive [] visited members members)
    (eq2IfTrueIfTrue: (visited) → (members) → (position: Position) → (rest: List Position) →
      (fresh: visited.contains position = False) → (grows: garden.plantAt position = Some plant) →
      (ih: motive (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members)
             (Garden.fill garden plant (…) (visited.insert position) (Cons position members))) →
      motive (Cons position rest) visited members (Garden.fill garden plant (…) (visited.insert position) (Cons position members)))
    (eq2IfTrueIfFalse: …) (eq2IfFalse: … (notFresh: visited.contains position = True) → …):
    (stack: List Position) → (visited: Set Position) → (members: List Position) →
    motive stack visited members (Garden.fill garden plant stack visited members)
```

**How.**

- **The cases** are the leaf equations of 1a and 1b: an arm with no split below it, or each of
  its branches. A case's binders are its equation's, in its order (so `Garden.fill`'s are
  `visited members position rest …`, the header's parameters before the arm's variables, as the
  equations have them, not §5.1's `position rest visited members`), then one `ih` per recursive
  call in the branch's right side, innermost first, then `motive (left side's arguments) (right
  side)`. A recursive definition one of whose cases has no equation gets no `f.induct`, and the
  reason names the equation and its own reason.
- **The fixed prefix**: the leading parameters that every case's left side has as a variable and
  every recursive call passes as it is (`k`, `garden plant`; an implicit `[a: Type]`). An
  effect-polymorphic definition's implicit rows are `Empty` (its equations' row), not
  parameters.
- **The proof** is a kernel term: the definition's own case tree (its `f.%step`'s for
  `decreasing`) on `f.induct`'s parameters; at each leaf, the arm's variables read off the
  leaf, its overlap hypotheses proved there, and below, one split per `if` or lifted `match`
  the arm's branches go through: `Bool.inspect` for a `Bool` `if` and for `if h: b = X` (whose
  `else` is D2186's other equation), `Decidable.elimProof` for another `if h:`, and for a lifted
  `match` a hidden lemma `f.induct.%splitN` (a case on the scrutinee's type, each case given `e
  = C fields`). At each branch the case is applied, its `ih`s being `f.induct`'s own recursive
  calls (for `decreasing`, `%rec` with the decrease proof the definition's call has: the
  equations' right sides are made a second time keeping it, `Def::mark_rec`), and carried to
  `motive … (f lhs)` along the branch's equation by `J`. Structural recursion passes the
  kernel's termination check as the definition's did; `decreasing` goes through
  `decreasing_theorem` (`%step`, `%go` and the wrapper, from the step term), with the measure
  read off the definition's wrapper (`decreasing_measure`).
- **Overlap hypotheses** (`notArmJ`) are proved at each leaf of the arm: one of the hypothesis's
  equations has sides that differ in a constructor there (the case tree separated the arm from
  arm J), and `J` with a hidden definition `f.induct.%apartN` (`Unit` for a value with the
  leaf's constructors on the way to the difference, `Void` otherwise) gives `Void`. A `notListed`
  (characters) or a number arm's hypothesis isn't proved this way; such a definition gets none.
- **Calls under binders.** §5.1 said calls under a binder get no `ih` and the definition no
  `f.induct`. As built, a call under a binder whose arguments (and decrease proof) don't mention
  the binder is lifted out and gets its `ih` like any other: the thunks of `&&`, `||` and an `if`
  that isn't in tail position (`Omega.allZero`'s `Omega.isZero a && Omega.allZero as`). One whose
  arguments do mention it (a function given to `List.map`) makes the definition skip.
- **Names and discovery.** `f.induct` is reserved (`theorem f.induct` beside `def f` is
  `E-DUPLICATE`); naming a skipped one is `E-NO-EQUATION` with the reason; a definition that
  doesn't call itself gives `E-UNKNOWN-NAME` with a note saying so. A recursive definition whose
  equations aren't made at all (abilities, on-demand compilation failing) records why for
  `induct` too. `doc f` lists `f.induct` first in its Equations section (so the 16 shown never
  cut it), its skip reason under "Not generated"; `search` marks it generated
  (`is_generated_name`, which tells it from a data type's `T.induct` by whether a type has the
  owner's name); a reference to `f.induct` is a module's need, as `f.eq2` is, so std's are made
  on demand. `doc` and hover name it beside the count of equations, not in it ("2 generated
  equations and f.induct", SW-1073); `doc --json` gives it as `equations.induct`, outside
  `shown` and `total`.
- **Budget**: one attempt, with the per-equation budget of 1a (`ATTEMPT`); out of it, skipped.

**Counts** **[measured: `crates/driver/tests/function_induct.rs`, the ignored
`the_librarys_inducts` and `a_projects_inducts`]**. std (every file loaded, every put-off
equation made): **178 made**, none refused by the kernel; skipped for its own reasons 9:
`List.unfold` (a lifted `match` with a nested pattern), `Map.Tree.lookupList`,
`Map.Spec.lastBelow`, `Map.lookupWithOnto` (a catch-all alternative), `Text.readDigits`,
`Map.Tree.buildFuel`, `Parse.Each`, `Parse.Scattered` (a call whose argument is a lambda's
variable), `Key.allWithin` (a case without an equation); and 59 recursive definitions whose
equations aren't made (14 performing abilities; 45 whose arms can't be compiled again from the
listing scope, `Map.Tree.*`, `Vec.*`, `Ring.*`, …, which a program importing the type gets).
AoC (eager): **99 made**, none refused; skipped 20: 7 a call whose argument is a lambda's
variable (2024 days 7, 10, 21), 5 a recursive call inside a lifted `match` not in tail position
(2021 day 12, 2024 day 7, 2025 day 7), 3 a lifted `match` with a catch-all or nested pattern
(2021 day 16's `badOperatorIn`, 2024 day 17's `Machine.run`, day 23's `largestFrom` with `Some
(candidate, others)`), 4 a case without an equation (2021 day 16's `readPackets` and
`transmissionBits`, day 18's `sumMagnitudes`, 2024 day 24's `repair`), 1 performing abilities
(2021 day 18's `number`). The 7 AoC definitions with overlap hypotheses (2021 days 3, 14, 16,
18) are among those made. (2021 day 18's `explode` as first written would be skipped too, its
`eq3` cases having no equations, 1d's limit; AoC keeps the reshaped one.)

**A real theorem by it.** §6.1's `fillCorrect`, proved again by the generated
`Garden.fill.induct` with its statement unchanged
([prototypes/day12-fill-induct.sw](function-equations/prototypes/day12-fill-induct.sw), run in a
copy of the AoC project): 47 lines, against `fillCorrect`'s 67 (on 1d's equations), with no
decrease proof, no `rewrite` with an equation, and no `match taken:` on a `Bool`; `check
--no-cache Aoc.Year2024.Day12.Proofs` in 3.6 to 4.7 s user (before and after rebasing on 1d). It isn't in AoC itself, where it would be a
second proof of the same statement. `examples/accept/function-induct.sw` proves five smaller
theorems with five kinds of `f.induct` (a fixed prefix and `if`, `decreasing`, a named `match`, a
`match` on an expression, an overlap with two calls).

**Cost** **[measured, one run each, `/usr/bin/time -l`, main at `bf6619de` against the lane]**:
`check --no-cache` of the AoC project (207 namespaces) 656.8 G → 658.2 G instructions (+0.22%),
55.2 → 53.5 s user, peak 1,572 → 1,575 MB; `search List.length --no-cache` (every library file
and every put-off equation and `f.induct` made) 76.5 G → 77.3 G instructions (+0.99%), 6.74 →
6.37 s user, peak 226 → 232 MB (+2.9%). Within §7.1's 10% gate; the times are within noise. A
program that names no library equation pays nothing for std's.

**Where the code differed from this note.**

1. **Case binder order** follows the equations (above), not §5.1's example.
2. **Calls under a binder** that doesn't reach their arguments get an `ih` (above).
3. **`gcd.induct` isn't generated**: its `else` equation isn't (1b's D2180 limit, its `a % b`
   uses the refutation), so neither is the case. A generator could split on the decision itself
   (`d = No r` makes the right side compute), but that is a case equation of its own.
4. **Not covered in 2a**: an overlap hypothesis that a number or character arm makes; a lifted
   `match` with a catch-all or literals, or a nested pattern whose inner constructor's type has
   several constructors (a nested pattern over one-constructor types, `Some (MkPair v next)`, is
   split again by the inner type's `%splitN` and the alternative's equation rebuilt by `J`,
   SW-1073); a `match` compiled
   into a helper's tree below an alternative. Each is recorded.

## As built (stage 2b)

SW-1058, 2 November 2026: `match induct (f args) with | eqK b… => body`, D2182 as decided. The
code is `crates/elab/src/induct_match.rs`; the parser (`Expr::Induct`, `InductAlt`), the
formatter (token-based, so no change: a golden pair covers it) and the navigation walks
(`nav.rs`, `module.rs`, `autobind.rs`, `numbers.rs`) know it as they know `match reify`.
Syntax and errors are in `docs/syntax.md` ("`match induct`"); the examples are
`examples/accept/match-induct.sw` (six theorems, three of them re-proved from
`function-induct.sw`: `countAboveLe`, `halvingsGe`, `exAtMostTotal`; `firstBigIsBig` with a
generalised hypothesis), `examples/goals/match-induct.sw` and `examples/reject/match-induct-*.sw`.

**How.** It is elaborated to the application the proposal said, not a new proof form:

- **The call** `f a₁…aₙ` is elaborated as written, for the occurrence test (its normal form, as
  `match` on an expression reads its scrutinee). `f.induct` is looked up by name; its explicit
  parameters before `motive` are the fixed prefix, taken from the call's first arguments (any
  terms); the rest, as many as the motive has parameters but the last, must be distinct
  variables of the context.
- **The motive** is built in a context extended by the motive's own parameters: the targets map
  onto them, the call onto the result parameter; the variables in scope whose types mention the
  call or a target, then those whose types mention a variable already taken (`matching.rs`'s
  rule, unrefined variables and `let`s), are rebound after them with the replaced types and
  become `Π` premises of the motive's body, the goal with the same replacements. The
  alternatives are then checked against `f.induct`'s case types with that motive: the case's
  own binders by position, then those premises introduced automatically under the original
  names (`Ctx::rebind`, as a generalised `match`'s copies are), so the arm sees them refined
  and an `ih` takes them as arguments. The result is applied to the targets and to the original
  variables, and its type must unify with the goal, else `E-MATCH-MOTIVE`.
- **No lifting.** Unlike a generalised `match` this builds no helper definition: the arms are
  lambdas inside the proof term.

**Decisions made in the build** (what §5.3 left open):

1. **Binding syntax is positional**: `| eq2IfTrue x xs h ih => …` names the case's variables,
   then its hypotheses, then its induction hypotheses, in `f.induct`'s order, all of them, `_`
   to ignore. Not named fields (`{x, ih}`): the names are already in `f.induct`'s type, and an
   arm that ignores a field is `_`, so there is nothing to select. A count mismatch is
   `E-INDUCT-CASE` listing the names the case binds.
2. **The generalised hypotheses are not bound by the arm**: they stay in scope under their own
   names, refined. Binding them positionally would make every arm repeat them, and a theorem
   with a `state` hypothesis would need it named in every alternative.
3. **A goal that is an implication isn't introduced by the names.** `| eq1 => none => cases`
   (a lambda body), since the arity check would otherwise depend on the goal's shape. Stating
   the premise as a hypothesis in scope (`(found: …)`) is the idiom and gets it generalised
   and refined.
4. **New codes, not reused ones**: `E-INDUCT-CASE` (unknown or duplicate case name, wrong count of
   names), `E-NO-INDUCT` (no `f.induct`; carries the `E-NO-EQUATION` reason as a note, or the
   not-recursive note). A missing case is `E-NONEXHAUSTIVE`, as §5.3 said.
5. **`E-MATCH-MOTIVE`** for a goal that isn't a proposition, a target that isn't a variable,
   and a motive that doesn't give the goal back. The last is the check after the fact: the
   goal mentions the call or a target where abstracting it isn't type-correct (§1.2's case).
   No reject example exists for it, as no small program was found that reaches it: a goal that
   mentions a target in a type is generalised, which is the usual way out. An inferred
   `match induct` (no expected type) is also `E-MATCH-MOTIVE`: there is no goal to abstract.
6. **The call is `f` by name** (qualified or not), with its explicit arguments written out; no
   method call, named argument, or computed head. `f.induct` must exist, which a definition
   without it (not recursive, skipped, mutual) can't use.
7. **Nothing warns when the goal mentions neither the call nor a target**: the motive is then
   constant and the arms prove the goal in each case, which is sound and sometimes wanted.
   (`match` warns with `W-MATCH-NOT-FOUND` only for a named equation.)

**Limits.** Dot notation for the call (`garden.fill …`) isn't read; a target that a case split
has already refined is refused; an arm's error is reported without the "in alternative"
context frame `match` adds.

## Sources

- [L1] Lean 4, `src/Lean/Meta/Match/MatchEqs.lean`, `getEquationsForImpl` (overlap hypotheses),
  lines 141-222 at `95d7b99d`:
  <https://github.com/leanprover/lean4/blob/95d7b99d100bc5a1ba635db8cff0a6d5861357e8/src/Lean/Meta/Match/MatchEqs.lean#L183-L201>
- [L2] Lean 4, `src/Lean/Meta/Eqns.lean` ("We generate equations theorems on demand", reserved
  names `f.eq_<idx>`, `f.eq_def`), lines 96-120, 319-321:
  <https://github.com/leanprover/lean4/blob/95d7b99d100bc5a1ba635db8cff0a6d5861357e8/src/Lean/Meta/Eqns.lean#L113-L120>
- [L3] Lean 4, `src/Init/Tactics.lean` (`rw` uses equational theorems, `:609-612`; `unfold`,
  `:873-876`; `fun_induction`/`fun_cases`, `:1094-1121`):
  <https://github.com/leanprover/lean4/blob/95d7b99d100bc5a1ba635db8cff0a6d5861357e8/src/Init/Tactics.lean#L1094-L1121>
- [L4] Lean 4, `src/Lean/Meta/Tactic/FunInd.lean`, module documentation (lines 48-104):
  <https://github.com/leanprover/lean4/blob/95d7b99d100bc5a1ba635db8cff0a6d5861357e8/src/Lean/Meta/Tactic/FunInd.lean#L48-L59>
- [L5] Lean release notes: v4.8.0 (`.eq_<idx>`, functional induction),
  <https://lean-lang.org/doc/reference/latest/releases/v4.8.0/>; v4.18.0 (`fun_induction`,
  `fun_cases`), <https://lean-lang.org/doc/reference/latest/releases/v4.18.0/>; v4.20.0
  (`induct_unfolding`), <https://lean-lang.org/doc/reference/4.35.0/releases/v4.20.0/>
- Lean runs: Lean 4.34.1 from the nix store, scratch files `T.lean`, `T2.lean`, `T4.lean`
  (`#check @f.eq_2`, `@cmd.eq_3`, `@h.eq_2`, `@halvings.induct`, `@w.induct`, …).
- [E1] Rocq Equations reference manual, `doc/manual.tex` lines 90-120, 356-381:
  <https://github.com/mattam82/Coq-Equations/blob/main/doc/manual.tex>; `Function` and
  `functional induction`: <https://rocq-prover.org/doc/master/refman/using/libraries/funind.html>
- [I1] A. Krauss, *Defining Recursive Functions in Isabelle/HOL* (sequential mode, `sep.simps`,
  `And.induct`, `findzero.pinduct`): <https://isabelle.in.tum.de/doc/functions.pdf>; source
  <https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/Doc/Functions/Functions.thy>
- [A1] Agda manual, "Function definitions" (case trees, `--exact-split`, `CATCHALL`):
  <https://agda.readthedocs.io/en/latest/language/function-definitions.html>; "With-abstraction":
  <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- Idris 2: `src/Core/Case/CaseTree.idr`,
  <https://github.com/idris-lang/Idris2/blob/main/src/Core/Case/CaseTree.idr>; views and `with`,
  <https://idris2.readthedocs.io/en/latest/tutorial/views.html>. No equation lemmas or functional
  induction found **[unconfirmed: absence of evidence]**.
- [F1] *Proof-Oriented Programming in F\**, "Understanding how F\* uses Z3":
  <https://fstar-lang.org/tutorial/book/under_the_hood/uth_smt.html>
- [D1] Dafny reference manual, attributes `{:fuel}`, `{:induction}`:
  <https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Attributes.md>
- Prototypes, in [function-equations/prototypes/](function-equations/prototypes/), each checked
  with `stitchwort check FILE` from that folder: `p1.sw` (overlap, literals), `p2.sw` (the wall,
  §1.2; fails as intended), `p2b.sw` (the `J` proof), `p3.sw` (`∉` hypotheses; its last two
  theorems fail as intended), `p4.sw` (`gcd`'s branch equations and `gcdInduct`), `p6.sw` (the
  wall on a `decreasing` definition; fails as intended), `p6b.sw` (the `J` after `f.unfold`),
  `p7.sw` (day 18's `explode`), `p8.sw` (an effect-polymorphic arm at the empty row), `p9.sw`
  (`rewrite` with an overlap equation, and with a transparent arm, which fails as intended),
  `p10.sw` (D2186's normalised `else`), `day12-induct.sw` (day 12, run inside a copy of the AoC
  project), the reviewer's `review-r1.sw` (an indexed overlap, ill-typed as intended) and
  `review-r2.sw` (the `uniqueEq` `J` of §3.5); `gen_cost.py` and `count.py` (§7).

## Review 1 and how it was addressed

Review 1 ([function-equations/review-1.md](function-equations/review-1.md)) was by an
independent Claude Opus subagent given the note and the repository, of draft 1 (`c4e0f228`).
Verdict: "approve with changes". Each finding, and what changed:

| # | Finding | Severity | How it was addressed |
|---|---|---|---|
| 1 | Overlap hypotheses are ill-typed on indexed families when an earlier arm fixes an index (`review-r1.sw`) | major | Re-ran `review-r1.sw`: `E-TYPE-MISMATCH`, as stated. §3.2 now says so; such arms are skipped in stage 1 and counted; new **D2185** (skip now; a generated `Bool` predicate as the likely next step) |
| 2 | `Bool`-guard hypotheses don't match the hand-written form (`Not (b = False)` vs `b = True`); §6.1 overclaimed "no conversion"; `fillOther` is more general than the generated equation; D2184 treats deleting std lemmas as a rename | major | Adopted the reviewer's fix as **D2186** (the `else` of `b = True`/`False` states the other equation; `p10.sw` checks it); the day 12 prototype now uses it, with the conversion inside `fillInduct`'s generated proof (re-checked, `day12-induct.sw`). §6.1 says what the user's proof no longer does and that `fillOther` is more general. **D2184** now asks to delete the three std lemmas (not keep corollaries) and says why |
| 3 | §3.5/D2180's "rare, none in the evidence" is wrong: std has several `if h:` branches that use `h`; all are `Bool` equations underneath, provable by `J` along `Bool.uniqueEq` (`review-r2.sw`) | minor | Re-ran `review-r2.sw` (checks) and listed the std cases (`Fin.sw:53, 81`, `Safe.sw:20, 24, 58`, `Mod.sw:36, 173`). §3.5 now has the wider rule (an equation in a `DecEq` type, `<`/`≤` on `Nat`/`Int` included) and that the generator builds the `J` (`rewrite` gave `E-UNIVERSE`); **D2180** rewritten, with corrected assumptions |
| 4 | Missed constructs: or-patterns; helpers inside `decreasing` definitions take `%rec`; implicit and `auto` parameters; names for `_`; character merging across columns; `opaque` definitions past `MAX_NUMBER_SPLIT` = 64 (not "about 100"); records | major | §3.1: or-patterns get `f.eqK.orN`; equations take the definition's implicit and `auto` parameters; `_` is named after its field (or `x1`, …); record patterns. §3.2: characters merge only when the earlier arms constrain that column alone, else Lean's form; a `decreasing` definition's helpers get no equations (the owner's branches cover their tail cases). §4: `opaque` equations are checked with `unfolding f`, not via `f.unfold`, so the 64 limit doesn't apply; "about 100" corrected to 64 (`opaque.rs:298-300`) |
| 5 | Names "from source alone" conflict with skips decided after elaboration | minor | §3.2 and §3.3: the index lists every name the source implies (as `candidate`s, `library.rs:684`); naming a skipped one is `E-NO-EQUATION` with the reason, after `E-NO-UNFOLD-EQUATION` (`opaque.rs:544-546`); in D2176 |
| 6 | Naming asymmetry between arms and a whole-body `match`; local `def eq`/`def induct` | minor | New **D2187**: a whole-body `match` on parameters counts as arms, so `Garden.fill` is `Garden.fill.eq1`, `.eq2.ifFalse`, … throughout; local definitions named `eq`, `eqK`, `induct` are refused (none exist, checked) |
| 7 | The cost argument rests on tiny bodies; "one more check of every body" is inferred | minor | Measured one data point at `Garden.fill`'s size: about 1 ms an equation, noisy (§7.1); the range for std (0.2 to 2.5 s) and the 10% gate stated, the inference labelled as such; stage 1a measures before merging (§9) |
| 8 | "Five reshaped programs" stretched; category K is mostly the roguelike's | minor | Now "four programs (days 12, 16, 18, 23), all of which this design makes unnecessary"; the roguelike row says it was already fixed by SW-533; the K count is described as what it is (§1.1) |
| 9 | Prototype claims didn't reproduce from the files (`p6.sw` lacked the failing attempts; `p3.sw` gave `E-CASES` where the note said `E-OMEGA`) | minor | All prototypes are committed in `function-equations/prototypes/`, formatted. `p6.sw` has the three attempts again; §1.2 says `cases` gives `E-MATCH-MOTIVE` there (not `E-CASES`). `p3.sw` has both: `omega` gives `E-OMEGA` with the model `n = 10`, `cases` gives `E-CASES`; §3.2 says both |
| 10 | Citation drift and nits: `syntax.md:58` → `:61`; `derive_induct.rs:37-39` → `:40-41`; update lemmas are generated as source (`update_lemmas.rs:23`); `explodeUnfold`'s hypothesis is weaker than `notArm2`; `found` reads badly on `= None` | nit | Citations fixed. §1.3 says update lemmas are elaborated source, so a model for when and how they're found, not for how they're built. §6.2 says `explode.eq3` is less general than `explodeUnfold` and why nothing breaks (all six uses are at shapes where `cases` proves `notArm2`). Unnamed `match` hypotheses are now `isSome`, `isNone`, … |

The reviewer's "checked and correct" list (citations, the prototypes, the soundness argument, the
Lean quotes) needed no change. The day 12 prototype took 3.8 s here and 4.8 s for the reviewer;
§6.1 now gives the range.
