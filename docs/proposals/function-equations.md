# Proposal: equations for each arm, and functional induction (`f.eq…`, `f.induct`)

**Status:** draft 1, 1 November 2026. Ticket SW-1028, decision D2163 (Matt, 1 November: one
design for SW-802, SW-199's `f.induct`, SW-809 and SW-980). A design note only: nothing in the
compiler changes. The questions are D2173 to D2184 in [§8](#8-decisions-for-matt).

It revisits D231 ("generated per-leaf equation lemmas: not now",
[equation-lemmas.md §9](equation-lemmas.md#9-decisions)), whose trigger has fired (§1.3), and
takes up T4/D2001 of [research/proof-automation.md](../research/proof-automation.md) ("generated
case theorems, then `f.induct`").

Labels:

- **[checked: file:line]**: read in this repo at `470ef5ee` (main, 1 November);
- **[run]**: a scratch program checked with `target/release/stitchwort` built from main on
  1 November. The programs are quoted where they are used; they are not committed;
- **[measured]**: counted or timed by a script, named where used;
- **[cited]**: read in the source linked in [Sources](#sources) on 1 November; Lean outputs
  marked **[run: Lean]** come from Lean 4.34.1 on this machine;
- **[inferred]**: my reasoning, not tested;
- **[unconfirmed]**: believed, not checked.

## The short answer

- **What's missing.** A proof about a function can use `rfl` (when the arguments are known
  enough to compute) or `f.unfold` (the whole body, for `decreasing` and `opaque` definitions).
  Nothing states "this arm, or this branch of an `if` or `match` in it, gives this result when
  these conditions hold". Agents have reshaped five programs to get such statements (§1.1), and
  in three cases (a named `match` on a `Bool` or `popMin`) every way of stepping through the
  definition by hand fails; I reproduced it (§1.2, **[run]**).
- **Stage 1: equations.** For each definition with arms or with an `if`/`match` in tail
  position, generate one theorem per **arm** (`explode.eq3`) and one per **branch** below it
  (`Garden.fill.eq.cons.ifFalse`, `explode.eq3.some`). The arm's left side is the arm's patterns;
  earlier arms that overlap it become hypotheses, in Lean's form (`(a: Nat) → (b: Nat) → left =
  Regular a → right = Regular b → Void`, `n ≠ 3`, `char ∉ ['k', 'j']`); a branch adds the
  condition it was taken under (`fresh: visited.contains position = False`, `found: split left =
  Some left2`). Every one is an ordinary theorem, built as a kernel term and checked by the
  kernel; nothing new is trusted (§4).
- **Stage 2: `f.induct`.** For each recursive definition, one induction principle with one case
  per branch, the branch's conditions as hypotheses and one induction hypothesis per recursive
  call, in Lean's "unfolding" form (the motive also gets `f`'s result, so no case needs to
  rewrite with an equation). Proved by the same recursion as `f` (structural, or the same
  `decreasing` measure with the same decrease proofs). Applied as `match induct (f x y) with |
  eq1 … => … | eq2IfTrue … ih => …`, with the motive worked out from the goal as `match`
  already does (§5).
- **Evidence it pays.** On 2024 day 12 the hand-written step lemmas (21 lines) go, and
  `fillCorrect` (67 lines) becomes 51 lines with no decrease proofs or `Bool`-to-`Prop`
  conversions: the prototype checks **[run]** (§6.1). On 2021 day 18, `explode` keeps the shape
  it was first written in, with no `explodeIn` helper and no 0.98 s → 1.1 s run-time cost
  (§6.2, **[run]**).
- **Cost.** A small generated equation checks in about 0.08 ms [measured]; std has about 1,250
  arms in 497 definitions [measured], so on the order of 2,000 equations and well under a second
  of cold check time, nothing warm (the check cache). Generated eagerly, with the definition, as
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
- [Sources](#sources)

## 1. The problem

### 1.1 What agents ran into

| Where | What happened | What it cost |
|---|---|---|
| 2021 day 18 (`aoc/NOTES-2021.md:4546-4560`, ranked 2nd at `:4644`; SW-980 item 3) | `explode`'s general arm `Pair left right` comes after `Pair (Regular a) (Regular b)`, so it doesn't hold as written for every pair. Writing its body again in a proof made a second hidden `match` function, not equal to the program's (`E-REFL`) | The program was reshaped around a helper `explodeIn` (`aoc/src/Aoc/Year2021/Day18/Day18.sw:57-70`), which walks the right part even when the left exploded (run time 0.98 s → 1.1 s), plus a hand-proved `explodeUnfold` (`Proofs/Explode.sw:19-29`) used 6 times |
| 2024 day 12 (`aoc/NOTES-2024.md:3517-3535`, ranked 1st at `:3627`) | `match taken: visited.contains position with` in a `decreasing` definition, its equation used in a decrease proof. `rewrite …, taken` gave `E-REWRITE-MOTIVE`, `match c: …` gave `E-MATCH-MOTIVE` | Program rewritten with `if fresh: … = False`; three step lemmas by hand (`aoc/src/Aoc/Year2024/Day12/Proofs/Fill.sw:98-118`) |
| 2024 day 16 (`aoc/NOTES-2024.md:5017-5034`, ranked 3rd at `:5185`) | `match popped: queue.min with`, the same wall | `Graph.searchFrom` takes the popped pair and its equation as extra arguments (`crates/elab/src/std/Graph/Search.sw:243-260`); three step lemmas `Graph.searchEmpty/Skip/Settle` (`:267-290`) |
| 2024 day 23 (`aoc/NOTES-2024.md:7573-7592`, SW-809) | `match found: candidates.popMin with`: `rewrite` gives `E-REWRITE-MOTIVE`, `match` gives `E-MATCH-MOTIVE` | Rewritten with a guard `if fewer: …` and a dead `else`; a step lemma `largestStep` by hand (`aoc/src/Aoc/Year2024/Day23/Proofs/Search.sw:23-34`) |
| D1439 / SW-802 | "A recursive function matching on a `Bool` or `queue.min` and keeping the equation can't be unfolded in proofs; days 12 and 16 got E-MATCH-MOTIVE" | the ticket |
| roguelike (`games/rogue/PROOFS.md:192`) | A literal match's catch-all couldn't be reached at all, so the game looked keys up in a table | Fixed in the kernel by SW-533 ([literal-match-facts.md](literal-match-facts.md)); a proof still needs "an arm per character" (`PROOFS.md:228`) |

[research/agentic-proving.md](../research/agentic-proving.md) counts this as category F,
"stepping through `match`/unfolding equations; hand-written case tables", 9 cases, and category
K, "program reshaped for the proof", 5 (`:835`, `:840`) **[checked]**.

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
1) [decreasing := omega]`, after `rewrite down.unfold n`) fail the same way **[run]**. So
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
- **Update lemmas** `T.f.update.g`, generated with the type, checked like hand-written theorems,
  shown by hover, names that can't be declared by hand (`docs/syntax.md:394`,
  `crates/elab/src/update_lemmas.rs:1-30`), and indexed so the library loads their file when one
  is named (`crates/elab/src/library.rs:664-686`) **[checked]**. The model for when and how these
  are generated and found.
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

Each arm gets an **arm equation**. Each path below it through at least one split gets a
**branch equation**. A definition with neither arms nor a split gets nothing (it unfolds at
once, or has `f.unfold`).

Every equation is: the header's parameters, the arm's pattern variables in written order (the
order local definitions already use, `docs/syntax.md:289`), then the hypotheses, each split's
after the variables its pattern binds;

```
f.eqK… (params) (pattern variables) (hypotheses): f params patterns = right side
```

where the right side is the arm's body (for an arm equation) or the branch's (for a branch
equation), as elaborated, with `let`s substituted (as goals show them, and as the `Abort` step
lemmas already do, `docs/syntax.md:795`).

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

**Literal patterns.** A literal is a pattern like any other, so an earlier arm `3` against a
later `n` gives `n = 3 → Void`, written **`n ≠ 3`** (the same proposition), which `omega` proves:
`kindEq3 n omega omega` from `10 ≤ n` checks **[run: p1.sw]**. For **characters**, the earlier
arms' literals on one variable are merged into one hypothesis **`char ∉ ['k', 'j']`**, so a
program's own key list (`char ∉ commandKeys`, which computes to the same) is passed as it is,
and a known character is decided by `byDecision` **[run: p3.sw]**:

```
kind.eq3 (n: Nat) (notArm1: n ≠ 3) (notArm2: n ≠ 7): kind n = 0
commandOf.eq1.alt3 (char: Char) (notListed: char ∉ ['k', 'j']): commandOf char = None
```

(Numbers stay one `≠` each: `omega` can't use `n ∉ [3, 7]`, `E-OMEGA` with the model `n = 10`
**[run: p3.sw]**.) Stitchwort has no `Text` literal patterns (`crates/syntax/src/ast.rs:704-745`),
so there is nothing to generate for them.

**Nested patterns** need nothing new: `explode.eq2`'s left side is `explode depth (Pair (Regular
a) (Regular b))`, and `notArm2` above quantifies arm 2's nested variables.

**`if` in tail position.** A `Bool` `if c` gives `c = True` / `c = False`; a decided `if p`
gives `p` / `Not p`; `if h: p` gives `h: p` / `h: Not p`, named as written. Suffixes `.ifTrue`
and `.ifFalse`. `gcd` (`examples/accept/decreasing.sw:45-48`):

```
gcd.eq.ifTrue (a: Nat) (b: Nat) (h: b = 0): gcd a b = a
gcd.eq.ifFalse (a: Nat) (b: Nat) (h: Not (b = 0)): gcd a b = gcd b (a % b)
```

Both check, by `rewrite gcd.unfold a b in cases` **[run: p4.sw]**.

**`match` in tail position.** Each alternative is a branch. Its suffix is the constructor's name
in lower case (`.some`, `.none`, `.cons`, `.true`), as `T.induct`'s cases are named
(`docs/syntax.md:198`), when the alternative is one constructor applied to variables or `_`;
otherwise `.alt1`, `.alt2`, … in written order (literals, nested patterns, several scrutinees, a
catch-all). On a **variable** of the arm (compiled into the case tree), the alternative's pattern
goes into the left side, like an arm's. On an **expression**, the hypothesis is `e = pattern`,
named after the `match`'s equation name if it has one (`match found: …`), else `found`; earlier
overlapping alternatives add `notAlt…` hypotheses as arms do:

```
explode.eq3.some (depth) (left) (right) (inLeft: Explosion) (notArm2: …) (found: explode (depth + 1) left = Some inLeft):
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
§10 bounds the size.

**Mutual groups.** Each member gets its equations once the group is final; a call of another
member is just a call.

**Local definitions** are definitions: `reach.left` gets `reach.left.eq1`, `reach.left.eq2`.

**Not generated** (each listed by `stitchwort doc` with the reason, D2177):

- theorems (nothing unfolds them, `docs/core.md:234`, and nobody rewrites with a proof's arms);
- instances and interface methods: an instance is a record, folded by name until taken apart
  (`docs/core.md:233`); a method written with arms is better as a named `def` the instance points
  to, which gets equations;
- definitions that perform abilities (`{Fail}`, `{State s}`): their arms are computations, whose
  type has no spelling in a statement (`docs/syntax.md:871`, the same reason `match h: reify t`
  is refused); `match reify` is the tool there. **Effect-polymorphic** ones (`List.filter: … {e}
  List a`) get their equations at the empty row, as the hand-written std lemmas about them are
  stated (`List.filterFilter` with a pure `p`) [inferred; stage 1 checks that the arm computes
  there, and skips the definition if not];
- `Partial` definitions: `Effect.pfix` has no computation rule (`docs/core.md:349-362`: "no computation rules");
- an `opaque` definition with an `unfolding` clause: it has no `f.unfold` either
  (`docs/syntax.md:1100-1104`);
- an arm the case tree never reaches; an indexed family's impossible branches.

### 3.3 Names

| Case | Name |
|---|---|
| arm K (1-based, written order) | `f.eqK` |
| a branch below it | `f.eqK` + one suffix per split: `.ifTrue`, `.ifFalse`, `.some`, `.none`, `.true`, `.alt3`, … |
| a branch of a `:=` body | `f.eq` + the suffixes: `gcd.eq.ifFalse`, `Garden.fill.eq.cons.ifTrue.ifFalse` |
| hypotheses | the source's names (`fresh`, `found`); `notArmJ` for an earlier arm J, `notAltJ` for an earlier alternative, `notListed` for merged characters; `h1`, `h2`, … for an unnamed `if` |

- Names are worked out from the **source alone** (arm count, tail `if`s and `match`es,
  constructor names), so the library index can list them before the file is elaborated, as it
  does `T.f.update.g` (`library.rs:664-686`), and naming one loads its file.
- They are **reserved**: declaring `theorem f.eq2` is `E-DUPLICATE` with a note, as written
  update lemmas are refused (`docs/syntax.md:394`). Nothing in std or AoC has such a name today
  (`git grep` for `\.eq[0-9]` and `.induct` declarations: none) **[checked]**.
- **Why paths and not Lean's flat numbers** (D2176): `rewrite Garden.fill.eq.cons.ifFalse` says
  which branch it is, a reviewer can check it against the source, and adding an `if` to one arm
  renames only that arm's branches. Arms keep numbers because overlapping arms have no other
  unique name.

### 3.4 How agents find them

- **`stitchwort doc f`** gets an **Equations** section, before Theorems: every generated
  equation with its statement and the line of the arm or branch it came from (at most 16, then a
  count and the `search` command). Generated equations are left out of the Theorems groups, whose
  `rewrite` group they would otherwise fill (`docs/syntax.md:58`). JSON: `equations`, each with
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
`A` gets the proof the decision found, `h'`; so the proof needs `A h' = A h`, which holds by
computation when `h` doesn't occur in the right side after unfolding (it is only in a
`[decreasing := …]`, which `f.unfold` drops: every AoC example, and `gcd` **[run: p4.sw]**), and
by `DecEq.uniqueEq` when `p` is an equation in a type with `DecEq`. Otherwise it isn't provable
without proof irrelevance (`docs/core.md:143`), and that branch gets no equation, with the reason
in `doc` (D2180). [proof-irrelevance.md](proof-irrelevance.md) stage 1 would lift this. A
`match` on a `Bool` with an equation name has no such limit: `J` transports the given `h` itself
(§1.2).

## 4. How each is proved

Every equation is a theorem built as a kernel term, as `T.induct` is (`derive_induct.rs:37-39`,
"made as kernel terms … their types need the fields' types, which source can't always name"),
because its statement may name `f.%matchN` and its proof `f.%step` or `f.%body`. The kernel
checks it like any declaration; a generator bug gives a refused declaration, never a false
theorem. Proofs, by kind:

1. **Arm, no overlap, transparent `f`:** `rfl`.
2. **Arm with overlap hypotheses:** the definition's own case tree, restricted to the arm's
   patterns: at a leaf of this arm, `rfl`; at a leaf of an earlier arm J, `Void.exfalso (notArmJ
   fields… rfl rfl)`; at a number case, the same literals with the hypotheses ruling them out and
   the default computing by the apart rule ([literal-match-facts.md](literal-match-facts.md)), not
   a `Zero`/`Succ` expansion (which `f.unfold` for `opaque` needs, and limits to literals below
   about 100, `opaque.rs:299`). `exEq3`, `kindEq3` and `commandOfEq3` are this proof written by
   hand; they check **[run: p1.sw, p3.sw]**.
3. **`decreasing` or `opaque` `f`:** `Eq.trans (f.unfold …)` and then the above on `f.%step` or
   `f.%body` (with `%rec` applied to `y … => f y …`, so recursive calls show as `f`).
4. **Branch:** the arm equation, then one step per split: for an `if`, `Bool.ifThenElse`'s case
   on the hypothesis; for `if h:`, `Decidable.elimEq` (`crates/elab/src/std/core/Decidable.sw:53`,
   the lemma the hand proofs use) and §3.5; for a `match` on an expression, `Eq.cong` of the helper
   along `found` (`p7.sw`'s equations do this by `rewrite found` and check **[run]**); for a
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
    (one case per branch, named after its equation: eq1, eq2IfTrue, eqConsIfFalse, …:
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
the prototype has it (`Induct.sw`, §6.1, **[run]**):

```
Garden.fill.induct (garden: Garden) (plant: Char) (motive: List Position → Set Position → List Position → Prop)
    (eqNil: (visited) → (members) → motive Nil visited members)
    (eqConsIfTrueIfTrue: (position) → (rest) → (visited) → (members) →
      (fresh: visited.contains position = False) → (grows: garden.plantAt position = Some plant) →
      motive (garden.neighboursGrowing plant position ++ rest) (visited.insert position) (Cons position members) →
      motive (Cons position rest) visited members)
    (eqConsIfTrueIfFalse: … (fresh: … = False) → (grows: Not (…)) → motive rest visited members → motive (Cons position rest) visited members)
    (eqConsIfFalse: … (fresh: Not (visited.contains position = False)) → motive rest visited members → motive (Cons position rest) visited members):
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
    | eqNil visited members => …                                   -- state: FillState … Nil visited members
    | eqConsIfTrueIfTrue position rest visited members fresh grows ih => …
    | eqConsIfTrueIfFalse position rest visited members fresh grows ih => …
    | eqConsIfFalse position rest visited members fresh ih => …
```

The motive is the goal with the call replaced by `result` and the targets by the motive's
parameters; variables in scope whose types mention a target (`state`) are generalised, as a
`match` on an expression already does (`matching.rs:10-19`), so each arm sees them refined and
each `ih` takes them as premises. Arms are named by case, in any order, all required
(`E-NONEXHAUSTIVE`). The proof it writes is `Garden.fill.induct` applied, and the kernel checks it.

## 6. Worked examples

### 6.1 2024 day 12: the flood fill

**Before.** `Garden.fill` (`Day12.sw:74-85`) is `decreasing (garden.unvisited visited,
stack.length)`, a `match stack` and two nested `if h:`s. The proof has three step lemmas by
`f.unfold` and `Decidable.elimEq` (`Fill.sw:98-118`, 21 lines) and `fillCorrect` (`:121-187`, 67
lines), which recurses on the same measure, re-proves the three decreases
(`Nat.LexLess.First (garden.unvisitedInsert …)`, `Nat.LexLess.Second rfl (omega)` twice), and
converts `garden.plantAt position == Some plant` back to a `Prop` (`DecEq.sound`, and a two-line
`other`) because it splits with `match taken:`/`match growing:` on `Bool`s.

**After stage 1.** The three step lemmas are `Garden.fill.eq.cons.ifFalse`,
`.eq.cons.ifTrue.ifTrue` and `.eq.cons.ifTrue.ifFalse`: delete `Fill.sw:98-118` and rename the
three uses (`:145`, `:164`, `:179`).

**After stage 2.** `fillCorrect` by `Garden.fill.induct`: the prototype
(`scratchpad/aoc/…/Day12/Proofs/Induct.sw`, a copy of the AoC project with `fillInduct` and the
four equations written by hand as the generator would make them) checks with `stitchwort check
--no-cache Aoc.Year2024.Day12.Proofs` in 3.8 s user **[run]**. `fillCorrectByInduct` is 51 lines
against 67, with no decrease proof and no `Bool`-to-`Prop` conversion; one case:

```
    (position rest visited members fresh grows ih state =>
      let (Both distinct (Both sound (Both closed (Both kept fromStack)))) := ih (takeKeeps garden plant start position rest visited members state fresh grows)
      rewrite fillEqConsIfTrueIfTrue garden plant position rest visited members fresh grows in
        Both distinct (…as before…))
```

With the unfolding form the `rewrite` line goes too (4 lines), and with `match induct` the
explicit motive (2 lines). In all, 88 lines become about 45.

Two small findings on the way: the `else` of `if fresh: b = False` gives `Not (b = False)`, and
std has `Bool.falseOfNotTrue` but not `Bool.trueOfNotFalse` (`crates/elab/src/std/Bool/Bool.sw:57`)
**[checked]**; and `cases`, given that hypothesis, derived `%fact1: Void` and still reported
`E-CASES` **[run]**. Both are backlog tickets, not part of this design.

### 6.2 2021 day 18: `explode` without the reshape

**Before.** `explode`'s general arm became `explodeIn left right (explode (depth + 1) left)
(explode (depth + 1) right)` (`Day18.sw:60`, `explodeIn` at `:66-70`), and `explodeUnfold`
(`Proofs/Explode.sw:19-29`) states it for every pair under a hypothesis `depth < 4 ∨ height left
+ height right ≠ 0`, used 6 times (`git grep`) **[checked]**.

**After stage 1.** `explode` as first written, with the `match`es in its last arm
(`p7.sw`, §3.2). Its generated equations:

```
explode.eq3.some      (…) (notArm2) (found: explode (depth + 1) left = Some inLeft): explode depth (Pair left right) = Some ({ toLeft = inLeft.toLeft, … })
explode.eq3.none.some (…) (notArm2) (found: explode (depth + 1) left = None) (found2: explode (depth + 1) right = Some inRight): … = Some ({ toLeft = 0, … })
explode.eq3.none.none (…) (notArm2) (found: … = None) (found2: … = None): explode depth (Pair left right) = None
```

all three proved as the generator would and checked, and used where the left part is a pair
with `cases` for `notArm2` **[run: p7.sw]**. `explodeInFound` (`Explode.sw:74`) then splits on
`explode (depth + 1) left` as it does now and rewrites with `explode.eq3.some` or
`.eq3.none.some` instead of `explodeUnfold` and `explodeIn`'s arms. The run time is back to
0.98 s (`aoc/NOTES-2021.md:4558-4560`, the author's measurement). I didn't rewrite the whole proof
file; that is stage 1's acceptance test (§9).

### 6.3 std's `Graph.searchFrom`

`Graph.searchEmpty`, `searchSkip` and `searchSettle` (`crates/elab/src/std/Graph/Search.sw:267-290`,
21 lines) become `Graph.searchFrom.eq1`, `.eq2.ifFalse` and `.eq2.ifTrue`. Its signature, which
takes `queue.popMin` and its equation as arguments because `match popped: queue.popMin with`
couldn't be stepped through (`aoc/NOTES-2024.md:5017-5030`), could go back to the `match`; that
changes a std signature and its callers, so it is D2184's question.

## 7. When, and what it costs

### 7.1 Eagerly, with the definition

Options: **(a) eager**, when the definition is final, as `f.unfold` and update lemmas are;
**(b) on demand**, when a name is first looked up, as Lean does; (c) statements eager, proofs on
demand, which would need the kernel to hold unchecked theorems: refused.

(a) is recommended (D2178), because:

- **Discovery needs them to exist.** `doc` and `search` read the elaborated library; on-demand
  lemmas wouldn't be listed unless those commands generated them, which is (a) again.
- **The cost is small.** A scratch file of 1,000 definitions of 5 arms each checks in 0.22 s;
  with one equation per arm written as source (5,000 theorems, one per definition with an
  overlap hypothesis and a case split) 0.62 s: about **0.08 ms an equation**, elaboration from
  source included, which generated kernel terms skip [measured: `scratchpad/gen_cost.py`, three
  runs, `check --no-cache`]. Equations about bigger bodies cost more, about as much as checking
  the arm again, so a bound: generating everything costs at most one more check of every
  definition body, and definitions are a minority of std's declarations (1,108 `def`s to 2,496
  theorems [measured: `scratchpad/count.py`]).
- **std's size.** 1,108 definitions, 497 with arms, 1,253 arms; 117 with an `if` and 69 with a
  `match` somewhere in their body; 11 `decreasing` [measured: `count.py`, which reads source with
  regular expressions, so the counts are close, not exact]. So about 1,250 arm equations and a few
  hundred branch equations.
- **The check cache** stores them in the file's entry and replays them (stage 3 admits them
  without checking again, `docs/proposals/check-cache.md` "As built (stage 3)"), so a warm run
  pays nothing.
- **The gate.** If stage 1 adds more than 10% to std's cold check, or to the playground's start,
  generation for the library switches to (b), behind the same names (the index already knows
  them, §3.3). Assumption, in full: that std's cold check is dominated by its theorems, not its
  definitions, as the counts above suggest; stage 1 measures it.

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
- **`rewrite`** with an arm equation of a transparent `f` whose left side is constructors finds
  the computed form in the goal and rewrites it to itself, a no-op (goals and rules are both
  searched computed, `docs/syntax.md:1748`). The useful ones are those whose left side is stuck:
  overlap hypotheses (`f x` with `x` a variable), `decreasing` and `opaque` definitions, and
  branches (stuck on the condition). `rewrite` takes the hypotheses as arguments, or leaves them
  as goals for `cases`/`omega` when written with `_`.
- **`match e:`** and **`cases`** keep working; the equations are what to use where they fail
  (§1.2).

## 8. Decisions for Matt

Each with my recommendation in [brackets] and its assumptions in full.

- **D2173. Build stage 1, generated equations for arms and branches?** [Yes.] Assumes the
  evidence of §1.1 (five reshaped programs, three hand step-lemma sets) is typical of what
  agents will meet, and that the per-equation cost measured in §7.1 holds for generated terms.
- **D2174. Granularity: an equation per source arm, with earlier overlapping arms as
  hypotheses (Lean), plus one per branch of each tail `if`/`match` (Lean's functional-induction
  granularity)?** [Yes.] The alternative is per leaf of the case tree (Isabelle, Rocq
  Equations): unconditional, but more and less general, and impossible for a character
  catch-all. Assumes agents think in arms and branches as written, which is how every note in
  §1.1 describes the problem.
- **D2175. Hypothesis forms: one per earlier overlapping arm, `(vars) → x = C vars → … → Void`;
  `n ≠ k` for a number literal; earlier character literals on one variable merged into
  `c ∉ ['k', 'j', …]`; the condition as tested for a split.** [Yes.] Assumes `omega` keeps not
  reading `n ∉ [3, 7]` (if it learns to, numbers could merge too) and that a program's key lists
  are written as literal lists or definitions that compute to them.
- **D2176. Names: `f.eqK` for arm K, a suffix per split (`.ifTrue`, `.ifFalse`, the constructor
  in lower case, `.altN`), `f.eq` + suffixes for a `:=` body; reserved.** [Yes.] The alternative
  is Lean's flat `f.eq1 … f.eqN` over all cases: shorter, but a name doesn't say which branch,
  and adding an `if` renumbers later arms. Assumes names a few segments long are acceptable in
  proofs (`Garden.fill.eq.cons.ifTrue.ifFalse` is the longest in §6).
- **D2177. Which definitions: every `def` (top-level or local) with arms or a tail split,
  transparent, `decreasing` or `opaque` without `unfolding`; effect-polymorphic ones at the empty
  row; not theorems, instances, ability-performing or `Partial` definitions.** [Yes, including
  the equations that hold by `rfl`.] Generating only the "useful" ones (stuck left sides) would
  save some hundreds of lemmas but make agents guess which functions have equations. Assumes the
  `rfl` ones are cheap (§7.1) and that `doc`'s separate section keeps them from crowding search.
- **D2178. Generate eagerly with the definition, with the 10% gate of §7.1; on demand (Lean)
  only if the gate trips.** [Yes.] Assumes std's cold check is dominated by theorems (§7.1).
- **D2179. Discovery: an Equations section in `doc`, a `generated` flag and a tie-break in
  `search`, notes on `E-MATCH-MOTIVE`/`E-REWRITE-MOTIVE`/`E-REFL` naming the equation, a section in
  the proving guide.** [Yes.]
- **D2180. A branch of `if h: p` whose right side still uses `h` gets an equation only when `h`
  is gone after unfolding or `p` has unique proofs (`DecEq`), until proof irrelevance lands.**
  [Yes.] Assumes such branches are rare in programs (none in the evidence: the proofs there go
  into `[decreasing := …]` only).
- **D2181. Stage 2, `f.induct` for recursive definitions: unfolding form only, a fixed prefix,
  cases named after the equations, no IH for calls under a binder, no mutual groups.** [Yes,
  after stage 1.] The alternatives: also the plain form (`f.inductPlain`; a statement not about
  `f` ignores one argument instead), or Lean's both. Assumes most theorems that need it are about
  `f`'s result, as `fillCorrect` is.
- **D2182. Stage 2b, `match induct (f args) with | eqK … => …`, the motive worked out from the
  goal and hypotheses generalised as a `match` on an expression does.** [Yes.] Assumes the
  generalisation `match` already does (`matching.rs:10-19`) is what the motive needs; if a goal
  mentions a target inside a proof (as §1.2's did), it can hit `E-MATCH-MOTIVE` like `match`, and
  the explicit `f.induct` stays the fallback.
- **D2183. Equations for lifted `match` helpers not in tail position (`reach.match1.eq2`)?**
  [No.] Their numbering is identity metadata, not a name (`syntax-conveniences.md` §2.4); a local
  `def` names one and then gets its own equations.
- **D2184. After stage 1, replace std's `Graph.searchEmpty/Skip/Settle` by the generated
  equations, and leave `Graph.searchFrom`'s signature and AoC's programs as they are (day 12 and
  day 18 as acceptance tests only)?** [Yes.] Changing `searchFrom` back to a `match` changes a
  std signature and every caller for no gain in what is proved.

## 9. Stages

| Stage | What | Size | Model |
|---|---|---|---|
| **1a** | `crates/elab/src/equations.rs`: arm equations for transparent, `decreasing` and `opaque` definitions; overlap and literal hypotheses (pattern unification against earlier arms); proofs by the case tree (§4, 1–3); the arm↔leaf map recorded by `check_tree` (`Tree::Leaf` has the arm's span, `crates/elab/src/lib.rs:802-813`, the core term doesn't); reserved names; library index | medium-large (in the order of `derive_induct.rs`, 2,560 lines, but simpler: no containers) | **Opus** (kernel terms, the overlap computation) |
| **1b** | Branch equations: tail `if`, `if h:` (§3.5), `match` on variables and expressions, named `match` (`J`), skipping helpers with copies | medium | **Opus** (dependent motives) |
| **1c** | `doc` Equations section, `search` flag and tie-break, hover, the three messages, `docs/syntax.md` and proving-guide sections | small-medium | **Sonnet** |
| **1d** | Acceptance: `examples/accept/function-equations*.sw` (every construct of §3.2, the prototypes `p1`–`p7`); 2021 day 18 back to `explode` as first written with its proofs on the equations; 2024 day 12's step lemmas deleted; std's `Graph.search*` replaced (D2184); `search_bench` and std cold check against §7's bounds | small-medium | **Sonnet** (proofs: Opus review) |
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
- **`rewrite` no-ops** on transparent arms (§7.3) may puzzle; the doc section says which
  equations have stuck left sides.
- **Not here:** Lean's `simp`-style automatic use of equations (Stitchwort has no simp set;
  `search --at` suggests them); equations for `Partial` or ability-performing definitions;
  closed, shared matchers (D233 stays "not now": equations make the inner `match` statable
  without them).

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
- Scratch programs (not committed), in the session scratchpad: `proto/p1.sw` (overlap, literals),
  `p2.sw` (the wall, §1.2), `p2b.sw` (the `J` proof), `p3.sw` (`∉` hypotheses), `p4.sw` (`gcd`
  branch equations and `gcdInduct`), `p6.sw`/`p6b.sw` (the wall on a `decreasing` definition, and
  the `J` after `f.unfold`), `p7.sw` (day 18's `explode`), `aoc/…/Day12/Proofs/Induct.sw` (day 12),
  `gen_cost.py` and `count.py` (§7).
