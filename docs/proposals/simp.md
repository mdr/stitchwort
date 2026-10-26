# Proposal: automatic case splitting (`split`), and where `simp` fits

**Status:** stage 1 built, 26 October 2026 (D1317 to D1319): `split` and `split in t`,
without the expand code action; see [§8.3](#83-stage-1-as-built). Ticket SW-592. The
scratch reproductions are described in [§1](#1-the-motivating-proofs) and listed under
[Sources](#sources). Six questions for Matt are in [§9](#9-decisions-for-matt). Related:
[proof-automation.md](proof-automation.md) (stages 0, 1, 1b and 2 built; its stage 3, `simp
[rules]`, was deferred until "a proof that needs it", D1168), [omega.md](omega.md) (built; its
facts are what close most leaves here), [variant-fields.md](variant-fields.md) (SW-581),
[proof-reification.md](proof-reification.md) (`Abort` lemmas, SW-587).

**The short answer.**

- **What the motivating proofs need is case splitting, not rewriting.** The helpers
  (`Float.ltLeBools` in std, about 70 lines of them in the ported program) exist to *split on
  Booleans* that a definition's `∧`/`∨`/`¬`/`if` chain tests. In Stitchwort those connectives
  are `if`s (`a ∧ b` is `if a then b else False`, `crates/elab/src/logic.rs:4-11`), so once
  each tested Boolean is `True` or `False`, the whole chain *computes*. No lemma set is needed
  for that: the evaluator does what Lean's `Bool.and_true`, `ite_true` and friends do.
- **Splitting by hand already works, when it splits on the right thing.** `match e:` on the
  innermost tested Booleans (`Float.isNaN x`, `Float.isZero x`, …) proves `Float.ieeeLtLe`
  with no helper, because generalisation compares *computed* forms (`matching.rs:682`) and
  so reaches inside folded calls **[run]**. What fails is splitting on a *compound* condition
  (`isZero a ∧ isZero b`) when another place has it in a different order (`isZero b ∧ isZero
  a`): that is the ported program's failure, reproduced in §1.2 **[run]**. The cost of the
  by-hand route is length (11 nested `match`es for one-line facts) and unreadable goals (14
  stale copies of `h` in one branch, everything unfolded) **[run]**.
- **Recommendation: a proof term `split`**, like `omega`. It finds what the goal (and any
  hypothesis that says "this is `True`" or "this is `Some v`") is stuck on, splits on it with
  the same generated `match` that `match e:` writes, and repeats, closing each case by
  computation, by a contradiction between hypotheses, or by `omega`. `split in t` tries `t`
  in each case the automatic closers leave. **Nothing new is trusted**: the proof is ordinary
  `match`es and the closers' own terms. On the scratch reproductions (§6), every motivating
  helper and every by-hand split tree becomes one word, `split` (or `split in lemma`), and
  the three other shapes the ported program hit (SW-587, SW-581, SW-568) are covered too.
- **`simp` (rewriting with a lemma set) stays deferred.** None of the motivating proofs needs
  it once `split` exists (§6). When one does, proof-automation.md §6.3's `simp [rules]` is
  still the design, and it composes with `split` as a term (`split in simp [..]`), rather
  than splitting on its own as Isabelle's does (§4.3, Q3).

Labels, as in the other notes:

- **[checked]**: read in the Stitchwort source or docs at the `file:line` given (at
  `941e394f`), or in a source listed at the end ([L1] and so on);
- **[run]**: run on 26 October 2026 with the release CLI built from `941e394f`, on the scratch
  files listed under [Sources](#sources); times are `STITCHWORT_TIMINGS=decls stitchwort check
  --no-cache`, one run (elaboration ms, kernel ms, evaluation steps);
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## Contents

- [1. The motivating proofs](#1-the-motivating-proofs)
- [2. Words this note uses](#2-words-this-note-uses)
- [3. How Stitchwort proves these today](#3-how-stitchwort-proves-these-today)
- [4. How other systems do it](#4-how-other-systems-do-it)
- [5. The proposal: `split`](#5-the-proposal-split)
- [6. The reproductions, before and after](#6-the-reproductions-before-and-after)
- [7. `simp`: what it would add, and when](#7-simp-what-it-would-add-and-when)
- [8. Staging, acceptance, risks](#8-staging-acceptance-risks)
- [9. Decisions for Matt](#9-decisions-for-matt)
- [Sources](#sources)

## 1. The motivating proofs

Each was reproduced in a scratch file (not committed; contents described here) and checked
with the release CLI **[run]**.

### 1.1 `Float.ltLeBools` (std)

`Float.ieeeLt` and `Float.ieeeLe` are `∧`/`∨`/`¬` chains (`std/Float/Float.sw:281-287`
**[checked]**):

```
def Float.ieeeLt (x: Float) (y: Float): Bool :=
  ¬(Float.isNaN x) ∧ ¬(Float.isNaN y) ∧ ¬(Float.isZero x ∧ Float.isZero y)
    ∧ Int.less (Float.orderKey x) (Float.orderKey y)
def Float.ieeeLe (x: Float) (y: Float): Bool :=
  ¬(Float.isNaN x) ∧ ¬(Float.isNaN y)
    ∧ ((Float.isZero x ∧ Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))
```

To prove `ieeeLt x y = True → ieeeLe x y = True`, std states the chain again over free
Booleans and lists the cases (`Float.sw:295-305`):

```
theorem Float.ltLeBools: (a: Bool) → (b: Bool) → (c: Bool) → (i: Int) → (j: Int)
    → (a ∧ b ∧ ¬c ∧ Int.less i j) = True → (a ∧ b ∧ (c ∨ Int.leq i j)) = True
  | True, True, False, i, j, h => Float.keyLessLeq i j h
  | True, True, True, i, j, h => rfl
  | True, False, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)
  | False, b, c, i, j, h => Void.exfalso (Bool.falseNotTrue h)

theorem Float.ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True :=
  Float.ltLeBools (¬(Float.isNaN x)) (¬(Float.isNaN y)) (Float.isZero x ∧ Float.isZero y)
    (Float.orderKey x) (Float.orderKey y) h
```

The new IEEE-order lemmas of `c16897c7` do the same thing inline: `ieeeLeRank` and
`ieeeLeNotNaN` take the chain apart with `Bool.andLeft`/`andRight`/`orElim`, restating each
remaining conjunction in full (the expression `¬(Float.isNaN y) ∧ ((Float.isZero x ∧
Float.isZero y) ∨ Int.leq (Float.orderKey x) (Float.orderKey y))` is written out three
times in those two proofs, `Float.sw:416`, `:444`, `:447`) **[checked]**.

**Splitting by hand works.** In scratch, nested `match e:` on the four tested Booleans, with
the lemma at two leaves, checks **[run]**:

```
theorem ieeeLtLeSplitIn (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True :=
  match nx: Float.isNaN x with
    | True => Void.exfalso (Bool.falseNotTrue h)
    | False =>
      match ny: Float.isNaN y with
        | True => Void.exfalso (Bool.falseNotTrue h)
        | False =>
          match zx: Float.isZero x with
            | True =>
              match zy: Float.isZero y with
                | True => rfl
                | False => Float.keyLessLeq _ _ h
            | False => Float.keyLessLeq _ _ h
```

It works because generalising `Float.isNaN x` compares computed forms, so it finds the
occurrence inside the folded `Float.ieeeLt x y` of `h`, and the branch's `h` computes to
`False = True`. Going two levels further, splitting also on the sign tests inside
`Float.orderKey` (`Nat.leq 9223372036854775808 x.bits`), every leaf is `rfl`, a `False =
True` hypothesis, or `omega`: no lemma at all (12 leaves, scratch `ieeeLtLeSplit`)
**[run]**.

**What it costs.** One branch's goal display, after four splits (abridged; full output in
the scratch log):

```
h✝: Float.ieeeLt x y = True
h✝: (if Bool.not (Nat.equal y.bits 9221120237041090560) then if Bool.not (if if Nat.equal x.bits 0 then …
nx: Float.isNaN x = False
h✝: (if Bool.not (Nat.equal x.bits 9221120237041090560) then …
… (14 copies of h in all, each fully unfolded)
h: Int.less (if Nat.leq 9223372036854775808 x.bits then NegSucc (x.bits - 9223372036854775808) else OfNat x.bits) (…) = True
zy: Float.isZero y = False
⊢ Int.leq (if Nat.leq 9223372036854775808 x.bits then NegSucc (…) else OfNat x.bits) (…) = True
```

Every split copies every hypothesis that mentions the scrutinee and keeps the old one
(`matching.rs:10-19`, "those variables get copies"), and the copies are shown computed, so
`Float.orderKey x` is gone from view. Times **[run]**:

| proof | elaboration + kernel ms | evaluation steps |
|---|---:|---:|
| `ltLeBools` + `ieeeLtLe` (today) | 0.2 + 0.1, 0.1 + 0.0 | 4,640 + 2,191 |
| split by hand, lemma at two leaves (`ieeeLtLeSplitIn`) | 3.7 + 0.7 | 86,913 |
| split by hand down to `omega` leaves (`ieeeLtLeSplit`) | 34.8 + 2.5 | 598,217 |

Most of the 35 ms is the eleven `match`es and what they generalise, not the six `omega`s:
the same tree with holes at the `omega` leaves still takes 24 ms, and that includes printing
six large goals **[run]**. §5.8 is about this.

### 1.2 The ported program: the order of a compound condition

The ported program (private) has about 70 lines of helpers of the `ltLeBools` kind, and its
author reported that a direct `match e:` fails because "after unfolding, the hypotheses stop
matching syntactically (`isZero b ∧ isZero a` against `isZero a ∧ isZero b`)". A public
reproduction **[run]**:

```
-- JS's `(a == 0 && b == 0) || a === b` on bit patterns.
def looseEq (a: Float) (b: Float): Bool := (Float.isZero a ∧ Float.isZero b) ∨ Nat.equal a.bits b.bits

theorem looseEqSymm (a: Float) (b: Float) (h: looseEq a b = True): looseEq b a = True := …
```

- **Today's style** is a helper over four free Booleans with four cases (`orSwapBools`, 6
  lines) plus a call that names all four (3 lines), plus `equalSymm` (2 lines).
- **`match z: Float.isZero a ∧ Float.isZero b`** (the compound condition, which is what the
  helper's free Booleans stand for) generalises it in `h` but not in the goal, whose unfolding
  has `isZero b ∧ isZero a`. Both branches are stuck:

  ```
  z: (if Float.isZero a then if Nat.equal b.bits 0 then True else … else False) = True
  ⊢ (if if if Nat.equal b.bits 0 then True else … then if Nat.equal a.bits 0 then … else False then True else Nat.equal b.bits a.bits) = True
  ```

- **`match` on the atoms** (`Float.isZero a`, then `Float.isZero b`) works: both sides compute,
  and the four leaves are `rfl` or `equalSymm a.bits b.bits h` (scratch `looseEqSymmAtoms`,
  9 lines). Splitting also on the goal's last stuck test, `Nat.equal b.bits a.bits`, every
  leaf is `rfl` or `omega` (which reads `Nat.equal … = True`/`False` facts, `docs/syntax.md`
  "Facts" **[checked]**), so no lemma at all (`looseEqSymmSplit`, 2.4 + 1.0 ms) **[run]**.

So the lesson for an automatic split is to split on the **innermost** tested Booleans, never
on a compound condition. A `∧` chain is then irrelevant: in any order, it computes once its
parts are known.

### 1.3 Three more shapes from the port

**SW-587, "this `.orAbort` chain returned `Some`".** Reproduction **[run]**:

```
def parseSmall (s: Text) (t: Text): {Abort} Nat :=
  let a := s.toNat.orAbort
  let b := t.toNat.orAbort
  ensure (a + b <= 10)
  a + b
def parseSmallOption (s: Text) (t: Text): Option Nat := toOption (() => parseSmall s t)

theorem parseSmallSome (s: Text) (t: Text) (v: Nat) (h: parseSmallOption s t = Some v): v <= 10 :=
  match es: s.toNat with
    | None => Void.exfalso (Option.noneNotSome v h)
    | Some a =>
      match et: t.toNat with
        | None => Void.exfalso (Option.noneNotSome v h)
        | Some b =>
          match ok: Nat.leq (a + b) 10 with
            | False => Void.exfalso (Option.noneNotSome v h)
            | True => rewrite <- Option.someInjective (a + b) v h in ok
```

One `match` per `.orAbort` and per `ensure`, each failing arm the same contradiction. The
splits are on `Option`s and a `Bool` that `h` (not the goal) is stuck on. The last leaf needs
`Some (a + b) = Some v` taken apart. 2.2 + 0.6 ms.

**SW-581, "update a field shared by every variant, then project another".** With `type Shape
= | Dot (ref: Nat) (id: Text) | Circle … | Square …`, `({ s | id = t }).ref = s.ref` is not
`rfl`: the goal is `(refAfterIdRfl.%match1 s t).ref = s.ref`, stuck on `s` **[run]**. The
proof is `match s with` and one `rfl` per variant (3 arms; the port's has 9).

**SW-568, record eta.** `p = { row = p.row, column = p.column }` is not `rfl` (no eta for
records in conversion). It is `Pos.ext p _ rfl rfl` today, or `match p with | { row = r,
column = c } => rfl` **[run]**.

All three are "split on what is stuck, then `rfl` or a contradiction" (§6.3 to §6.5). SW-568
is better fixed in conversion (that is the ticket); `split` would only be a workaround.

### 1.4 How common

Rough indicators across `aoc/src` and `crates/elab/src/std` (grep counts, **[run]**; not all
of them would go):

| | AoC | std |
|---|---:|---:|
| `match name: e with` (a split with an equation) | 86 | 214 |
| `\| True =>` / `\| False =>` arms | 150 | 272 |
| `Bool.falseNotTrue` / `trueNotFalse` (a contradiction leaf) | 42 | 158 |
| `Bool.andLeft` / `andRight` (taking an `∧` apart) | 26 | 44 |

Theorems whose statement starts with two or more free `Bool`s, the `ltLeBools` kind, are 13
in std (`Bool.orComm`, `orAssoc`, `xorAssoc`, `andIntro`, …, `Nat.keepIfKeepIf`,
`Float.ltLeBools`) and 4 in AoC (`andOr`, `andTrueLeft`, `toNatAnd`, `andKeep`) **[run]**. The
library's are the laws such helpers are built from; `split` would prove each of them, and,
more to the point, would make most uses of them unnecessary.

## 2. Words this note uses

- **Stuck.** A term that doesn't compute further because something it tests isn't known:
  `Bool.ifThenElse c …` with `c` a variable or a call that is itself stuck. Evaluation
  stops at the test.
- **Blocker.** The thing a stuck term is waiting for: in `Float.isNaN x ∧ …` it is `Float.isNaN
  x`, in `match s.toNat with …` it is `s.toNat`. Following blockers inwards gives a chain; the
  innermost one that is worth splitting on is the **atom** (§5.2).
- **Split.** Case analysis on an atom with a `match` that names an equation (`match e: atom
  with | True => … | False => …`), so that in each branch the atom is a constructor and the
  stuck term computes one step further.
- **Leaf.** A branch with nothing left to split, or that a closer proves.
- **Closer.** Something tried on each branch to finish it: `rfl`, a contradiction between
  hypotheses (`False = True`, `None = Some v`), `omega`.
- **Simplifier (`simp`).** As in proof-automation.md §2: a loop that rewrites with a set of
  equations, anywhere in the goal, until none applies. **Simp set**: the equations it uses.
- **Splittable type.** A data type with finitely many shapes at the top: not recursive, not
  an indexed family. `Bool`, `Option a`, `Ordering`, `Int` (`OfNat n | NegSucc n`), a
  record, an enumeration, `Shape` above. Not `Nat` or `List a`.

## 3. How Stitchwort proves these today

All **[checked]** at `941e394f`.

- **`∧`, `∨`, `¬` on `Bool` are `if`s.** `a ∧ b` is `if a then b else False`, `a ∨ b` is `if
  a then True else b`, `¬a` is `Bool.not a` (`crates/elab/src/logic.rs:4-11`), and `if` is
  `Bool.ifThenElse`, defined by cases on the condition (`std/core/Data.sw:51-53`). So a chain
  of them computes as soon as each tested `Bool` is a constructor, and is stuck otherwise.
- **`match e:` generalises by computed form.** A scrutinee that isn't a variable is replaced
  "wherever it appears in the expected type", and in "variables in scope whose types mention
  the scrutinee", which are copied (`docs/syntax.md` §`match`, "What a generalised `match`
  replaces"). The comparison is on terms "as types hold it (evaluated and read back)"
  (`matching.rs:407`), by the occurrence test, which unfolds nothing further and looks
  through only locations and binder names (`matching.rs:682-686`). That is why `match nx:
  Float.isNaN x` finds it inside `h: Float.ieeeLt x y = True`, and why `isZero a ∧ isZero b`
  doesn't match `isZero b ∧ isZero a`.
- **The branches see computed goals.** After a split the goal and the copies are shown as
  their normal forms (§1.1), and the originals stay in scope as `h✝`.
- **Closers that exist.** `rfl` (by conversion); `Void.exfalso (Bool.falseNotTrue h)` and
  `Option.noneNotSome` (contradictions, each proved by `J` with a motive that tells the
  constructors apart, `std/core/Equality.sw:34-35`, `ListOptionPair.sw:58-59`); injectivity
  (`Option.someInjective`, by `Eq.cong` of a projection, `std/Option/Option.sw:18`);
  `omega`, which reads `Nat.leq … = True/False`, `Nat.equal … = True/False`, `(p && q) =
  True` and others as facts, and proves a non-arithmetic goal by refuting the facts
  (`omega.rs:22-30`; `docs/syntax.md` "Facts").
- **`rewrite`'s premise discharger** already tries "a hypothesis in scope of exactly its type,
  … `omega`" (proof-automation.md, stage 1b). `split`'s closers are the same kind of list.
- **No propositional extensionality.** There is `Quot.funext` (`docs/core.md:437-440`) but no
  `propext`: two propositions that imply each other can't be proved *equal*. So a rewrite can
  turn `(a ∧ b) = True` into `(b ∧ a) = True` (an equation between `Bool`s), but can't turn
  the proposition `And P Q` into `And Q P`. This matters for §7: Lean's `simp` relies on
  `propext` for most of its logic rules ([L3]).

## 4. How other systems do it

A research sub-agent fetched and read the sources below in full on 26 October 2026 and quoted
them; I checked the quotes I rely on against its saved copies of the pages (listed under
[Sources](#sources)). Where a full text couldn't be had, it says so.

### 4.1 Summary

| | rewriting with a lemma set | case splitting on `if`/`match` | `Bool` connectives |
|---|---|---|---|
| Lean 4 | `simp`: default set (`@[simp]`), `simp only [..]`, `simp?` | separate: `split` (one `if`/`match` at a time); Mathlib `split_ifs` (all `if`s) | simp lemmas (`Bool.and_true`, `Bool.and_eq_true`, …) |
| Isabelle/HOL | the Simplifier: conditional, ordered rewriting | built into `simp`: `if` in the goal split by default (`if_split`), `case` on request (`split: t.split`) | simp rules; `if` split |
| Rocq | `autorewrite with base` | `destruct (e) eqn:E`, by hand | `simpl` computes; lemmas |
| Stitchwort (proposed) | deferred (`simp [rules]`, proof-automation §6.3) | `split`: automatic, on the innermost stuck tests, goal and hypotheses | computation |

### 4.2 Lean 4

- **`simp` never splits.** Its default pipeline is `rewritePre >> simpMatch >> userPreSimprocs s
  >> simpUsingDecide` before the parts and `rewritePost >> userPostSimprocs s >> simpGround >>
  simpArith >> simpUsingDecide` after (`Simp/Rewrite.lean` L536-547 [L7]). An `if` is decided
  only when its condition simplifies to `True` or `False`, by the `reduceIte` simproc, run
  *before* the branches are visited:

  ```
  builtin_simproc ↓ [simp, seval] reduceIte (ite _ _ _) := fun e => do
    let_expr f@ite α c i tb eb ← e | return .continue
    let r ← simp c
    if r.expr.isTrue then … return .visit { expr := tb, proof? := pr }
    if r.expr.isFalse then … return .visit { expr := eb, proof? := pr }
    return .continue
  ```

  (`Simp/BuiltinSimprocs/Core.lean` L15-24 [L8]). The sub-agent found no case splitting
  anywhere on `simp`'s code path, and no `splits` field in `Simp.Config` (a grep of
  `MetaTypes.lean` for "split" matches nothing) [L9].
- **`split` is its own tactic.** "The split tactic is useful for breaking nested if-then-else
  and match expressions into separate cases. For a match expression with n cases, the split
  tactic generates at most n subgoals. For example, given n : Nat, and a target if n = 0 then
  Q else R, split will generate one goal with hypothesis n = 0 and target Q, and a second goal
  with hypothesis ¬n = 0 and target R. Note that the introduced hypothesis is unnamed… split
  at h will split the hypothesis h." [L2]
- **What `split` picks: the innermost condition.** `findSplit?` takes an `if`, then looks for
  a nested one inside its condition: "Try to find a nested `if` in `cond`" (`SplitIf.lean`
  L101-113 [L10]). It never splits on an `if` whose condition mentions a bound variable, and
  doesn't look inside proofs: "We do not look for split candidates in proofs." (L39-76).
  After a split it tidies each case with an empty simp set plus `reduceIte`, using only the
  hypotheses from before: "It is effective after a case-split." (L174-195, L284-294). If
  neither case changed: "`split` tactic failed to simplify target using new hypotheses"
  (L320-322).
- **Mathlib's `split_ifs`** splits them all: "`split_ifs` splits the main goal in two goals for
  every if-then-else expression it contains, by applying excluded middle to the condition. …
  If there are multiple if-then-else expressions, then `split_ifs` will split them all,
  starting with a top-most one whose condition does not contain another if-then-else
  expression." It skips a condition already known as a hypothesis and never splits the same
  one twice [L11].
- **Bool lemmas** are ordinary simp lemmas: `Bool.and_eq_true (a b : Bool) : ((a && b) = true)
  = (a = true ∧ b = true)`, `Bool.and_true`, `Bool.and_self`, `Bool.not_eq_true`,
  `decide_eq_true_eq`, `ite_true`, `ite_self` (`Init/SimpLemmas.lean` [L12]). Commutativity
  (`Bool.and_comm`) is **not** a simp lemma [L12].
- **Propositions as rules use `propext`.** "Due to propositional extensionality, equational
  lemmas can rewrite propositions to simpler, logically equivalent propositions. When the
  simplifier rewrites a proof goal to True, it automatically closes it." [L3]
- **`decide := true`**: "When true (default: false), rewrites a proposition p to True or False
  by inferring a Decidable p instance and reducing it." [L5] The code skips any term with free
  variables (`if e.hasFVar || e.hasMVar … return .continue`, `Rewrite.lean` L286-301 [L7]).
  So it decides closed facts only, which Stitchwort's `rfl` and `auto` already do.
- **Conditional rules** are discharged by simplifying the condition to `True`, to depth
  `maxDischargeDepth` (default 2) [L5]; `contextual` (default false; on for `simp_all`) adds
  the branch's condition as a fact when simplifying an `if`'s branch [L5][L7].
- **Budget**: `maxSteps`, "The maximum number of subexpressions to visit when performing
  simplification. The default is 100000." [L5]
- **Robustness**: "To write maintainable proofs, avoid using simp without only unless it
  closes the goal" [L6]; "simp? suggests an invocation of simp with a minimal simp set" [L6].
  "The default simp set is as much a part of a library's interface as the type signatures of
  the constants that it exports." [L4]

### 4.3 Isabelle

- **The Simplifier splits `if` by default, after rewriting.** "The looper is a list of tactics
  that are applied after simplification, in case the solver failed to solve the simplified
  goal. If the looper succeeds, the simplification process is started all over again… A
  typical looper is case splitting: the expansion of a conditional." The `if` rule is "?P (if
  ?Q ?x ?y) ←→ (?Q −→ ?P ?x) ∧ (¬ ?Q −→ ?P ?y)" (isar-ref §9.3 [I1]). `if_split` is the
  default split rule (`lemmas [split] = if_split`, `HOL.thy` [I3]).
- **And it warns about it.** "Case splits should be allowed only when necessary; they are
  expensive and hard to control. Case-splitting on if-expressions in the conclusion is usually
  beneficial, so it is enabled by default in Isabelle/HOL…" and, for splits in hypotheses,
  "With Splitter.split_asm_tac as looper component, the Simplifier may split subgoals! This
  might cause unexpected problems…" [I1].
- **`case` is not split by default**: "Case expressions are not split automatically by simp,
  but simp can be instructed to do so: apply(simp split: nat.split) splits all
  case-expressions over natural numbers… Splitting if or case-expressions in the assumptions
  requires split: if_splits or split: t.splits." (prog-prove §2.5.6 [I2]). And `simp` "can
  prove (A ∧ B) = (if A then B else False)" [I2]: Isabelle reasons about connectives through
  `if` too.
- **The weak `if` congruence is the default**: `if_weak_cong`, "Only the first argument is
  simplified; the others remain unchanged. This can make simplification much faster, but may
  require an extra case split over the condition ?q to prove the goal." [I1][I3]
- **Conditional rewriting**: "Conditions in conditional rewrite rules are solved recursively
  before the rewrite rule is applied", to `simp_depth_limit` (default 100) [I1]; and "all
  preconditions need to be simpler than the left-hand side of the conclusion… Suc n < m =⇒ (n
  < m) = True leads to nontermination." [I2]
- **Ordered rewriting** for commutativity: "Permutative rules are detected and only applied if
  the rewriting step decreases the redex wrt. a given term ordering… Ordered rewriting with
  the combination of A, C, and LC sorts a term lexicographically — the rewriting engine
  imitates bubble-sort." [I1]
- **`split` alone**: "The effect of repeatedly applying (split thms) can be imitated by
  '(simp only: split: thms)'." [I1]

### 4.4 Rocq

- `simpl` computes, it doesn't rewrite: it "Reduces a term to something still readable instead
  of fully normalizing it" [R1].
- Splitting is by hand: `destruct e eqn:E` "Generates a new hypothesis in each new subgoal that
  is an equality between the term being case-analyzed and the associated constructor" [R2],
  which is Stitchwort's `match E: e`. The sub-agent couldn't find ssreflect's `case: ifP` in
  the reference page it fetched (it lives in MathComp's `ssrbool`, not fetched): **[unverified]**.
- `autorewrite` "may loop if you build non-terminating rewriting systems" [R1].

### 4.5 What to take

1. **Split on the innermost condition**, as Lean's `findSplit?` and `split_ifs` do. In
   Stitchwort this is the fix for §1.2, since `∧` is an `if`.
2. **Keep splitting separate from rewriting**, as Lean does, and for Isabelle's stated reason
   (splits are "expensive and hard to control"). Composition (`split in simp [..]`) gives
   Isabelle's behaviour when wanted.
3. **Use computation where Lean uses lemmas.** Lean's `simp` doesn't unfold definitions by
   default and needs `ite_true`, `Bool.and_true`, `reduceIte` and `reduceCtorEq` to do what
   Stitchwort's evaluator does by itself on a split branch. And Lean's logic rules need
   `propext`, which Stitchwort doesn't have (§3).
4. **Close what is closed, split only when stuck**, and fail when nothing changes (Lean's
   "failed to simplify target using new hypotheses").
5. **Budgets that fail loudly** (Lean's `maxSteps`).

## 5. The proposal: `split`

### 5.1 Surface

`split` is a proof term, like `omega` and `ring` (no tactic language: proof-automation.md §3).

| form | meaning |
|---|---|
| `split` | split on what the goal and the hypotheses are stuck on, until every case is closed by computation, a contradiction, or `omega` |
| `split in t` | the same, and in each case the automatic closers leave, `t` (elaborated there, so `h` is that case's `h`, and `_`s are solved per case) |
| `rewrite p in split`, `split in simp [..]` | composition, as for any term |

`split` with nothing to split and nothing closed is an error (§5.7). There is no `split at h`:
which hypotheses take part is fixed by §5.3 (Q2).

### 5.2 What it splits on

At each step `split` computes the goal (and the hypotheses of §5.3) and, if one is stuck,
follows its blocker inwards, through the `Bool` connectives (`if`, `∧`, `∨`, `¬`) to the
condition they test, and through each stuck call to the argument its case tree tests, as far
as it goes. **The atom is the innermost term on that chain whose type is splittable with two
or more constructors** (Lean's rule, "innermost condition", §4.2). Unfolding a definition
doesn't make a new term: `Float.isNaN x` and its body `Nat.equal x.bits 9221120237041090560`
are one atom, named by the folded call.

- In `¬(Float.isNaN x) ∧ …` the atom is `Float.isNaN x`: inside it, `x.bits` is a `Nat`.
- `Float.isZero b` is itself an `∨` (`Nat.equal b.bits 0 ∨ Nat.equal b.bits
  9223372036854775808`), so its two tests are two atoms. `isZero b ∧ isZero a` is never an
  atom, which is the fix for §1.2.
- In `(%match1 s t).ref` it is `s`, not the generated `%match1 s t`; in `parseSmallOption s t
  = Some v` it is `s.toNat` (inside it, `s` is `Text`).
- Records and other one-constructor types are split only when nothing else is stuck (§6.5):
  splitting `x: Float` into its fields never helps decide `Float.isNaN x`.

Which atom is chosen changes the number of cases, never whether the proof is right: anything
still stuck after a split is split next. The scratch trees of §1 split `Float.isZero x` as one
`match` (one case fewer per `isZero`); `split` would make one or two more cases there
**[inferred]**. Atoms are shown by their folded form where the goal has one (glued values,
SW-257), so the case list and the expanded tree read `Float.isNaN x = False`.

`split` never splits on: a term that mentions a variable bound inside the goal (as Lean, §4.2;
there is no `match` there to write); a proof; a value of a recursive type (`Nat`, `List`), whose
cases never end; an indexed family. Those stay for the closers.

Order: the goal's atom first; then the hypotheses' (§5.3), latest first. A value already known
in this branch (a hypothesis `atom = C`) is not split again (as `split_ifs`, §4.2).

### 5.3 Which hypotheses

A hypothesis takes part when, computed, it is an equation with a constructor form on one side
and a stuck term on the other: `ieeeLt x y = True`, `parseSmallOption s t = Some v`. Such a
hypothesis can only become a contradiction or a fact `omega` reads once its atom is split, so
splitting on it is the useful direction (SW-587's ladder is driven entirely by `h`). Other
hypotheses (`h: (n: Nat) -> …`, `List.Mem x xs`) are generalised as `match` does today, but
never cause a split. Isabelle splits in hypotheses only on request (§4.3); Q2 asks whether
Stitchwort should.

### 5.4 Closing a case

Tried at every node, before splitting further, in this order (cheap first):

1. **Computation**: the goal is `rfl` by conversion, within the budget.
2. **Contradiction**: a hypothesis computes to an equation between different constructors
   (`False = True`, `None = Some v`, `Dot … = Circle …`). The proof is `Void.exfalso` of a `J`
   whose motive tells the constructors apart, built for the type as `Bool.falseNotTrue` is
   written by hand.
3. **Taking an equation apart**: a hypothesis `C a1 … = C b1 …` (same constructor) adds `a1 =
   b1`, … as hypotheses (by `Eq.cong` of a projection, as `Option.someInjective` is written),
   for the next steps. This is what closes SW-587's last leaf.
4. **A hypothesis of exactly the goal's type** (latest first).
5. **`t`**, for `split in t`.
6. **`omega`**, with the case's facts, only when nothing is left to split (it is the most
   expensive, and on a node that can still split, it would usually fail).

A case nothing closes, with nothing left to split, is the error of §5.7. Between 1 and 6
nothing is guessed: no lemma is applied unless the user wrote it in `t`.

### 5.5 The proof term

Each split is the generated `match` that `match e: atom with` writes today (`matching.rs`,
lifted to `owner.%matchN`), with one arm per constructor and the equation named. The closers
are their own terms (`rfl`, `Void.exfalso (…)`, `Eq.cong …`, `t`, `Std.Omega.prove …`). So the
term `split` writes is exactly a proof a user could write, and the kernel checks it as such:
**no new trusted code, no new axioms**, and `stitchwort axioms` is unchanged. The expand code
action (as proposed for `simp` in proof-automation.md §6.3) replaces `split` by that `match`
tree, with readable names (`nx`, `zx`, … from the atom: `isNaN` → `nan1`, or numbered; a build
detail).

### 5.6 Termination and predictability

- **Termination.** Each split replaces an atom by a constructor in the goal and the
  hypotheses, and an atom is never split twice in one branch. New atoms can appear when a
  branch unfolds further (`Float.orderKey x` after `isZero x` is known), but only from
  definitions that compute on the new constructor; recursive types are never split, so the
  usual source of endless unfolding is out. A budget (§5.8) bounds the rest.
- **Predictability.** Given the goal and hypotheses, the tree is fixed: atoms in evaluation
  order (the order the definitions test them, left to right), the goal before hypotheses,
  closers in the fixed order of §5.4. It doesn't depend on a lemma set (there is none) or on
  what the library marks; adding a library lemma can't change a `split`. Changing a
  *definition* can, as it changes `match e:` proofs today.
- **What it is complete for.** A goal that is an identity between `Bool` expressions over
  atoms (`(a ∧ b) = (b ∧ a)`, `Bool.xorAssoc`, `andOr`) is proved: after splitting every atom,
  both sides are constructors, and `rfl` decides them. That is the truth-table method, and its
  cost is exponential in the number of atoms; fine for the 2 to 6 atoms seen here, and the
  budget says so when it isn't.

### 5.7 Errors

- **A case it can't close** (`E-SPLIT`): the error lists the path to that case, folded, and the
  case's goal and hypotheses with the stale copies left out (the copy of `h` a later split made
  replaces the earlier one in the display):

  ```
  [E-SPLIT] Error: `split` can't close the case
      Float.isNaN x = False, Float.isNaN y = False, Nat.equal x.bits 0 = False,
      Nat.equal x.bits 9223372036854775808 = False
    Note 1: h: Int.less (Float.orderKey x) (Float.orderKey y) = True
    Note 2: goal: Int.leq (Float.orderKey x) (Float.orderKey y) = True
    Note 3: it stopped here because `Float.orderKey x` is stuck on `x.bits`, a `Nat`, which
            `split` doesn't take apart; give the case's proof as `split in t`
    Note 4: 3 other cases were closed (2 by contradiction, 1 by computation)
  ```

  (wording illustrative). That this display is readable is half the value: the by-hand route
  shows §1.1's fourteen unfolded copies.
- **Nothing to split** (`E-SPLIT`): the goal isn't stuck on anything splittable and no closer
  proves it; it says what the goal is stuck on, if anything (`xs`, a `List`).
- **Budget** (`E-SPLIT-BUDGET`): about cost, not truth, as `E-REWRITE-BUDGET` is. It shows how
  many cases were made, the atoms split on, and the first case still open.
- **`split in t`**: when `t` fails in a case, that case's error is `t`'s, under the path note.

### 5.8 Performance

- **The measured cost is in generalising, not in deciding.** §1.1's 12-leaf tree took 35 ms,
  of which at least 24 ms is the eleven `match`es with their copies of every hypothesis,
  each read back fully unfolded **[run]**. `split` doesn't have to work that way: it builds
  the tree itself, so it can (a) generalise only in the goal and the hypotheses of §5.3,
  replacing rather than copying, (b) keep the atoms folded (§5.2), and (c) try `rfl` and
  contradictions on values without reading them back. The acceptance bar (§8) is that the
  bare `split` for `ieeeLtLe` costs no more than 5 ms, against 0.3 ms for today's helper and
  call, and 4.4 ms for the by-hand tree with the lemma.
- **Budget.** At most 64 cases per `split` (§1's largest tree has 12), and the closers share
  one evaluation-step budget, like `rewrite`'s. Each is a build detail to tune on the
  acceptance tests; running out is `E-SPLIT-BUDGET`, never a wrong answer, and checking as a
  whole stays under the `E-RESOURCE` limits as now.
- **Order of closers.** `omega` runs only at nodes with nothing left to split (§5.4), so a
  `split` that a lemma closes early (`split in Float.keyLessLeq _ _ h`) never pays for it.

## 6. The reproductions, before and after

The "after" forms are by hand: no prototype of the search was built. Each tree was written
out with `match` and checked **[run]**, unless marked; it is what `split` would emit except
that the hand trees split `Float.isZero` as one atom where §5.2 makes it two.

### 6.1 `Float.ieeeLtLe`

```
-- before: the 6-line helper `Float.ltLeBools` and a 3-line call
-- after
theorem Float.ieeeLtLe (x: Float) (y: Float) (h: Float.ieeeLt x y = True): Float.ieeeLe x y = True := split
```

The tree is scratch `ieeeLtLeSplit` (§1.1): `isNaN x`, `isNaN y`, `isZero x`, `isZero y`, then
the two sign tests inside `orderKey`; leaves `rfl`, `False = True`, or `omega`. With the
lemma as the closer, `split in Float.keyLessLeq _ _ h` stops two levels earlier
(`ieeeLtLeSplitIn`). `ltLeBools` goes, and so does `Float.keyLessLeq`'s own match (`split`:
`Int` is splittable, leaves `rfl`, contradiction or `omega`) **[inferred]**: not run.

The `c16897c7` lemmas that take the chain apart by `Bool.andRight`/`orElim` (`ieeeLeRank`,
`ieeeLtRank`, `ieeeLeNotNaN`) become `split in …` with their real content at the leaves; for
example `ieeeLeNotNaN` is `split in Both rfl rfl` (in the cases that survive, `isNaN x = False`
and `isNaN y = False` are the split's own equations, so both conjuncts are `rfl` after the
split; the rest are `False = True` contradictions) **[inferred]**: not run.

### 6.2 The ported program's helpers (public form)

```
-- before: `orSwapBools` (6 lines), `equalSymm` (2 lines) and a 3-line call
-- after
theorem looseEqSymm (a: Float) (b: Float) (h: looseEq a b = True): looseEq b a = True := split
```

Tree: scratch `looseEqSymmSplit`, 5 leaves, `rfl` or `omega`, 2.4 + 1.0 ms **[run]**. The
compound-condition failure of §1.2 can't happen: the atoms are the `Nat.equal` tests inside
`isZero a` and `isZero b` and the final `Nat.equal`, never an `∧` of them. On the private program's ~70 lines, I expect the same, but
haven't seen them: **[unverified]**, and the stage 1 acceptance test is to measure it there.

### 6.3 SW-587: the `.orAbort` chain

```
theorem parseSmallSome (s: Text) (t: Text) (v: Nat) (h: parseSmallOption s t = Some v): v <= 10 := split
```

`h` is stuck on `s.toNat` (an `Option`, split), then `t.toNat`, then `Nat.leq (a + b) 10`.
Three cases are `None = Some v`; in the last, `h` is `Some (a + b) = Some v`, taken apart to
`a + b = v`, and `omega` closes `v <= 10` with `ok`. This is the tree of scratch
`parseSmallSome` (11 lines, 2.2 + 0.6 ms) with `omega` for its last line **[inferred]**: the
taking-apart step (§5.4, 3) is new, so this leaf wasn't run as written. SW-587 asked for "a
generated lemma (or simp via `Abort.toOptionThen` / `Option.flatMapEqSome`)": `split` needs
neither, because the chain computes once each lookup is a constructor. **Covered.**

### 6.4 SW-581: shared-field update, then another field

```
theorem refAfterId (s: Shape) (t: Text): ({ s | id = t }).ref = s.ref := split
```

The goal is stuck on `s` (via the generated `%match1`): one split, three `rfl`s. The 9-arm
version is two splits. **Covered**, though SW-581's own proposal (generated lemmas, so it is
`rfl` or a named lemma at the use) is still the better fix where these appear inside larger
proofs, because `split` only works where the goal is *about* the update.

### 6.5 SW-568: record eta

`p = { row = p.row, column = p.column }` is stuck on `p` (the projections), so `split` makes
one case, `{ row = r, column = c } = { row = r, column = c }`, which is `rfl`. **Covered as a
workaround**; `Pos.ext p _ rfl rfl` works today, and eta in conversion (the ticket) would make
it `rfl` and is the real fix.

### 6.6 Summary

| shape | before (body lines) | after | how |
|---|---:|---|---|
| `ieeeLtLe` + `ltLeBools` | 9 | `split` | §6.1 |
| `looseEqSymm` + helpers | 11 | `split` | §6.2 |
| `parseSmallSome` (SW-587) | 11 | `split` | §6.3 (last leaf not run) |
| `refAfterId` (SW-581) | 4 | `split` | §6.4 |
| record eta (SW-568) | 1 | `split` (workaround) | §6.5 |

## 7. `simp`: what it would add, and when

**What the three parts the ticket names become.**

1. **Rewriting with a lemma set** is proof-automation.md §6.3 unchanged: `simp [rules]`,
   listed rules only, under binders through the congruence lemmas stage 1 built, conditional
   rules discharged as `rewrite`'s premises are. None of §6's proofs needs it.
2. **`Bool` normalisation** (`∧`/`∨`/`¬`/`if`, `==` on known constructors) is mostly
   *computation* in Stitchwort: on a split branch the connectives compute, and `==` on
   constructors computes through its `DecEq` instance. A lemma set would add two things
   computation can't do: normalising `Bool`s that mention a bound variable (under `x => …`,
   where `split` can't go; `List.filter (x => p x ∧ True) xs`), and simplifying without
   splitting (`(a ∧ a) = a` in one step rather than two cases). Neither appears in the
   motivating proofs. Note also that without `propext` (§3), a Stitchwort `simp` can rewrite
   `Bool`s and data, not propositions: `And P Q` to `And Q P` is out of reach, which is most
   of Lean's logic simp set.
3. **Case splitting** is `split`, §5.

**How lemmas would be marked**, if `simp` is built: as proof-automation.md Q2 recommended,
listed in each proof (`simp [a, b]`), no `@[simp]` attribute and no default set; Lean's own
advice converges on that (`simp only`, `simp?`, [L6]), and a default set would be the first
attribute with a meaning inside Stitchwort (today a known attribute on a theorem is refused,
`docs/syntax.md:486`). Named sets (`simp
[List.mapLaws]`) would be the middle way if lists repeat. Q5 asks this again because it is
the one `simp` question that shapes how proofs read.

**Does `simp` split?** Isabelle's does (after rewriting, as its looper); Lean's doesn't. I
recommend Lean's choice with composition: `simp [..]` never splits, and `split in simp [..]`
or `simp [..] in split` gives either order explicitly. One mechanism for splitting, one
place its cost shows (Q3).

**When to build it.** When a proof needs rewriting with lemmas *and* `rewrite p, q in …` is
too long or can't do it (the rule must be applied repeatedly, or inside binders with
conditions): proof-automation.md §1.4's `multiplierSucc` and `weightedIds` are such proofs,
and they are still written the long way. So the trigger D1168 waited for is still "a proof
that needs it"; this ticket's proofs turned out not to. Q1.

## 8. Staging, acceptance, risks

### 8.1 Stages

| stage | what | acceptance |
|---|---|---|
| 1 | `split` and `split in t` (§5), the expand code action, `E-SPLIT`, `E-SPLIT-BUDGET`; docs in `syntax.md` and `guide/10-proofs.md`; `examples/accept/split-*.sw`, `examples/reject/split-*.sw` | §6.1 to §6.4 as one-word proofs; `Float.ltLeBools` and `Float.keyLessLeq`'s match gone from std; `split` for `ieeeLtLe` ≤ 5 ms; the private program's ~70 lines of helpers measured before and after (a target of at least 50 gone); no kernel change; `stitchwort axioms` unchanged |
| 1b | convert: std's and AoC's `Bool` helpers and `match e:` ladders that `split` replaces (§1.4) | lines and `falseNotTrue` mentions before and after, per file; check time within +2% |
| 2 | `simp [rules]` (proof-automation.md §6.3), only when a proof needs it | as there |

Stage 1 is one lane. It doesn't need proof-automation's stage 3. It reuses `matching.rs`'s
generalisation (or a leaner copy, §5.8), `omega::prove_premise`-style calls into `omega`, and
the contradiction and injectivity terms the library already writes by hand.

### 8.2 Risks

- **Exponential cases.** A goal testing ten independent Booleans has 1,024 cases. The budget
  turns that into an error with the count; the fix is a lemma at an earlier node (`split in
  t`). §1's goals have at most 12 cases **[run]**.
- **Slow generalisation.** §1.1's by-hand tree spends 24 ms or more in `match`es. If `split`
  can't do better (§5.8), it will be slower than the helpers it replaces, which cost 0.3 ms;
  the acceptance test catches that. Proofs are cached by content hash, so this is a
  first-check cost.
- **Over-splitting.** `split` may split on something the proof didn't need (the sign tests in
  §6.1, when the lemma would have done). The result is still a proof, just a larger one; `split
  in t` stops earlier. The expand code action shows what was done.
- **Fragility to definitions.** A `split` proof depends on what the definitions test and in
  what order; reordering a program's `∧` can change the tree (not the outcome, for `Bool`
  identities). That is no worse than the `match e:` proofs it replaces, and better than the
  helpers, which restate the definition.
- **Display.** The folded names in §5.7's messages rely on glued values surviving a split. If
  they don't, the messages show unfolded terms as `match` does today, which is worse but not
  wrong.

### 8.3 Stage 1 as built

Built in `crates/elab/src/split.rs`, with the surface in `crates/syntax` (`Expr::Split`;
`split` is a keyword except after a `.`). The kernel is unchanged and nothing new is trusted:
each split is the generated `match` of `matching.rs`, and the closers are `rfl`, `J` terms and
`Std.Omega.prove`. Decisions: `split` now, `simp` deferred (D1317); hypotheses of the form
"stuck = constructor" are split on, after the goal (D1318); `omega` only where nothing is left
to split (D1319), with the exception below. User docs: [syntax.md](../syntax.md#split),
[guide chapter 10](../guide/10-proofs.md#cases-split). Examples:
`examples/accept/split-bool.sw`, `examples/accept/split-data.sw`,
`examples/reject/split-*.sw`.

**Acceptance** (release CLI, `STITCHWORT_TIMINGS=decls`, best of 8 runs for `ieeeLtLe`, one
run otherwise; elaboration + kernel ms; the machine's load average was about 110 to 120, so
absolute times are high for all rows alike):

| proof | as built | before |
|---|---|---|
| §6.1 `Float.ieeeLtLe` by `split` | 7.5 + 2.5 (207k steps) | helper + call 0.3; lemma tree 3.5 + 0.7; bare hand tree 35.3 + 2.6 |
| §6.1 by `split in Float.keyLessLeq _ _ h` | 4.3 + 1.2 | |
| §6.2 `looseEqSymm` (compound `∧` in two orders) | 3.4 + 2.3 | failed by hand (§1.2) |
| §6.3 SW-587 `parseSmallSome` | 1.4 + 0.8 | |
| §6.4 SW-581 `refAfterId` | 0.1 + 0.0 | |
| §6.5 SW-568 `posEta` | 0.0 + 0.0 | |

**The 5 ms bar for bare `split` on `ieeeLtLe` is missed**: about 10 ms, a third of the bare
hand tree's but twice the bar. Profiles put most of the rest in `matching.rs`'s generalisation
(reading the goal and hypotheses back in normal form) and in resolving the lifted
`%match` helpers. Two of §5.8's three savings are built: stale copies of hypotheses are not
generalised again (a later copy replaces them), and contradictions and `rfl` are tried on
values without reading them back. The third, keeping atoms folded through generalisation
(§5.8 (b)), was tried and backed out **[run]**: to reach the atom, the calls around it have
to be unfolded, and their bodies came back with the neighbouring calls unfolded too (after
splitting `Float.isNaN x`, the goal showed `Nat.equal y.bits 9221120237041090560` where
`Float.isNaN y` had been), so the next atom was found unfolded again and no time was saved.
Keeping the neighbours folded needs evaluation to glue the calls in a body it unfolds; that is
the next lever if the time matters.

**Where it differs from §5:**

- **The goal's own side is tried with `omega` before it's split.** When the atom found is a
  whole side of the goal (`Nat.leq a b = True`), splitting gives a `True = True` case and a
  `False = True` case, and `omega` usually proves the goal whole. So `omega` is tried first
  there (§5.4 puts it last); the goal-side atom is also taken only after the hypotheses have
  been searched, since what they're stuck on usually decides more.
- **Records.** A one-constructor atom is split only when the chain to it met no unsplittable
  value and it isn't an argument of a stuck call; otherwise `x: Float` was split into its
  fields under `Float.isNaN x`, which made the tree much larger (the first build took 8.2 s on
  `ieeeLtLe`, before this rule and the goal-side one).
- **Contradictions** on `Bool` use `Bool.falseNotTrue` (turned round by `J` for `True =
  False`); on other types a `J` with a motive drafted as a lifted helper, as §5.4 says.
- **Taking an equation apart** adds the field equations as `let`s named `%fact1`, …, and the
  split equations are `%split1`, …: neither name can be written, so `split in t` refers to them
  only through `_`s and `omega`.
- **`Float.isZero x` is two atoms** (§5.2's prediction), so the `ieeeLtLe` tree has more cases
  than §1.1's hand tree.
- **Not built**: the expand code action (§5.5), and converting std and AoC (stage 1b).
- **Reserved word.** `split` became a keyword, so bare uses of `Text.split` stopped working:
  `import Text (split)` (two examples, `docs/syntax.md`, guide page 13), an exported
  `split` in `examples/extract/text.sw`, and a theorem named `split`. They now use other
  names (`lines`, `splitOn`, `splitText`); `line.split ','` and `Text.split` are unchanged.

## 9. Decisions for Matt

Build details (search order, budgets, the leaner generalisation, names in the expanded tree,
error wording) are mine and are decided above. These six are about what proofs look like.

**Q1. Build `split` now, and keep `simp` (rewriting with a lemma set) deferred?**
Recommendation: **yes**. Every motivating proof is closed by `split` (§6), and none by
rewriting. Alternative: build proof-automation's stage 3 `simp [rules]` too, as one feature
with `split`; larger, and its trigger proofs (§7) are not the ones that started this ticket.

**Q2. Should `split` split on what hypotheses are stuck on, or only on the goal (with an
explicit `split at h` for hypotheses)?** Recommendation: **goal and hypotheses**, limited to
hypotheses that say "this is a constructor" (`… = True`, `… = Some v`, §5.3). SW-587's ladder
is driven entirely by `h`, and `ieeeLtLe` closes most cases by contradictions in `h`.
Alternative: Lean's and Isabelle's default of the goal only (hypotheses on request), more
predictable in principle, but every motivating proof would need `split at h`.

**Q3. Should a future `simp` split on its own when rewriting gets stuck (Isabelle), or never
(Lean), with `split in simp [..]` to combine them?** Recommendation: **never; combine as
terms**. One mechanism for case splits and its cost in one visible place. Alternative:
Isabelle's looper, shorter proofs where both are needed.

**Q4. Should `split` call `omega` at the leaves automatically?** Recommendation: **yes, last,
only where nothing is left to split** (§5.4). Without it, §6.1 and §6.2 need a lemma at the
leaves. Alternative: `split` closes only by computation and contradictions, and `split in
omega` asks for it; cheaper and more explicit, one more word in most uses.

**Q5. If `simp` is built: rules listed in each proof only, or an `@[simp]` default set?**
Recommendation: **listed only**, as proof-automation.md Q2 recommended (§7). Alternative:
Lean's default set, shorter calls, but a proof's meaning then depends on what any imported
file marks.

**Q6. Name: `split`?** Recommendation: **`split`**, Lean's and Isabelle's name for the same
idea (§4). Alternatives: `cases` (suggests one split on a named variable, as Lean's `cases`
does), `decide` (suggests running a decision procedure, which `auto` already does).

## Sources

**Read in full** by a research sub-agent on 26 October 2026 (its saved copies were in the
lane's scratch directory, and I checked the quotes this note relies on against them):

- [L1] Lean reference, The Simplifier (chapter index): https://lean-lang.org/doc/reference/latest/The-Simplifier/
- [L2] Lean reference, Tactic Reference (Simplification section; `split`, `by_cases`, `decide`, `bv_decide`, `omega`): https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/
- [L3] Lean reference, Rewrite Rules: https://lean-lang.org/doc/reference/latest/The-Simplifier/Rewrite-Rules/
- [L4] Lean reference, Simp Normal Forms: https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-Normal-Forms/ ; Simp sets: https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/ ; Invoking the Simplifier: https://lean-lang.org/doc/reference/latest/The-Simplifier/Invoking-the-Simplifier/ ; Simplification vs Rewriting: https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/
- [L5] Lean reference, Configuring Simplification: https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification/
- [L6] Lean reference, Terminal vs Non-Terminal Positions: https://lean-lang.org/doc/reference/latest/The-Simplifier/Terminal-vs-Non-Terminal-Positions/
- [L7] Lean source, `Simp/Rewrite.lean` and `Simp/Main.lean` (read in full), `Simp/Types.lean` (lines 1-470), at commit `c3f0fa3b`: https://github.com/leanprover/lean4/blob/c3f0fa3b44bf1e3aeae3a613c66e7262b8a6ba6f/src/Lean/Meta/Tactic/Simp/
- [L8] Lean source, `Simp/BuiltinSimprocs/Core.lean` (in full): https://github.com/leanprover/lean4/blob/c3f0fa3b44bf1e3aeae3a613c66e7262b8a6ba6f/src/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean
- [L9] Lean source, `Init/MetaTypes.lean` (`Simp.Config` block only, **not in full**): https://github.com/leanprover/lean4/blob/c3f0fa3b44bf1e3aeae3a613c66e7262b8a6ba6f/src/Init/MetaTypes.lean
- [L10] Lean source, `Meta/Tactic/SplitIf.lean` and `Elab/Tactic/Split.lean` (in full), `Meta/Tactic/Split.lean` (doc comments, `splitMatch`, `splitTarget?`, `splitLocalDecl?` only): https://github.com/leanprover/lean4/blob/c3f0fa3b44bf1e3aeae3a613c66e7262b8a6ba6f/src/Lean/Meta/Tactic/SplitIf.lean
- [L11] Mathlib, `Mathlib/Tactic/SplitIfs.lean` (in full): https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/SplitIfs.lean
- [L12] Lean source, `Init/SimpLemmas.lean` (every `@[simp]` line listed, quoted regions read; **not read line by line**), and greps of `Init/Core.lean`, `Init/Data/Bool.lean`, `Init/PropLemmas.lean` for the commutativity lemmas: https://github.com/leanprover/lean4/blob/c3f0fa3b44bf1e3aeae3a613c66e7262b8a6ba6f/src/Init/SimpLemmas.lean
- [I1] Isabelle/Isar reference manual (October 2026), §9.3 "The Simplifier" (pp. 219-239) in full, and §9.2.2 (`split` method): https://isabelle.in.tum.de/doc/isar-ref.pdf
- [I2] Isabelle, "Programming and Proving in Isabelle/HOL" (October 2026), §2.5 in full: https://isabelle.in.tum.de/doc/prog-prove.pdf
- [I3] Isabelle `src/HOL/HOL.thy` (GitHub mirror, excerpts on `if_split`, `if_cong`, `if_weak_cong`): https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/HOL.thy
- [R1] Rocq 9.2 reference, `auto`/`autorewrite` (entries only, **not in full**): https://rocq-prover.org/doc/V9.2.0/refman/proofs/automatic-tactics/auto.html ; `simpl` (entry only): https://rocq-prover.org/doc/V9.2.0/refman/proofs/writing-proofs/equality.html
- [R2] Rocq 9.2 reference, reasoning with inductives (`case_eq`, `induction_clause`'s `eqn:`; entries only, **not in full**): https://rocq-prover.org/doc/V9.2.0/refman/proofs/writing-proofs/reasoning-inductives.html

**Not read:** MathComp's `ssrbool` (`ifP`); "Metaprogramming in Lean 4" and "Theorem Proving in
Lean 4" (the reference manual and source covered the same ground at first hand).

**Stitchwort**, at `941e394f`: as cited inline.

**Scratch reproductions** (not committed; checked with the release CLI built from `941e394f`):
`repro1.sw` (`ltLeBools`, `ieeeLtLe`, `ieeeLtLeDirect`: the by-hand split and its goal
display), `repro1b.sw` (`ieeeLtLeSplit`, bare split to `omega` leaves; `ieeeLtLeSplitIn`, with
the lemma), `repro1c.sw` (the same tree with holes, for the timing in §1.1), `repro2.sw`
(`looseEq`: helper, compound `match` stuck, atom `match`, bare split), `repro3.sw`
(`parseSmallSome`, `refAfterId`, `posEta`, `posEtaMatch`).
