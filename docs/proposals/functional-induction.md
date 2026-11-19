# Proposal: functional induction that proofs actually use (`match induct`, gaps and reach)

**Status:** draft 1, 19 November 2026. Ticket SW-4229 (Opus, paper), from
[SW-4222 §6.2](../reviews/SW-4222-lean-rocq-comparison.md) ("induction along
a function", ranked second). A design note only: nothing in the compiler
changes. One decision for Matt in [§6](#6-the-decision-for-matt). Written
against `main` at `13575ae77`.

Related: [function-equations.md](function-equations.md) (the design and
as-built record of `f.eqK`, `f.induct` and `match induct`, SW-1028 to
SW-2868), [pattern-guards.md](pattern-guards.md) (guarded arms and their
equations), [proof-walk-step.md](proof-walk-step.md) and its review
[SW-4238](../reviews/SW-4238-walk-step-review.md) §3.12, SW-4047 (a proof
`match` doesn't refine a guard), D3694 / SW-4236 (or-patterns that bind).

Claims are marked **[measured]** (counted by
[functional-induction/count.py](functional-induction/count.py), or read off
arms by hand, as said), **[run]** (a file in
[functional-induction/](functional-induction/) checked with
`target/release/stitchwort` built from main this evening, or with Lean
4.35.0 from `nixpkgs#lean4`), **[read]** (the file or page named),
**[recalled]** (from memory of the system's documentation, not re-read for
this note), **[sketch]** (proof text written for this note, not checked) and
**[estimated]**.

## In plain words

**The problem.** SW-4222 asked for a generated `f.induct` that follows a
function's own cases. **Stitchwort has had it since 2 November**: `f.induct`
(SW-1057) and `match induct (f args) with` (SW-1058), with the guard or `if`
condition as each case's hypothesis and the call already unfolded in the goal
[read: docs/syntax.md, "Functional induction"; run]. SW-4222 didn't know, and
neither do the proofs: of 9,687 theorems in the formatter and std, **none**
uses it [measured]. Instead 115 formatter proofs and 41 std proofs re-do a
function's split by hand (`match pair: fwdPair … with`, 278 such splits), and
56 hand-written "this is what the function does here" lemmas in the formatter carry a
condition (`withoutRNop`, `withoutRPair`) [measured]. Three things keep it
unused: the proving guide that every proof lane reads first never mentions it;
it is refused for the formatter's commonest shape (a guarded arm that a later
arm partly overlaps: `withoutR` and at least six of its relatives); and for
std's own functions it is never made when `match induct` is the only thing
asking (a bug, B1).

**The change.** Not a new feature: finish the one we have and make it the
tool proofs reach for. Fix B1; teach `match induct` in the proving guide;
give a guarded, partly overlapped arm its cases (one where the guarded arm's
patterns matched and its guard failed, one where they didn't), as Isabelle's
`fun` does with overlapping patterns; give a recursive call inside a
non-tail `match` its induction hypothesis; let `match induct` alternatives
share a body with an or-pattern. The kernel doesn't change: every
principle is an ordinary theorem the kernel checks, as today.

**What it should do.** The SW-4222 sample `allTokensWithout` goes from 29
lines to about 14 [sketch], Lean's being 15 and Rocq's 12 [read: SW-4222
§3.4]; with the if-style definition it is 4 alternatives today [run]. Std's
`Text.allNotLineBreak` goes from 13 lines to 8, checked [run]. The step lemmas
`withoutRNop`/`withoutRPair` and their two sibling pairs (6 lemmas, 25 uses)
can go once their users switch [measured]. Cost: four small lanes, about
2 to 3 hours of agent time in all [estimated from past actuals, §5].

## Contents

1. [The problem in numbers](#1-the-problem-in-numbers)
2. [Prior art](#2-prior-art)
3. [Design](#3-design)
4. [Before and after](#4-before-and-after)
5. [Cost and risks](#5-cost-and-risks)
6. [The decision for Matt](#6-the-decision-for-matt)

## 1. The problem in numbers

### 1.1 What the corpus does

`count.py` reads every top-level `def` and `theorem` of `tools/fmt/src`
(tests left out) and `crates/elab/src/std`, comments stripped. Its
heuristics are textual; their precision is discussed below the table
[measured, `count.py`, at `13575ae77`].

| | tools/fmt | std |
|---|---:|---:|
| definitions / recursive ones | 2,893 / 541 | 1,697 / 444 |
| recursive definitions with a guarded arm and an arm after it | 21 | 1 |
| theorems / proved by recursion (the theorem calls itself) | 5,422 / 924 | 4,265 / 1,133 |
| **"along f"**: by recursion, splits with `match`, and the statement names a recursive definition | 599 (14,724 lines) | 273 (5,021 lines) |
| of those, with a named split `match h: e with` (a branch condition re-split by hand) | **115** (227 splits) | **41** (51 splits) |
| step lemmas: conclusion `f … = f …` with `f` recursive | 172 | 356 |
| of those, taking a condition (`= True`, `= False`, `≠` or `¬` in a hypothesis) | **56** | **49** |
| "along f" proofs that use one of those conditional step lemmas | 48 | 10 |
| proofs that name `f.induct` or use `match induct` | **0** (5 hits, all inside the self-hosted parser's strings) | **0** |

How to read it:

- **"Along f" over-counts.** It catches every structural induction whose
  statement mentions a recursive function, including plain list inductions
  where `f`'s recursion and the list's coincide and `match induct` saves
  nothing. The row with named splits is the tighter one: a proof that splits
  on a branch condition by name is re-doing a split the function makes. The
  three I read (`homeStands`, 13 splits; `Text.allNotLineBreak`;
  `laidWithout`) are all of that kind [read].
- **Step lemmas over-count too.** 356 in std includes algebraic laws whose
  two sides happen to start with the same function (`List.map f (xs ++ ys) =
  List.map f xs ++ …` has `++` on the right, but `Map.Raw.getInsertOther` is
  a real law, not an unfolding step). The conditional ones in the formatter
  are mostly unfolding steps: `withoutRNop`, `barishNop`, `barishFNop`,
  `endsDrop` and the like [read]. In std, mostly not (`Map.*Other`).
- **Zero uses** is exact. Of the 22 hits for `match induct` in `tools/`,
  every one is the self-hosted parser parsing it, its tests and its notes
  [measured: grep].

So, at a conservative reading: about **150 proofs** hand-build a split that
`match induct` would give them, and the formatter keeps **about 50
conditional step lemmas** whose job is one equation each.

### 1.2 Why it is unused

1. **Not taught where lanes look.** `docs/proving-guide.md`, which every
   proof lane reads first (CLAUDE.md), says "Induction is recursion. A
   theorem that calls itself on a smaller argument is a proof by induction"
   and lists `f.eqK` and `T.induct`, but never `f.induct` or `match induct`
   [read: proving-guide.md §2, §3]. The language guide does teach it
   (docs/guide/10-proofs.md:450-560) and the web tour has a page
   (`web/guide/26-induct.sw`) [read], but lanes don't read those for proof
   technique.
2. **G1: guarded arm partly overlapped by a later one.** The formatter's
   rule-N family is written

   ```
   def withoutR (behind rest: List Leaf): List Leaf := match rest with
     | [] => behind
     | [comma, closer, ..after] if comma.kind == Comma && closer.kind.isCloser && hasItem behind => …
     | [leaf, ..after] => withoutR [leaf, ..behind] after
   ```

   and `withoutR` gets no `f.induct`: "an overlap hypothesis about a guarded
   earlier arm is needed where that arm's patterns match, which stage 2a's
   proof doesn't establish" [run: `g1-guarded-overlap.sw`]. Its third
   equation exists, in Lean's form (`∀ closer after1, after = [closer,
   ..after1] → ¬(…)`) [run], but the induction principle doesn't. Reading the
   arms of the 21 guarded definitions, at least 9 have this shape: `withoutR`,
   `withBareR`, `withMarkedR`, `withoutLastCommas`, `withBareLastCommas`,
   `withMarkedLastCommas`, `barishF`, `pastAttributes`, `rowNames` [measured
   by hand]. These are exactly the definitions whose proofs carry
   `fwdPair` (36 uses) and the `…Nop`/`…Pair` lemmas.
3. **G2: a recursive call inside a `match` that isn't in tail position.**
   The formatter's checkers are `Bool` predicates of the form `c && (match
   step owed x with | None => False | Some still => stands still words
   rest)`; such a definition gets none ("it calls itself inside this
   `match` … that isn't in tail position: its induction hypothesis can't be
   stated") [run: `g2-nontail-match.sw`, modelled on `Fmt.stands`]. The
   SW-1057 counts list 5 AoC definitions skipped for this [read:
   function-equations.md, "As built (stage 2a)"].
4. **B1: std's principles aren't made for `match induct`.** In a program,
   `match induct (List.dropWhile xs p)` says `List.dropWhile` "doesn't call
   itself, so it has no `List.dropWhile.induct`", and the same for
   `List.takeWhile`, `List.reverseOnto`, `List.all`, `Text.containsChars`
   and `Text.startsWithChars` [run: `b1-std-on-demand.sw`]. `stitchwort doc
   List.dropWhile` lists `List.dropWhile.induct` [run], and once anything in
   the file names `List.dropWhile.induct` directly, `match induct` works
   [run: `std-containsChars.sw` does this]. So the on-demand need scan sees
   the name `f.induct` but not the call inside `match induct`. A bug, with a
   one-file repro; filed below.
5. **Smaller frictions.** A `match induct` alternative can't be an
   or-pattern, so four arms with one proof are written four times (D3694 now
   allows it in an ordinary `match`); the call can't be written with a dot
   (`garden.fill …`); a target already refined by an outer split is refused
   [read: function-equations.md, "As built (stage 2b)", Limits].

## 2. Prior art

**Lean 4** [run unless marked].

- Every recursive definition, structural or well-founded, gets
  `f.induct`; `f.fun_cases` is the non-recursive split [run:
  `lean-induct.lean`; `fun_cases` per the installed `Init/Tactics.lean`,
  read by SW-4222]. The tactic `fun_induction f x y` applies it and "will try
  to automatically unfold the call" in each goal [read: SW-4222, citing
  `Init/Tactics.lean:1092`]; cases are named `case1`, `case2`, … [run].
- **The motive is over the arguments only**:
  `withoutR.induct : ∀ ok (motive : List Nat → List Nat → Prop), … → ∀
  behind a, motive behind a`. The goal's call is unfolded by the tactic, not
  by the principle. Stitchwort's motive also takes the result, so its cases
  need no unfolding at all [read: syntax.md].
- **Conditions as hypotheses**: an `if` in an arm gives `ok a b = true` and
  `¬ok a b = true`; `if h : n ≥ 2` gives `x ≥ 2` [run: `log2.induct`].
- **Overlapping patterns**: the later arm takes `(∀ b after_1, after = b
  :: after_1 → False)` and, for numbers, `(n = 2 → False)` [run:
  `withoutR.induct`, `g.induct`]. One case per arm; Lean has no pattern
  guards, so the guarded-overlap shape of G1 can't be written, and a Lean
  user writes the `if` inside the two-element arm instead.
- **A call in a non-tail `match`**: the induction hypothesis is quantified
  over the `match`'s variables and *drops* the branch fact: `(∀ still,
  motive still rest) → motive owed (1 :: rest)` [run: `stands.induct`]. That
  holds because recursion is structural in `rest` whatever `still` is.
- **Mutual recursion**: one motive per function, `ev.induct` proves the
  first, `ev.mutual_induct` the conjunction [run].
- **Nested recursion** through `List.attach`: `(∀ t, t ∈ ts → motive t) →
  motive (node ts)` [run: `T.size.induct`].
- Known limits [recalled]: the principle is derived from the compiled
  definition, so a function whose termination proof is by `decreasing_by`
  over a complex measure can give a principle with awkward hypotheses;
  `fun_induction` needs the call's varying arguments to be variables (as
  Stitchwort's `E-MATCH-MOTIVE` does).

**Rocq.** `Function f … {measure …}` generates `f_ind`/`f_rect` and the
equation `f_equation`; `functional induction (f x)` applies the principle,
with each branch's condition as a hypothesis and the call unfolded [read:
Rocq 9.1 refman, "Functional induction", via SW-4222 §3.4]. The refman
itself recommends Equations "for new code and new projects" [read: same].
Equations generates an eliminator `f_elim` from the definition's splitting
tree, applied with `funelim (f x)`; it supports with-clauses (a match on a
computed value, the G2 shape), well-founded recursion, and mutual and nested
definitions [recalled].

**Isabelle/HOL.** `fun` and `function` generate `f.induct` (and `f.pinduct`
for partial functions, over the domain predicate); `induction x y rule:
f.induct` applies it, with case names taken from the equations [recalled].
**Overlapping patterns are made disjoint before anything is proved**: `fun`
replaces a later, more general pattern by the instances the earlier ones
don't cover, so each induction case is one place in the case tree with its
constructors explicit [recalled; the `fun` tutorial, "pattern matching with
overlapping patterns"]. That is §3.1's rule for G1, applied to patterns
alone.

**Summary.** All three give the condition as a hypothesis and the call's
recursive calls as induction hypotheses, which Stitchwort already does. What
Stitchwort lacks against them: a case for a call in a non-tail `match`
(Lean, Equations), mutual groups (all three), nested recursion through a
function argument (Lean via `attach`, Equations), and the reach: Lean's and
Rocq's users get the principle from a tactic named in every tutorial.

## 3. Design

Everything below extends `crates/elab/src/equations/induct.rs` (the
principle) and `crates/elab/src/induct_match.rs` (`match induct`). The kernel
doesn't change: each principle is still a theorem whose proof is the
definition's own case tree, checked by the kernel [read: function-equations.md
§As built 2a].

### 3.1 What is generated

**Unchanged:** `f.induct` for each recursive definition, structural or
`decreasing` (fuel is structural recursion on the fuel); one case per leaf
equation, named after it (`eq2IfTrue`); the case's variables, then its
hypotheses, then one `ih` per recursive call; the motive at the arm's
patterns and the branch's right side; a fixed prefix of unchanged leading
parameters. Or-pattern arms already give one case per alternative
(`eq3Or1`, `eq3Or2`) [run: a probe of `width` with `| Nest inner | Group
inner`].

**G1: a guarded arm that a later arm partly overlaps.** Where arm K comes
after a guarded arm J whose patterns take some but not all of K's values,
K's case splits in two, at J's patterns, as the compiled definition does:

- `eqK`: J's patterns don't match. Its hypotheses are the equation's (Lean's
  form, `∀ closer after1, after = [closer, ..after1] → ¬…`), now provable by
  the existing `%apart` refutation, since the case tree separates the two
  arms there by a constructor.
- `eqKNotArmJ`: J's patterns matched and its guard failed. It binds J's
  variables (`comma closer after`), takes J's guard negated in the form the
  equations use for `notArmJ` (`c = False` for a `Bool` test, `¬(…)` for a
  conjunction), and its `ih` and motive are K's, with K's patterns written in
  J's variables (`[comma, ..behind]`, `[closer, ..after]`).

With several such J's, each place is named by the first guarded arm whose
patterns match there and carries the negated guards of every guarded arm
whose patterns match there. A guarded arm that takes all of K's values (the
guide's `countBig`) keeps its single case `eqK`, as today: nothing that has
an `f.induct` now changes. A definition whose split would make more than 32
cases is skipped with the reason (a bound in the spirit of `E-MATCH-SIZE`).

For `withoutR`: `eq1 behind`, `eq2 behind comma closer after guard ih`,
`eq3 behind leaf after notArm2 ih`, `eq3NotArm2 behind comma closer after
notGuard ih`.

**G2: a recursive call inside a non-tail `match` (or local definition).**
The call's `ih` is quantified over the variables the `match` alternative
binds, with the alternative's equation as a premise:
`ih: (still: Nat) → step owed x = Some still → motive still rest (stands
still rest)`. This is stronger for the user than Lean's (it keeps the
branch fact; a proof that doesn't need it ignores it). It is provable where
the call's decrease doesn't depend on the alternative: always for
structural recursion; for `decreasing`, when the decrease proof the
definition gives is closed under the alternative's binders. Otherwise the
definition is skipped with that reason. A call under `&&`/`||` already gets
its `ih` (SW-1057); this extends the same lifting to the `match` inside it.

**Not in this design**, each with its reason: **mutual groups** (one motive
per function, as Lean's `motive_1 motive_2`; the group machinery for
equations doesn't exist yet, and the corpus has no measured demand);
**calls under a lambda** whose argument is the lambda's variable
(`List.map (c => f c) children`, which needs membership, Lean's `attach`;
std's `Parse.Each` and 7 AoC definitions skip for it); **effectful
definitions** (the walk step's job, below).

### 3.2 How a proof uses it

The syntax is the existing `match induct (f args) with | case names… =>
body` [read: syntax.md]. Three additions:

1. **Or-patterns of cases**, under D3694's rule (the body checked once per
   alternative, every alternative binding the same names):
   `| eq3 _ _ _ _ ih | eq3NotArm2 _ _ _ _ _ ih => ih …`. Each alternative
   still names all of its case's binders positionally, `_` for the unused.
2. **The call by dot**: `match induct (leaves.withoutR behind)` reads as
   `withoutR leaves behind`, as an ordinary call does.
3. **A hole lists the cases.** `match induct (f args) with ?` (no
   alternatives) is a goal report listing each case with its binders and
   refined goal, so an author or agent starts from the skeleton. The
   language server offers the same as a code action, "Prove by induction on
   `f`", writing the alternatives with the binder names from `f.induct`.

No `cases`-style automatic closing is added: `cases` already runs inside an
alternative, and SW-4222 §6.3's lemma sets are the route to closing more.

### 3.3 Errors

- `E-NO-INDUCT` keeps its reason note; G1 and G2's skips get reasons that
  say what to write instead (move the guard into an `if` inside the arm;
  bind the `match`'s result with `let` before the call).
- `E-NONEXHAUSTIVE` on `match induct` already lists the missing cases
  [run]; it adds each missing case's binders, so a fix is a copy.
- A theorem that recurses on itself, splits with `match h: c with` on a
  condition `c` that is a branch condition of a recursive `f` in its
  statement, and has an `f.induct`: **no new warning** (too heuristic to be
  right often enough). The proving guide carries the advice instead.

### 3.4 Where it lives, hashes, caching

- **Elaborator only.** `induct.rs` (G1's split reuses SW-2868's nested
  splitting, which already places an alternative at each place of the tree
  and proves overlap facts there; G2 extends the lifting of calls under
  binders), `induct_match.rs` (or-patterns, dot calls, the skeleton hole),
  the need scan for B1, and `crates/lsp` for the code action.
- **Hashes.** Definitions that have an `f.induct` today keep the same term:
  G1 and G2 only add principles to definitions that are skipped now. The
  hash snapshots gain lines and change none; that is the lanes' bar, as it
  was SW-1057's and SW-2868's [read: function-equations.md].
- **Caching and cost.** Made with the equations, eagerly for a program,
  on demand for std; the check cache keys on the definition as today.
  SW-1057 measured +0.22% instructions over the AoC project for all
  principles [read]; G1 and G2 add a few dozen principles across the
  formatter.
- **Docs.** proving-guide.md §2 gets "Induction along a function" with the
  `countAbove` example and the rule "a proof about `f` whose recursion
  follows `f`'s starts with `match induct`"; syntax.md and the guide's
  chapter 10 get G1's case names, G2's `ih`, or-patterns of cases.

### 3.5 The walk step and SW-4047

The walk step (proof-walk-step.md) is for effectful code and does no
induction; `f.induct` is for pure recursive definitions. The SW-4238 review
§3.12 says they share "a definition's case tree with guards as hypotheses".
That piece **already exists**: `induct.rs`'s leaves are exactly the places of
the case tree with each guard, `if` condition and lifted-`match` equation as
a hypothesis. G1's per-place split is the same rule the walk needs when it
steps through a guarded arm (§3.4's "code after a split" in the review). So:
whichever lane lands first factors the leaf enumeration out of `induct.rs`
into a function the other calls; neither waits for the other.

SW-4047 (a proof `match` doesn't refine its guard) stays a separate fix for
ad hoc proof matches. With G1 the commonest reason to want it, proving
something about a guarded function, goes away.

## 4. Before and after

### 4.1 The SW-4222 sample: `allTokensWithout` (tools/fmt)

Before: 29 lines [read: `tools/fmt/src/Syntax/SettleOnceProofs.sw:424`],
with a hand split `match pair: fwdPair behind leaf after with`, an inner
`match after with`, and `rewrite withoutRNop …`/`rewrite withoutRPair …`.

After, with G1 and or-patterns of cases [sketch]:

```
theorem allTokensWithout ∀ (q: Token → Bool)
    (blind: ∀ (token: Token) (start: Bool) => q { token | lineStart = start } = q token) (behind rest: List Leaf)
    (kept: (tokens behind).all q = True)
    (coming: (tokens rest).all q = True):
    (tokens (withoutR behind rest)).all q = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 _ comma closer _ _ ih =>
      let (tok, sndToks) := commaDeletedToken comma closer behind
      let moved: q (commaDeleted comma closer behind).fst.token = True :=
        rewrite tok, blind closer.token (comma.token.lineStart || closer.token.lineStart) then
          Bool.andLeft (Bool.andRight coming)
      ih (rewrite sndToks then Bool.andIntro moved kept) (Bool.andRight (Bool.andRight coming))
    | eq3 _ _ _ _ ih | eq3NotArm2 _ _ _ _ _ ih => ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)
```

14 lines, against Lean's 15 and Rocq's 12. One uncertainty: `withoutR`'s
arm 2 binds `let (moved, earlier) := commaDeleted …`; if that elaborates as
a split on the pair, the case is `eq2Pair` or similar with `commaDeleted … =
(moved, earlier)` as a hypothesis and the proof rewrites with it once.
The same proof against the `if`-style definition, with a simplified leaf
type, checks today: four one-line alternatives [run: `withoutR-if.sw`].

### 4.2 tools/fmt: `laidWithout`

Before: 26 lines [read: `SettleOnceProofs.sw:228`], with the same hand split,
the inner `match after`, `match behind with | [previous, ..tail]`, and both
step lemmas. After [sketch]:

```
  match induct (withoutR behind rest) with
    | eq1 _ => back
    | eq2 _ comma closer after2 guard ih =>
      match behind with
        | [previous, ..tail] =>
          let (b, f) := laidMoved comma closer previous tail after2 back fwd
          ih b f
    | eq3 _ leaf _ _ ih | eq3NotArm2 _ leaf _ _ _ ih =>
      let (b, f) := laidNop leaf behind _ back fwd ?nop
      ih b f
```

About 11 lines plus the header. The open point is `?nop`: `laidNop` takes
`fwdPair behind leaf after = False`, which each case has in a different form
(`notArm2` in Lean's form, `notGuard` directly). Either `laidNop` is
restated to take the guard's negation and the `[leaf]` case's fact
separately, or the two alternatives are written apart (two more lines). This
is the honest cost of G1's two cases: helper lemmas stated against the old
`fwdPair` summary need restating once.

### 4.3 std: `Text.allNotLineBreak`

Before: 13 lines [read: `crates/elab/src/std/Text/Text.sw:978`]: `match
chars`, then `match same: Text.sameChar '\n' first with`, then a nested
`match isBreak:`. After, **checked** (with B1 worked around by naming
`Text.containsChars.induct` once in the file) [run: `std-containsChars.sw`]:

```
theorem allNotLineBreak ∀ (chars: List Char) (none: Text.containsChars ['\n'] chars = False):
    chars.all (char => char != '\n') = True :=
  match induct (Text.containsChars ['\n'] chars) with
    | eq1 => byComputing
    | eq2IfTrue char rest starts => cases
    | eq2IfFalse char rest starts ih => Bool.andIntro cases (ih none)
```

The hypothesis `none` is generalised and refined in each case, so `ih none`
is the induction step and `cases` closes both the contradiction and the
first character's fact.

## 5. Cost and risks

### 5.1 Lanes

Past actuals for this code: SW-2868 (nested splitting in `induct.rs`) Opus,
32 min against 120 estimated; SW-1073 (catch-alls) Sonnet, 22 min against
90; SW-4236 (binding or-patterns) Opus, about 25 min [read: board].

| Lane | Model | What | Estimate (agent time) |
|---|---|---|---|
| A | Sonnet or DeepSeek | B1: `match induct (f …)` asks for `f.induct` like a name does; the repro as a test. Proving guide §2 entry | 20 min |
| B | Opus | G1: per-place cases for a partly overlapped guarded arm; `withoutR`-family examples; syntax.md, guide ch. 10 | 45 min |
| C | Opus | G2: `ih` for a call in a non-tail `match`, with the alternative's equation as premise | 45 min |
| D | Sonnet | `match induct` or-patterns of cases, dot calls, the skeleton hole and the LSP code action | 40 min |
| E | Sonnet | Formatter pilot: rewrite `allTokensWithout`, `laidWithout`, `plainWithout` and the `withBareR`/`withMarkedR` siblings with `match induct`; delete step lemmas left unused | 40 min |

A first (it unblocks std proofs today and teaches the tool), B and D in
parallel after it, E after B and D, C whenever; about 3 hours of agent time
in all, 1 to 1.5 hours of wall time with parallel lanes [estimated].

### 5.2 Risks

- **Case names are user-visible and a little long** (`eq3NotArm2`). They
  follow the existing `notArmJ` naming of the equations' hypotheses, so they
  read like the rest; renumbering arms renames them, as today.
- **Case counts.** G1 multiplies cases where several guarded arms overlap
  one arm. Bounded at 32, skipped above with a reason.
- **Helper lemmas stated against summaries** (`fwdPair`) need restating
  for the two G1 cases (§4.2). A cost per proof family, paid once.
- **G2 and `decreasing`.** The `ih`'s proof uses the definition's decrease
  proof under the alternative's binders; where that proof uses the
  alternative's equation, the case can't be stated generally and the
  definition is skipped. The skip reason says so.
- **Motive inference.** `match induct` needs the varying arguments as
  distinct variables; a theorem stated about `withoutR [] leaves` has to be
  generalised first. That is today's `E-MATCH-MOTIVE`, and the guide entry
  should show the generalised lemma pattern.
- **No narrowing.** Nothing here makes a proved tool accept less or changes
  a statement; the pilot (lane E) replaces proofs of unchanged statements.

### 5.3 Findings to file

- **B1** (bug, small): `match induct (f …)` on a std function says "`f`
  doesn't call itself" unless `f.induct` is named elsewhere in the file;
  repro `docs/proposals/functional-induction/b1-std-on-demand.sw`.
- **SW-4222 §6.2's premise is wrong**: it proposes building `f.induct`,
  which exists. The review should get a one-line correction pointing here.
- **The proving guide doesn't mention `match induct`** (lane A).

## 6. The decision for Matt

**D?? (numbered by the orchestrator): re-scope SW-4229 from "build
functional induction" to "fix and teach the one we have", as lanes A to E,
with a guarded, partly overlapped arm giving two cases (`eq3`,
`eq3NotArm2`)? [rec: yes]**

- **The problem.** SW-4222 ranked "induction along a function" second, not
  knowing Stitchwort already has it (`match induct`, since 2 November). No
  proof in the formatter or std uses it; about 150 proofs re-do a function's
  split by hand instead, and the formatter keeps about 50 one-equation step
  lemmas. It isn't taught in the proving guide, it is refused for the
  formatter's commonest shape (a guarded arm that a later arm partly
  overlaps), and a bug hides it for std's own functions.
- **The change.** Fix the bug and add a proving-guide entry first; then give
  the guarded shape its cases. The user-visible choice is how: two cases
  for the overlapped arm, one where the guarded arm's patterns matched and
  its guard failed (`eq3NotArm2`, with the guard's negation stated
  directly), one where they didn't (`eq3`), as Isabelle splits overlapping
  patterns. The alternative, Lean's, keeps one case `eq3` whose hypothesis
  is "for every way the earlier arm's patterns could match, its guard
  fails", which proofs must then instantiate by hand. Then calls inside an
  inner `match`, or-patterns of cases, an editor skeleton, and a formatter
  pilot.
- **What it should do.** The sample proof goes from 29 lines to about 14
  (Lean 15, Rocq 12) [sketch]; a std proof from 13 to 8 [run]; 6 step lemmas
  and the hand splits in their 25 uses can go in the formatter's rule-N
  family [measured]. About 3 hours of agent time over five small lanes. No
  kernel change, no statement changes, no existing principle changes.

## Sources

- Stitchwort: docs/syntax.md ("Generated equations", "Functional induction,
  `f.induct`", "`match induct`", "Pattern guards"); docs/proposals/function-equations.md
  ("As built" stages 2a, 2b, nested splitting); docs/proving-guide.md;
  docs/guide/10-proofs.md; docs/reviews/SW-4222-lean-rocq-comparison.md and
  its samples; docs/proposals/proof-walk-step.md;
  docs/reviews/SW-4238-walk-step-review.md §3.12; board tickets SW-1057,
  SW-1058, SW-1073, SW-2868, SW-4047, SW-4236.
- Lean 4.35.0 (`nixpkgs#lean4`), run on `functional-induction/lean-induct.lean`:
  `#check` of `withoutR.induct`, `withoutR.fun_cases`, `g.induct`,
  `ev.induct`, `ev.mutual_induct`, `log2.induct`, `T.size.induct`,
  `stands.induct`, `sumMap.induct`; `fun_induction … with | case1 … |
  case4` closed by `grind`.
- Rocq 9.1 reference manual, "Functional induction"
  (rocq-prover.org/doc/V9.1.0/refman/using/libraries/funind.html), as read
  for SW-4222. Equations (`funelim`, `f_elim`) and Isabelle's `fun` /
  `function` (`f.induct`, `f.pinduct`, sequential disambiguation of
  overlapping patterns): recalled, not re-read for this note.
