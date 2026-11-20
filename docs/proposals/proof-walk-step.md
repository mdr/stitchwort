# Proposal: a walk step for proofs about effectful code (`walk [lemmas]`)

**Status:** draft 1, 19 November 2026. Ticket SW-4231 (Opus, paper), from
[SW-4222 §6.1](../reviews/SW-4222-lean-rocq-comparison.md#61-a-walk-step-first).
A design note only: nothing in the compiler changes. One decision for Matt
in [§6](#6-the-decision-for-matt). Written against `main` at `79a3787fc`.
Related: SW-4220 (`followsThen`'s function arguments; part (a) here does it),
SW-4047 (guards a proof `match` doesn't refine; part (b) meets the same
case), SW-4229 (generated functional induction), SW-3631 (rule sets for
`rewrite repeatedly`), [parse-proof-library.md](parse-proof-library.md) §2.2
and §4 (the `gives` tactic left for later; `readsThen` inference as built by
SW-3561), [function-equations.md](function-equations.md) (why effectful
definitions have no equations).

> **Reviewed (SW-4238, Fable, 19 November 2026):**
> [docs/reviews/SW-4238-walk-step-review.md](../reviews/SW-4238-walk-step-review.md).
> The review recommends building it with changes, and they are not yet
> folded into the text below. In short: (1) on single-file copies, the
> elaborator already infers `p` and `j` and already steps through an
> inline `match`, so §1's "why the arguments are spelled out", its probe
> and the NOTES.md quote need correcting, a baseline lane comes first,
> and parts (a) and (b) become one lane; (2) §3.4 unfolds a callee only
> when the brackets say `unfold f`; (3) §3.2 allows one `@[walk]` lemma
> per function and family, and local hypotheses serve calls of
> parameters; (4) §3.2's cache gap is in std's lazy loading, not in
> project imports; (5) §3.4 needs a rule for code after a split; (6)
> Expand walk gets a command-line form in the first lane; (7) the two-run
> walk is in the pilot's bars. §5's lanes, bars and D3695 are superseded
> by the review's §4 to §6.

Claims are marked **[measured]** (counted or run for this note), **[read]**
(in the file or page named), **[sketch]** (proof text written for this note
and not checked), or **[estimated]**.

## In plain words

**The problem.** About a third of the formatter's parser proofs are walks:
one lemma per parser function, written as a chain of "then" steps that
follows the function's body by hand. 920 walk lemmas take 13,828 lines; 531
of them spell out the pieces of the program the step is about (`[p := …]
[j := …]`), 1,583 times **[measured]**. And because a proof can't step into
a `match` inside a function, the parser is cut into small functions that
exist only so the proofs can name them: 536 of its 788 functions are called
from one place **[measured]**.

**The change.** A proof step, `walk [lemmas]`, that reads the function's
body itself: at each call it uses the lemma registered for that function,
at each `if` or `match` it splits the same way the program does, and at
each value it leaves the fact that needs thought, which `then t` or the
usual closers prove. It writes the same chain of std lemmas a lane writes
today, so the kernel checks it unchanged.

**What it should do.** On the three walks in [§4](#4-before-and-after) the
proof text goes from 46, 26 and 55 lines to about 10, 10 and 27 **[sketch]**;
SW-4222 measured Lean's equivalent at about a third of the lines.
New parser code can keep its `match`es inline instead of being cut up. No
statement changes and no theorem gets weaker.

## Contents

1. [The problem in numbers](#1-the-problem-in-numbers)
2. [Prior art](#2-prior-art)
3. [Design](#3-design)
4. [Before and after](#4-before-and-after)
5. [Cost, risks and how to measure success](#5-cost-risks-and-how-to-measure-success)
6. [The decision for Matt](#6-the-decision-for-matt)
7. [Sources](#7-sources)

## 1. The problem in numbers

Counted over `tools/fmt/src/Syntax/*.sw` at `79a3787fc` with a script
(regular expressions over theorem blocks: a block runs from `theorem` to
the next top-level line; heuristic, so read the figures as good to a few
per cent) **[measured]**:

| What | Count | Lines |
|---|---|---|
| Theorems in `Syntax/` | 3,118 | 42,964 |
| Theorems whose conclusion is a parser relation (`Parse.Gives`, `ReadsIn`, `ReadsAt`, `Reads0`, `Follows`, `FollowsAt`, `Kept`, …) | 1,387 | 19,279 |
| of which contain a `match` | 775 | |
| Walk lemmas: the proof uses a sequencing step (`Parse.givesThen`, `readsThen`, `readsAtThen`, `followsThen`, `followsMap`, `givesAfter0`, `reads0Then`, the files' own `…Then` lemmas) | 920 | 13,828 (median 12 a lemma) |
| Walk lemmas that spell out a function argument (`[p :=`, `[q :=`, `[j :=`, `[k :=`) | 531 | |
| Those spellings | 1,583, on 1,472 lines | |
| Sequencing steps in the walks | 1,853 | |

The 1,387 agree with SW-4195's "walk lemmas 23%" of slice 1's 6,031
theorems **[read]**. By file, `ParseWalk.sw` has 368 walks (4,557 lines,
778 spelled arguments), `FollowsDecl.sw` 91 (1,980), `FollowsForms.sw` 112
(1,921), `ParseCarriesLadder.sw` 55 (858, 152 spelled).

**The parser is cut for the proofs.** `Parser.sw`, `DeclParser.sw` and
`Statements.sw` have 788 definitions; 536 are called from exactly one place
in those files, and 148 of those carry a continuation's name (`…On`,
`…After`, `…Rest`, `…End`, `…Close`, …) **[measured]**. The formatter's
notes give the reason: "a `match` written inside a rule is a function the
proofs can't name" **[read: `tools/fmt/NOTES.md:1213`]**. The comma list is
four functions (`commaListFrom`, `commaListOn`, `commaListComma`,
`commaListAfter`, `Parser.sw:1825-1848`) where the program is one loop.

**Why the arguments are spelled out although `readsThen` infers them.**
SW-3561 built inference for `readsThen`: the first lemma fixes `p`, and `j`
is read off the goal **[read: parse-proof-library.md §4, "As built"]**.
It fails in three common places, which is where the 1,583 spellings are:

1. **The goal is computed past the call.** Once a proof `match` has run
   the parser's own `match` or `if`, the step's value is substituted and
   the next step run, so there is no `j (p())` left to read
   ("`[j := …]` stays there", ibid.).
2. **The first step is in another family.** `givesAfter0` (`ParseWalk.sw:345`)
   takes a `Reads0` lemma for a look-ahead and is a plain theorem, not one
   the held-argument rule knows; the comma list's first step is written
   `givesAfter0 [p := () => modes.peek] [j := seen => commaListOn …]`.
3. **The goal's parser is one unfolding away.** The goal names
   `commaListFrom`; the bind is in its body, `commaListOn … modes.peek`.

A probe shows the second half of the trouble **[measured: a 17-line file,
checked with the release binary]**: after `Parse.givesThen` over a
`peek` whose continuation is a `match fuel, seen with …`, the remaining
goal is shown as `∀ (start: Parse.Mark Nat) => Parse.Fits … → Parse.ReadsAt
start (arg => (match fuel, seen with …)) …`, the `Gives` unfolded, and
`Parse.givesDone` in a proof `match` on `fuel, seen` fails with "`_holds` is
`Parse.givesDone`'s implicit `holds`, not worked out". The hand-written walks
avoid this by cutting the parser so that each arm is a named function with
its own lemma.

**The two-run walks** (`Follows*.sw`, 290 walks) spell fewer arguments
(`followsThenEq` and `followsMap` help) but pass long explicit argument lists
to each callee's lemma: `followsTupleSecond` gives `followsCommaListFrom`
fourteen arguments, all of which are in the two calls it is about
(`FollowsBase.sw:569-585`) **[read]**.

## 2. Prior art

| System | The step | Lemmas for calls | Splits | What's left | Source |
|---|---|---|---|---|---|
| Lean 4 `Std.Do` | `mvcgen [specs, defs]` breaks a triple `⦃P⦄ prog ⦃Q⦄` into verification conditions | `@[spec]` on `foo_spec : Triple (foo a b c) P Q`: "`mvcgen` will use `foo_spec` as a specification for calls to `foo`"; a definition named in the brackets is unfolded | `if`, `dite`, `cond` and `match`; tries to reduce the matcher, then "last resort: split match" | VCs where "the original program `prog` no longer occurs", tried by `mvcgen_trivial`; `invariants` for loops; `with` alternatives per case | [read] `Std/Tactic/Do/Syntax.lean:76-84`, `Init/Tactics.lean:2336-2360`, `Lean/Elab/Tactic/Do/VCGen.lean:95-200` (Lean 4.35.0 source in the Nix store) |
| Hoare / Dijkstra | weakest preconditions, computed backwards through sequencing, with a rule per construct | a procedure's contract stands for its body (modular rule) | the conditional rule | one implication per path | [known] Dijkstra 1975, "Guarded commands, nondeterminacy and formal derivation of programs" |
| Rocq + Iris | `wp_bind pat` focuses a subterm; `wp_apply lem` "apply[ies] a lemma whose conclusion is a WP, automatically applying `wp_bind` as needed"; `wp_pures` does pure steps, but "will not reduce lambdas/recs that are hidden behind a definition" | lemmas passed by name to `wp_apply` | `wp_pures` reduces `if`/`match` on known values; case analysis by hand otherwise | the proof mode's goals | [read] Iris `heap_lang` ProofMode docs, as indexed (current page not reachable, 429); Charguéraud's CFML in *Separation Logic Foundations*: "`xapp` will be able to automatically invoke the lemma `triple_incr`" once registered in a hint database; `xif` does the case analysis on a test |
| F\* | computes the weakest precondition of any effect by "putting the code into an explicit monadic form and then translating the binds, returns, actions, and lifts" to predicate transformers | a function's computation type (its WP) | built into the WP of `if`/`match` | one validity problem for the SMT solver, "a combination of SMT solving and user-provided lemmas" | [read] F\* tutorial and OPLSS 2021 lecture 2 (fstar-lang.org), as summarised by search |
| Dafny | the verifier is "powered by Boogie and Z3"; methods carry "pre- and postconditions, frame specifications … and termination metrics" | a call is checked against the callee's contract | Boogie's VC | SMT | [read] Dafny reference manual §1; the call rule [known] |

**What carries over.** All five reason about a call by the callee's
specification, never by unfolding it unless asked (Lean's brackets, Iris's
"hidden behind a definition"). All split on the program's own conditions.
The interactive ones (Lean, Iris, CFML) leave named goals for the user;
the auto-active ones (F\*, Dafny) send everything to a solver, which
Stitchwort doesn't have and the hammer experiment (SW-3586: 0 net gain over
`arithmetic` and `cases`) **[read: board]** argues against needing.

**What to avoid,** from SW-4222 §4 **[read]**: Lean's tool is mid-rename and
its leftover hypotheses have machine names (`h✝`, reached with
`rename_i`); Rocq's unifier walked *into* a callee instead of using its
lemma. Both shape the rules below: names come from the program, and a call
with a lemma is never unfolded.

## 3. Design

### 3.1 What a walk is about: families

A **family** is a relation over a thunk of effectful code, `R … (() =>
body) post`, with four std lemmas that say how it sequences. Today's
families, all in std or the formatter **[read]**:

| Family | then | done | weaken | Where |
|---|---|---|---|---|
| `Parse.ReadsIn inv p spec` | `Parse.readsThen` | `Parse.readsDone` | `Parse.readsWeaken` | `std/Parse/Reads.sw` |
| `Parse.ReadsAt start p spec` | `Parse.readsAtThen` | `Parse.readsAtDone` | `Parse.readsAtWeaken` | same |
| `Parse.Gives inv p holds` | `Parse.givesThen` | `Parse.givesDone` | `Parse.givesWeaken` | `std/Parse/Gives.sw` |
| `Reads0 p` (reads nothing) | `reads0Then` | `reads0Done` | — | `Syntax/ParseProofs.sw` |
| `Parse.Follows same alike p q` (two runs) | `Parse.followsThen` | `Parse.followsDone` | `Parse.followsWeaken` | `std/Parse/Follows.sw` |

A family is declared by attributes on those lemmas, so that the walk is not
Parse-specific and a new family (a `State` invariant, `Kept`) needs no
compiler change:

```
@[walk.then] theorem Parse.givesThen …
@[walk.done] theorem Parse.givesDone …
@[walk.weaken] theorem Parse.givesWeaken …
```

The compiler checks each when it is declared: a `walk.then` lemma's
conclusion is the family's relation at `() => j (p())` with `p` and `j`
implicit, its first explicit premise the relation at `p`, and its second a
`∀` over the value (and, for `ReadsIn`, the read list) ending in the
relation at `() => j v`. A two-run family's then-lemma has two thunks
(`p`, `q`, `j`, `k`). A lemma of the wrong shape is `E-ATTRIBUTE`, with what
was expected. A **bridge** (`@[walk.then]` on `givesAfter0`, whose first
premise is in `Reads0`) lets a lemma of one family serve a call in another.

### 3.2 Which lemma a call uses: `@[walk]` and the brackets

A lemma about one function in one family is registered with `@[walk]`:

```
@[walk]
theorem givesBump: Parse.Gives GoodItems (() => bump()) (word => True) := …
```

It is filed under its family and the head of its thunk (`bump`). At a call,
the walk uses, in this order:

1. a term in the brackets whose type is the family's relation at that call:
   a local hypothesis (`nextGives`, `nested`), a lemma applied to some of
   its arguments (`endsGives count`), or a lemma by name;
2. the theorem being proved, for a recursive call of its own head
   (structural or `decreasing` recursion, checked as now);
3. a `@[walk]` lemma in scope (the module's imports), for that head and
   family.

If two in the same tier fit, it is an error naming both, with "name one in
the brackets": the choice never depends on the order lemmas were found.
A lemma's explicit arguments that are the call's arguments are found by
first-order unification of its thunk with the call as written, never by
unfolding the call. Its other premises (`seconds: ExprsAlike second
secondTwin`, `valueHolds`) are filled, in order, from the facts the walk has
introduced, the hypotheses in scope and the bracket terms; what can't be
filled is a goal left (§3.5).

**Why an attribute and not a naming convention.** The repo's names are
not uniform (`givesBump`, `readsAtBumpFirst`, `followsBump`, `reads0Peek`),
and a convention fails silently; `@[reading]` is the precedent for a
theorem the compiler files and uses (`crates/elab/src/reading.rs`)
**[read]**. Unlike readings, a walk lemma need not live in its head's
module: walk lemmas are in `ParseWalk.sw`, the functions in `Parser.sw`.
That is safe because a proof only sees what its file imports, and the term
the walk writes names every lemma it used, so the check cache records the
dependency. One gap to settle in the build lane: a lemma *added* to an
imported module can change a later choice (tier 3) without the proof
mentioning it; the cached proof stays a correct proof, but the key should
include the walk lemmas in scope for the heads the walk met (the
`check-cache.md` rule for units used, applied to the registry).

### 3.3 Syntax

Proofs are terms, so the walk is a term, written as `rewrite repeatedly
[rules]` is (docs/syntax.md, "rewrite repeatedly"; `then` as D3648 chose):

```
walk [t1, t2, …]                 -- walk the goal's body; close what's left with the closers
walk [t1, t2, …] then t          -- and try `t` in each goal the closers don't close
walk [t1, t2, …, unfold f, unfold g]   -- also unfold f and g where they're called
```

- `walk` is a word only when `[` follows at the start of a term, like
  `repeatedly` after `rewrite`: 426 uses of `walk` as a name in `.sw` code
  (`Expr.walk`, `Fmt/Walk.sw`) stay names, and no program writes `walk [`
  today **[measured]**. The brackets are required, `walk []` included.
- The goal must be a family's relation whose thunk's body is a call of a
  definition, or the step reports the goal and the families it knows.
- The leftover goals are what a lane needs to see, so the language server
  shows them at `walk` like any open goal, and offers **Expand walk** (as
  `rewrite repeatedly`'s expand action, SW-3642): it replaces the step with
  the explicit chain it built (`Parse.givesThen … (seen seenFacts => match
  …)`), which is also the escape hatch when a leftover needs a proof the
  closers can't find and `then t` can't express.

### 3.4 What it does, step by step

It unfolds the goal's head once (delta and beta, as `byComputing` would one
step) and follows the elaborated body. Code in a row of abilities is
elaborated in computation mode, "effectful arguments are run first, left to
right, with `bind`" **[read: `crates/elab/src/effects.rs:27-30`]**, so the
evaluation order is already explicit in the term: the walk reads it, it
doesn't infer it.

- **Bind** (`bind (call) (v => rest)`, from `let v := f x` or from
  `g (f x)`): this is **part (a)**. `p` is `() => call` and `j` is `v =>
  rest`, read off the term, so nothing is unified higher-order and the
  1,583 spellings go. The call gets its lemma (§3.2), the family's
  then-lemma is applied, and the walk goes on in `rest` with the value and
  its fact in scope.
- **A call with no lemma**: if it is in the brackets as `unfold f`, or it is
  not recursive and has no `@[walk]` lemma in this family, it is unfolded a
  step and walked through (the split-out continuations, `commaListOn`,
  `tupleFuel`, need no lemma of their own); a recursive call that is neither
  the theorem's own head nor has a lemma stops the walk (§3.5).
- **A pure `let`** is substituted (zeta); a pure argument stays as written.
- **`if c then a else b`, and `match` on any scrutinees**: this is **part
  (b)**. The walk writes a proof `match` on the same scrutinees with the
  definition's own case tree (`match h: c with | True => … | False => …`
  for an `if`; for `| Succ more, Some kind => … | _, _ => …`, the compiled
  splits: `Zero`, `Succ more` with `None`, `Succ more` with `Some kind`, as
  the hand proof of §4.1 does). In each case it states the expected type
  itself, folded: `Parse.Gives inv (() => armBody) post`, with the arm's
  body taken from the definition. The kernel accepts that by conversion,
  since the program's `match` computes once the scrutinee is a constructor.
  This is what the probe in §1 lacked: the goal is never left in its
  unfolded `ReadsAt` form, so `givesDone` and the then-lemmas apply in every
  arm. Guards (`| x if g =>`) split on the guard after the pattern, with
  `g = True` and `g = False` in scope: the SW-4047 workaround, done
  mechanically. A scrutinee that is a computed value (`kind == Comma`) is
  abstracted by the term the walk holds, not by searching the goal.
- **A value** at the end of a path: the family's done-lemma, leaving
  `post value` with the path's facts and conditions in scope.
- **A lemma whose post differs** from what the rest needs: the family's
  weaken-lemma, leaving the implication.
- **A two-run family** walks both bodies in lockstep: a bind in each, the
  pair of calls given one two-run lemma; an `if` in each splits on both
  conditions with the agreement as a goal (`Parse.followsIf`'s `agree`), and
  a `match` on scrutinees the `between` facts make equal splits once.
  Bodies whose shapes differ stop with both shown. As built (SW-4240), the
  equal values are rewritten to the first run's and the split is made once
  after; `followsIf`'s agreement goal is not built.

**Names.** A value is named after the program's binder (`let seen :=
modes.peek` gives `seen`), or, when the call is an argument, after the
function (`full`, `commaListFrom`); its fact is that name with `Facts`, and
for `ReadsIn` its items read with `Read` (`seenRead`). A case's hypotheses
take the pattern's names (`more`, `kind`) and the condition's equation is
`<name>Is` for an `if` on a binder, `branch1`, `branch2` otherwise. A name
that clashes with one in scope gets a numeral (`comma1`). The goals show
these names, so `then t` and an expanded walk can use them, and they don't
change when an unrelated step is added, unlike Lean's `h✝`.

**Closers.** Each leftover goal is tried, cheapest first, with what `cases`
tries at a node (computation, a contradiction among the facts, a hypothesis
or a part of one: `crates/elab/src/cases.rs` module docs **[read]**), then
building a conjunction from parts, then `arithmetic` on the facts in scope,
then `t` from `then t`. A step cap (the `cases` cap, 20M steps, SW-3846,
as a start) bounds the whole walk.

### 3.5 When it stops

The walk never fails silently into a harder goal (the failure SW-4222 met
with its ten-line Rocq walk). It stops with an error, `E-WALK`, at the
`walk` token, that names the place in the program and shows the goal:

```
[E-WALK] Error: the walk has no lemma for this call
   ╭─[ ParseWalk.sw:980:3 ]
   │   walk [reads0Peek modes, givesBump, nextGives] then …
   │   ──┬─
   │     ╰── at `ends count` (Parser.sw:1843:39, in `commaListComma`, arm `Succ more, Some kind`, `kind == Comma` True)
   │
   │ Note 1: `ends` is a parameter; give its lemma in the brackets, e.g. `endsGives count`
   │ Note 2: the goal there is Parse.Gives GoodItems (() => ends count) ?first
```

The other stops are: a recursive call with no lemma; a construct it doesn't
walk (`handle`, a row change by `translate`, `match reify`, code in an
effect-polymorphic row `{e}`: §3.6); two lemmas in a tier; and leftover
goals the closers and `then t` don't close, listed each with its path (arm,
branch, call) and its facts. `walk?` is not proposed: the expand action
gives the same.

### 3.6 Where it lives, and what it doesn't touch

- **The elaborator**, beside `cases.rs` and `rewrite.rs`: a new
  `walk.rs`, the attribute specs in `attributes.rs`, the syntax in the
  parser's proof terms. It writes ordinary applications of the family's
  std lemmas, proof `match`es and conversions; **no kernel change**, and
  `docs/core.md` is untouched. Because it generates kernel terms, its
  build gets an Opus review (D2364).
- **Abilities.** The walk is generic in the row: what it needs is the
  then-lemma of a family, whose `bind` is in the row's `Comp`. Stage 1
  handles code in one closed row (every formatter parser is `{Parse
  Item}`). A call moved into the row with `translate` along a `SigMap`, a
  `handle` in the body, and effect-polymorphic code (`bindIn`, `bindDv`)
  stop with `E-WALK` until a family needs them.
- **Recursion through `Parse.recursiveWith` and fuel** is by lemmas, as now
  (`Parse.givesRecursiveWith` registered); the walk does no induction of its
  own, and a theorem's recursion is checked for termination as now.
- **The language server**: goals at `walk`, Expand walk, hover on `walk`
  listing the lemmas used per call (the trace), go-to-definition on a used
  lemma through the trace.
- **Check time.** Every step is a first-order unification of a lemma's
  thunk with a call as written, or a split the program already makes; no
  search. Stage 1's bar is `rewrite repeatedly`'s: within 1.5× the
  hand-written proof's check time on the pilot (SW-3602 met it only after
  two follow-ups, which §5 budgets).

### 3.7 Alternatives considered

- **Better inference only (SW-4220 as filed).** Helpers so `followsThen`'s
  arguments needn't be given. It removes the spellings where the goal still
  shows `j (p())`, which §1 says is not where most of them are, and does
  nothing for the cut-up parser. Part (a) is the same goal done from the
  body instead of the goal; SW-4220 can close into this.
- **Generated equations for effectful definitions** (so `rewrite
  commaListOn.eq1` works). function-equations.md skips them because their
  arms are computations "whose type has no spelling in a statement"
  **[read]**; the walk never states one, only the family's relation, so it
  doesn't need them.
- **A tactic language users program.** SW-4222 §6 "not worth taking"; the
  built step can report where it stopped, a user's script can't.
- **A solver** (F\*, Dafny). No SMT in Stitchwort, and SW-3586's hammer
  found no net gain on the leftovers.

## 4. Before and after

The "after" texts are **[sketch]**: written for this note against the
design above, not checked. Line counts include the statement.

### 4.1 `givesCommaListFrom` (`ParseWalk.sw:973-1018`): 46 lines to about 10

Before (the proof, two argument lines joined; the statement is unchanged):

```
  givesAfter0
    [p := () => modes.peek]
    [j := seen => commaListOn fuel modes ends next count current found seen]
    (reads0Peek modes)
    (seen =>
      match fuel, seen with
        | Succ more, Some kind =>
          match isComma: kind == Comma with
            | True =>
              Parse.givesThen
                [p := () => bump()]
                [j := comma => commaListAfter more modes ends next count [current, ..found] (ends count)]
                givesBump
                (comma _ =>
                  Parse.givesThen
                    [p := () => ends count]
                    [j := stop => commaListAfter more modes ends next count [current, ..found] stop]
                    (endsGives count)
                    (stop _ =>
                      match stop with
                        | True => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
                        | False =>
                          Parse.givesThen
                            [p := () => next()]
                            [j := value => commaListFrom more modes ends next (count + 1) value [current, ..found]]
                            nextGives
                            (value valueHolds =>
                              Parse.givesWeaken
                                (givesCommaListFrom modes ends next holds endsGives nextGives more
                                  (count + 1) value [current, ..found] valueHolds (currentHolds, foundHolds))
                                (pair facts => (facts.left, arithmetic [facts.right])))))
            | False => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
        | Succ more, None => Parse.givesDone (commaEnd holds current found currentHolds foundHolds)
        | Zero, seen => Parse.givesDone (commaEnd holds current found currentHolds foundHolds))
```

After, with parts (a) and (b):

```
  walk [reads0Peek modes, givesBump, endsGives count, nextGives]
    then commaEnd holds current found currentHolds foundHolds
```

What the walk does: unfolds `commaListFrom` to `commaListOn … modes.peek`
(no lemma; bridged from `Reads0` by `givesAfter0`), unfolds `commaListOn`
(no lemma, not itself recursive) and splits its `match fuel, seen` and its
`if kind == Comma`; unfolds `commaListComma` and `commaListAfter`; uses
`givesBump`, `endsGives count`, `nextGives`; at `commaListFrom more …` uses
the theorem itself, filling `valueHolds` from `nextFacts` and `List.All
holds [current, ..found]` as the conjunction of `currentHolds` and
`foundHolds`; weakens, and closes the length implication by `arithmetic`.
The four `commaEnd` leaves are closed by `then`. With (b), the four parser
functions could be one again; the proof text doesn't change.

### 4.2 `followsTupleSecond` (`FollowsBase.sw:560-585`): 26 lines to about 10

Before (proof):

```
  Parse.followsThen
    (followsCommaListFrom inner
      (tupleEnds inner)
      (tupleEnds inner)
      (count => followsTupleEnds inner count)
      (() => full self inner)
      (() => full selfTwin inner)
      (followsFull knot inner)
      fuel
      2
      second
      secondTwin
      seconds
      [first]
      [firstTwin]
      (Both firsts Trivial))
    (pair pairTwin pairs => followsTupleEnd inner open openTwin opens pair pairTwin pairs)
```

After, with the two-run walk:

```
  walk [followsCommaListFrom, followsTupleEnds inner, followsFull knot inner, followsTupleEnd]
```

Every argument of `followsCommaListFrom` but its three premises is in the
two calls; the premises are bracket terms or in scope (`seconds`, and
`Both firsts Trivial` as a conjunction of `firsts` with `True`). The tail
call `tupleEnd inner open pair` gets `followsTupleEnd` with `pairs` from the
then-step's fact. (`followsCommaListFrom` and `followsTupleEnd` would be
`@[walk]` and could leave the brackets.)

### 4.3 `readsTupleRest` (`ParseKept.sw:730-784`): 55 lines to about 27

This one has real content at its leaf: the items read regroup into the
shape `keptTuple` takes. The walk removes the plumbing (the marks `after`,
`after2` … `after5`, the `Fits` threading, two spelled arguments, the
`readsAtAfter0`/`readsAtBumpRead` bridges) and leaves the leaf. Before is
the 43-line proof at `ParseKept.sw:742-784`. After **[sketch]**:

```
  walk [nested, readsCommaListFrom inner (tupleEnds inner) (() => full self inner) (readsTupleEnds inner)
      (nested { modes = inner, level = LevelFull }), readsTupleClose inner]
    then
      let (more, split, others) := commaListFromFacts
      let tail: RestKept [comma, ..fullRead ++ commaListFromRead] [full, ..more] trailing :=
        restKeptStep comma isComma fullFacts others
      let all: ItemsKept (inside ++ [comma, ..fullRead ++ commaListFromRead]) items trailing :=
        rewrite split then itemsKeptCons kept tail
      let whole := keptTuple open (inside ++ [comma, ..fullRead ++ commaListFromRead]) tupleCloseRead
        items trailing tupleClose isOpen all tupleCloseFacts
      rewrite List.appendNil tupleCloseRead then
        rewrite List.appendAssoc inside [comma, ..fullRead ++ commaListFromRead] tupleCloseRead,
            List.appendAssoc fullRead commaListFromRead tupleCloseRead at whole then
          whole
```

The `ReadsAt` family's then-lemma carries the mark and `Fits`, so the
`bump` at a known `start.rest = [comma, ..later]` needs the family's
bump-with-shape lemma registered (`readsAtBumpRead` today). The names come
from §3.4: `full`, `commaListFrom` (calls as arguments), `items, trailing`
(the definition's pattern in `tupleEnd`), `tupleClose`.

## 5. Cost, risks and how to measure success

### 5.1 Lanes

Estimates in agent time, from the actuals of the nearest past lanes
**[read: board, "Model result" lines]**: SW-3561 (`readsThen` inference in
the elaborator, Opus) 70 min; SW-3602 (`rewrite repeatedly` stage 1, a new
proof step with rule lists, Opus) 97 min, then SW-3629, SW-3654 and SW-3659
on its check time, 35 + 29 + 37 min; SW-3642 (stage 2, named sets) 50 min;
SW-3752 (`cases` splitting equalities, Opus) 76 min; SW-3662 (language-server
follow-ups, Sonnet) 17 to 25 min.

| Lane | What | Model | Estimate |
|---|---|---|---|
| W1 | Part (a): `walk [..] then t` for one-run families; `@[walk]`, `@[walk.then/done/weaken]`; binds, calls (three tiers), unfolding lemma-less non-recursive callees, values, weaken, closers, names, `E-WALK`; std's `Gives`, `ReadsIn`, `ReadsAt` tagged; guide and syntax.md sections; examples (accept, reject per stop) | Opus | 100 min |
| W2 | Part (b): inner `if` and `match` along the compiled case tree, guards, folded expected types per arm | Opus | 75 min |
| W3 | Review of W1+W2 (generates kernel terms, D2364) | Opus paper | 20 min |
| W4 | Pilot: convert the comma lists and brackets of `ParseWalk.sw` (about 40 walks) and their `Follows`/`Kept` twins where W5 allows; tag their lemmas; measure (§5.3) | Sonnet | 50 min |
| W5 | Two-run families in lockstep (`Follows`) | Opus | 60 min |
| W6 | Language server: goals, hover trace, Expand walk | Sonnet | 30 min |
| W7 | Check time, if the pilot misses the bar (as SW-3629/3654/3659) | Opus | 30 to 60 min |

About **6 to 7 agent hours** in all, against SW-4222's 8 to 15 h
**[read]** (that was before the step was laid out). W1 and W2 can run one
after the other in one lane if the orchestrator prefers; W5 and W6 can run
beside W4. Converting the rest of slice 1's 920 walks is a separate,
mechanical rollout (Sonnet or DeepSeek by file, keeping a conversion only
where it shortens the proof, as SW-3631 does), and not in these figures.

### 5.2 Risks

- **Lean's tool has been changing for a year** (SW-4222 §4). The design is
  smaller than `mvcgen`: no predicate transformers, no invariants, no
  solver; it writes the chain a lane writes now. If W2 proves hard, W1 is
  useful alone (the 1,583 spellings and the first-step bridge).
- **Conversion cost in the kernel.** Each arm's folded type is checked by
  conversion against the computed `match`; on large case trees
  (`bracketedAfter`'s nested `if`s) this could be slow. The pilot measures
  it; the fallback is the existing per-arm functions, which the walk still
  handles.
- **Brittleness of automatic unfolding.** A lemma added for a helper
  changes what the walk does at its calls. The proof still checks if the
  lemma is right; the one-lemma-per-tier rule keeps it deterministic, and
  the cache-key point of §3.2 must be settled in W1.
- **Leftover goals the closers can't see.** The leaf facts of `ParseKept`
  stay hand-written; the walk doesn't make them shorter, only reachable.
  That is the expected end state (SW-4222 §4: "no system makes the walk
  lemmas disappear").
- **The word `walk`** is a common name in the formatter. As a contextual
  word (only before `[` at a term's start) nothing changes for programs;
  a reader may still be surprised by `walk [` meaning a proof step.

### 5.3 How to measure success

On the W4 pilot, against the same theorems before (`git show` of the base):

1. **Proof lines** of the converted walks: target at most half (SW-4222's
   Lean figure is a third); **spelled arguments**: zero.
2. **Check time** of the converted file within 1.5× the hand-written one
   (the bar `rewrite repeatedly` used).
3. **Errors that point**: a set of reject examples (a missing lemma, a
   false leaf, an ambiguous pair, an unsupported construct) each naming the
   call or branch and showing the goal, checked by snapshot.
4. **The parser can be uncut**: the four `commaList…` functions merged into
   one with inline `match` and `if`, with the walk's proof unchanged and
   `Fmt.Tests` passing.
5. After the rollout, the §1 script again: walk lines and the share of
   single-call parser functions.

## 6. The decision for Matt

**D3695: build the walk step as designed here, a new proof term `walk
[lemmas] then t` with `@[walk]` lemmas, parts (a) and (b) and the two-run
walk, about 6 to 7 agent hours, piloted on the comma lists and brackets
before any rollout? [rec: yes]** (The number is the next after D3694 at
the time of writing; the orchestrator renumbers it if taken.)

- **The problem.** A parser function's lemma is a hand-written chain that
  follows the function's body step by step, with the program's pieces
  spelled out 1,583 times in 920 lemmas (13,828 lines), and the parser is
  cut into one function per step so that proofs can name each piece (536
  of its 788 functions are called from one place) **[measured]**.
- **The change.** A proof step that reads the function's body itself,
  uses each called function's registered lemma, and splits each `if` and
  `match` the way the program does, leaving only the facts that need
  thought. It writes the same std lemmas the lanes write now, so the
  kernel checks it unchanged; programs are untouched (`walk` is a word only
  before `[` in a proof).
- **What it should do.** On three real walks, 46, 26 and 55 lines become
  about 10, 10 and 27 **[sketch]**; on SW-4222's sample, Lean's equivalent
  was a third of the lines **[read]**. The parser's split functions can be
  merged back. No statement changes and no theorem gets weaker. Slice 2's
  parser walks (about 2,100 to 2,500 theorems on the present form, SW-4210
  **[read: SW-4222 §7]**) would be written with it from the start.

The rest is the orchestrator's: lane order, models, the attribute names
under `walk.`, the closer order and the step cap.

## 7. Sources

- Stitchwort at `79a3787fc`: `tools/fmt/src/Syntax/{ParseWalk,ParseKept,FollowsBase,Parser,ParseProofs}.sw`,
  `crates/elab/src/std/Parse/{Gives,Follows,Reads}.sw`,
  `crates/elab/src/{effects,cases,reading,attributes,induct_match}.rs`,
  `docs/syntax.md` ("Attributes", "Proofs about effectful code", "rewrite
  repeatedly", "arithmetic", "cases"), `tools/fmt/NOTES.md:1213`,
  `docs/proposals/parse-proof-library.md` §2.2 and §4,
  `docs/proposals/function-equations.md` ("Not generated"),
  `docs/reviews/SW-4222-lean-rocq-comparison.md` §§2 to 7,
  `docs/reviews/SW-4205-slice1-retrospective.md`, board tickets' "Model
  result" lines.
- The counts in §1: a Python script over `tools/fmt/src/Syntax/*.sw` and
  the three parser files, run for this note (in the lane's scratch, not
  committed); the regular expressions are as §1 describes.
- The probe in §1: a 17-line file with a `peek` followed by an inner
  `match`, checked with `target/release/stitchwort check`.
- Lean 4.35.0 source (nixpkgs `lean4`, in the Nix store):
  `src/lean/Std/Tactic/Do/Syntax.lean` lines 76 to 84 (`spec`) and 435 to
  440 (`mvcgen` syntax, deprecated for `vcgen`);
  `src/lean/Init/Tactics.lean` from line 2336 (`mvcgen`'s docstring);
  `src/lean/Lean/Elab/Tactic/Do/VCGen.lean` lines 95 to 200 (the step:
  lets, splits, unfolding, specs, "last resort: split match").
- Iris HeapLang proof mode documentation (`docs/heap_lang.md` in the Iris
  repository; quoted from indexed copies, as gitlab.mpi-sws.org returned
  429): `wp_bind`, `wp_apply`, `wp_pures`.
- *Separation Logic Foundations* (Software Foundations vol. 6),
  chapter `Basic`, softwarefoundations.cis.upenn.edu/slf-current/Basic.html:
  `xwp`, `xapp` with registered specifications, `xif`.
- F\*: fstar-lang.org tutorial ("Primitive Effect Refinements"), OPLSS 2021
  lecture 2, and the F\* overview paper (microsoft.com, fstar.pdf), as
  returned by search.
- Dafny Reference Manual §1, dafny.org/latest/DafnyRef/DafnyRef.
- [known], not re-read: E. W. Dijkstra, "Guarded commands, nondeterminacy
  and formal derivation of programs", CACM 18(8), 1975; Dafny's modular
  call rule.
